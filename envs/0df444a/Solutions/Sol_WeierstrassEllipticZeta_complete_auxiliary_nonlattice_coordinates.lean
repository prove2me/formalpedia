-- Prove2me | solution 1 for WeierstrassEllipticZeta.complete_auxiliary_nonlattice_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T17:20:25.665708+00:00
-- url     : https://prove2.me/submissions/45b8d35e-0faf-4c17-b439-1eae22f7fd33

import Definitions.Def_WeierstrassEllipticZeta_MovingCoordinates
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section

open MvPolynomial Filter
open scoped Polynomial

open WeierstrassEllipticZeta

private def flatten : ℤ[X][X] →+* MvPolynomial (Fin 2) ℤ :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom C (X 0)) (X 1)

private lemma flatten_eval (p : ℤ[X][X]) (θ ν : ℂ) :
    eval₂ (Int.castRingHom ℂ) ![θ, ν] (flatten p) =
      p.eval₂ (Polynomial.aeval θ).toRingHom ν := by
  have h : (eval₂Hom (Int.castRingHom ℂ) ![θ, ν]).comp flatten =
      Polynomial.eval₂RingHom (Polynomial.aeval θ).toRingHom ν := by
    apply Polynomial.ringHom_ext
    · intro q
      have hq : (eval₂Hom (Int.castRingHom ℂ) ![θ, ν]).comp
          (Polynomial.eval₂RingHom C (X 0)) = (Polynomial.aeval θ).toRingHom := by
        apply Polynomial.ringHom_ext <;> simp
      simpa [flatten] using congrArg (fun f : ℤ[X] →+* ℂ => f q) hq
    · simp [flatten]
  exact congrArg (fun f : ℤ[X][X] →+* ℂ => f p) h

private def polyLength {σ : Type} (p : MvPolynomial σ ℤ) : ℕ :=
  ∑ m ∈ p.support, (p.coeff m).natAbs

private lemma polyLength_eq {σ : Type} (p : MvPolynomial σ ℤ) :
    polyLength p = ∑ m ∈ p.support, (p.coeff m).natAbs := rfl

private lemma polyLength_sum_le {σ ι : Type} (s : Finset ι)
    (f : ι → MvPolynomial σ ℤ) :
    polyLength (∑ i ∈ s, f i) ≤ ∑ i ∈ s, polyLength (f i) := by
  classical
  let t := s.biUnion fun i => (f i).support
  have heq (p : MvPolynomial σ ℤ) (hp : p.support ⊆ t) :
      polyLength p = ∑ m ∈ t, (p.coeff m).natAbs := by
    rw [polyLength_eq]
    apply Finset.sum_subset hp
    intro m _ hm
    simp [notMem_support_iff.mp hm]
  rw [heq _ support_sum]
  simp_rw [coeff_sum]
  calc
    _ ≤ ∑ m ∈ t, ∑ i ∈ s, ((f i).coeff m).natAbs := by
      apply Finset.sum_le_sum
      intro m _
      exact Int.natAbs_sum_le _ _
    _ = ∑ i ∈ s, polyLength (f i) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      exact (heq _ (Finset.subset_biUnion_of_mem (fun i => (f i).support) hi)).symm

private lemma polyLength_monomial {σ : Type} (m : σ →₀ ℕ) (a : ℤ) :
    polyLength (monomial m a) = a.natAbs := by
  classical
  by_cases ha : a = 0 <;> simp [polyLength, support_monomial, ha]

private lemma polyLength_mul {σ : Type} (p q : MvPolynomial σ ℤ) :
    polyLength (p * q) ≤ polyLength p * polyLength q := by
  classical
  conv_lhs => rw [p.as_sum, q.as_sum]
  simp only [Finset.sum_mul, Finset.mul_sum, monomial_mul]
  apply (polyLength_sum_le _ _).trans
  apply (Finset.sum_le_sum fun _ _ => polyLength_sum_le _ _).trans
  simp only [polyLength_monomial, Int.natAbs_mul]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, ← polyLength_eq, le_refl]

private lemma polyLength_one {τ : Type} : polyLength (1 : MvPolynomial τ ℤ) = 1 := by
  exact polyLength_monomial (0 : τ →₀ ℕ) 1

private lemma polyLength_C {τ : Type} (a : ℤ) :
    polyLength (C a : MvPolynomial τ ℤ) = a.natAbs :=
  polyLength_monomial 0 a

private lemma polyLength_add {τ : Type} (p q : MvPolynomial τ ℤ) :
    polyLength (p + q) ≤ polyLength p + polyLength q := by
  simpa [Fin.sum_univ_succ] using
    polyLength_sum_le (Finset.univ : Finset (Fin 2)) ![p, q]

private lemma ordinary_coordinate_length_bound (H N a b c : ℕ)
    (hN : max 13 (H : ℝ) ≤ N)
    (ha : a ≤ 3 * auxiliaryS N) (hb : b ≤ 3 * auxiliaryS N)
    (hc : c ≤ 3 * auxiliaryS3 N) :
    (((2 * a + 1 + b + c) * H : ℕ) : ℝ) ≤ Real.exp (4 * Real.log N) := by
  have hN13 : (13 : ℝ) ≤ N := (le_max_left _ _).trans hN
  have hHN : (H : ℝ) ≤ N := (le_max_right _ _).trans hN
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hS : (auxiliaryS N : ℝ) ≤ N := by
    apply (Nat.floor_le (by positivity : 0 ≤ (N : ℝ) ^ (3 / 16 : ℝ))).trans
    simpa using Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (3 / 16 : ℝ) ≤ 1)
  have hq : (auxiliaryS3 N : ℝ) ≤ (N : ℝ) ^ 2 := by
    have hfloor := Nat.floor_le (by positivity :
      0 ≤ (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N / 64)
    change (auxiliaryS3 N : ℝ) ≤ _ at hfloor
    have hp : (N : ℝ) ^ (5 / 8 : ℝ) ≤ N := by
      simpa using Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (5 / 8 : ℝ) ≤ 1)
    have hl : Real.log N ≤ N := (Real.log_le_sub_one_of_pos hN0).trans (by linarith)
    have hprod := mul_le_mul hp hl hlog0 hN0.le
    nlinarith [sq_nonneg (N : ℝ)]
  have haR : (a : ℝ) ≤ 3 * auxiliaryS N := by exact_mod_cast ha
  have hbR : (b : ℝ) ≤ 3 * auxiliaryS N := by exact_mod_cast hb
  have hcR : (c : ℝ) ≤ 3 * auxiliaryS3 N := by exact_mod_cast hc
  have hsum : (2 * a + 1 + b + c : ℝ) ≤ 13 * (N : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((N : ℝ) - 1)]
  calc
    _ = (2 * a + 1 + b + c : ℝ) * H := by push_cast; rfl
    _ ≤ (13 * (N : ℝ) ^ 2) * N := mul_le_mul hsum hHN (by positivity) (by positivity)
    _ ≤ (N : ℝ) ^ 4 := by nlinarith [mul_le_mul_of_nonneg_right hN13 (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 3)]
    _ = Real.exp (4 * Real.log N) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hN0]
      norm_num [mul_comm]

/-- Complete all eight jet coordinates from the three moving ones and the seven
fixed polynomial presentations, retaining the required asymmetric profiles. -/
theorem solution
    (L : PeriodPair) (ω u₁ u₂ θ ν : ℂ)
    (d : ℤ[X]) (hd : Polynomial.aeval θ d ≠ 0)
    (h_fixed : ∀ j : Fin 7, ∃ p : ℤ[X][X],
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = Polynomial.aeval θ d *
        (![u₁ / 2, u₂, ω, weierstrassZeta L (u₁ / 2), L.weierstrassP (u₁ / 2),
          L.derivWeierstrassP (u₁ / 2), deriv L.derivWeierstrassP (u₁ / 2)] j))
    (h_moving : AuxiliaryMovingCoordinateData L ω u₁ u₂ θ ν) :
    AuxiliaryNonlatticeCoordinateData L ω u₁ u₂ θ ν := by
  classical
  choose p hp using h_fixed
  let s : Fin 7 → MvPolynomial (Fin 2) ℤ := fun j => flatten (p j)
  let q : MvPolynomial (Fin 2) ℤ := flatten (Polynomial.C d)
  let D := q.totalDegree + Finset.univ.sup fun j => (s j).totalDegree
  let H := 1 + polyLength q + Finset.univ.sup fun j => polyLength (s j)
  have hsD (j : Fin 7) : (s j).totalDegree ≤ D := by
    have := Finset.le_sup (f := fun j => (s j).totalDegree) (Finset.mem_univ j)
    dsimp [D]; omega
  have hqD : q.totalDegree ≤ D := by dsimp [D]; omega
  have hsH (j : Fin 7) : polyLength (s j) ≤ H := by
    have := Finset.le_sup (f := fun j => polyLength (s j)) (Finset.mem_univ j)
    dsimp [H]; omega
  have hqH : polyLength q ≤ H := by dsimp [H]; omega
  have hs_eval (j : Fin 7) : eval₂ (Int.castRingHom ℂ) ![θ, ν] (s j) =
      Polynomial.aeval θ d * (![u₁ / 2, u₂, ω, weierstrassZeta L (u₁ / 2),
        L.weierstrassP (u₁ / 2), L.derivWeierstrassP (u₁ / 2),
        deriv L.derivWeierstrassP (u₁ / 2)] j) :=
    (flatten_eval (p j) θ ν).trans (hp j)
  have hq_eval : eval₂ (Int.castRingHom ℂ) ![θ, ν] q = Polynomial.aeval θ d := by
    simpa [q] using flatten_eval (Polynomial.C d) θ ν
  have hq_ne : eval₂ (Int.castRingHom ℂ) ![θ, ν] q ≠ 0 := hq_eval ▸ hd
  obtain ⟨C₀, hC₀⟩ := h_moving
  let B := C₀ + D + H + 4
  have hDB : D ≤ B := by dsimp [B]; omega
  have hCB : C₀ ≤ B := by dsimp [B]; omega
  have hHB : H ≤ B := by dsimp [B]; omega
  have h4B : 4 ≤ B := by dsimp [B]; omega
  have hHexp : (H : ℝ) ≤ Real.exp B := by
    have h := Real.add_one_le_exp (B : ℝ)
    have hHB' : (H : ℝ) ≤ B := by exact_mod_cast hHB
    linarith
  refine ⟨B, ?_⟩
  filter_upwards [hC₀, (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
    (max 13 (H : ℝ))] with N hMN hN v hv hvl
  obtain ⟨P⟩ := hMN v hv hvl
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hv
  let a₀ : ℕ := (a 0).val
  let a₁ : ℕ := (a 1).val
  let a₂ : ℕ := (a 2).val
  let p₀ := MvPolynomial.C (2 * a₀ + 1 : ℤ) * s 0 +
    MvPolynomial.C (a₁ : ℤ) * s 1 + MvPolynomial.C (a₂ : ℤ) * s 2
  let h₀ := (2 * a₀ + 1 + a₁ + a₂) * H
  have hHh₀ : H ≤ h₀ := by dsimp [h₀]; nlinarith
  have htermD (j : Fin 7) (k : ℤ) : (MvPolynomial.C k * s j).totalDegree ≤ D :=
    (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using hsD j)
  have hp₀D : p₀.totalDegree ≤ D :=
    (totalDegree_add _ _).trans (max_le
      ((totalDegree_add _ _).trans (max_le (htermD 0 _) (htermD 1 _))) (htermD 2 _))
  have htermH (j : Fin 7) (k : ℕ) : polyLength (MvPolynomial.C (k : ℤ) * s j) ≤ k * H := by
    apply (polyLength_mul _ _).trans
    simpa only [polyLength_C, Int.natAbs_natCast] using Nat.mul_le_mul_left k (hsH j)
  have hp₀H : polyLength p₀ ≤ h₀ := by
    apply (polyLength_add _ _).trans
    apply (Nat.add_le_add ((polyLength_add _ _).trans
      (Nat.add_le_add (htermH 0 (2 * a₀ + 1)) (htermH 1 a₁))) (htermH 2 a₂)).trans
    dsimp [h₀]
    exact le_of_eq (by ring)
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg (by
    have := (le_max_left 13 (H : ℝ)).trans hN; linarith)
  have hh₀ : (h₀ : ℝ) ≤ Real.exp (B * Real.log N) := by
    apply (ordinary_coordinate_length_bound H N a₀ a₁ a₂ hN
      (Nat.le_of_lt (a 0).isLt) (Nat.le_of_lt (a 1).isLt) (Nat.le_of_lt (a 2).isLt)).trans
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast h4B) hlog0
  have hPD (j : Fin 3) : (P.numerator j).totalDegree ≤ B * auxiliaryS N ^ 2 :=
    (P.numerator_degree j).trans (Nat.mul_le_mul_right _ hCB)
  have hQD (j : Fin 3) : (P.denominator j).totalDegree ≤ B * auxiliaryS N ^ 2 :=
    (P.denominator_degree j).trans (Nat.mul_le_mul_right _ hCB)
  have hPH (j : Fin 3) : (P.lengthBound j : ℝ) ≤
      Real.exp (B * ((auxiliaryS N : ℝ) ^ 2 + Real.log N)) := by
    apply (P.length_le j).trans
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hCB) (by positivity)
  have hp₀eval : eval₂ (Int.castRingHom ℂ) ![θ, ν] p₀ =
      Polynomial.aeval θ d * (u₁ / 2 +
        integerGridPoint u₁ u₂ ω (fun j => (a j : ℕ))) := by
    simp only [p₀, eval₂_add, eval₂_mul, eval₂_C, hs_eval]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    dsimp [integerGridPoint, a₀, a₁, a₂]
    push_cast
    ring
  refine ⟨{
    numerator := ![p₀, P.numerator 0, P.numerator 1, P.numerator 2, s 3, s 4, s 5, s 6]
    denominator := ![q, P.denominator 0, P.denominator 1, P.denominator 2, q, q, q, q]
    lengthBound := ![h₀, P.lengthBound 0, P.lengthBound 1, P.lengthBound 2, H, H, H, H]
    numerator_degree := ?_
    denominator_degree := ?_
    numerator_length := ?_
    denominator_length := ?_
    length_le := ?_
    denominator_ne_zero := ?_
    evaluation := ?_ }⟩
  · intro j
    fin_cases j
    · exact hp₀D.trans hDB
    · exact hPD 0
    · exact hPD 1
    · exact hPD 2
    · exact (hsD 3).trans hDB
    · exact (hsD 4).trans hDB
    · exact (hsD 5).trans hDB
    · exact (hsD 6).trans hDB
  · intro j
    fin_cases j
    · exact hqD.trans hDB
    · exact hQD 0
    · exact hQD 1
    · exact hQD 2
    all_goals exact hqD.trans hDB
  · intro j
    fin_cases j
    · exact hp₀H
    · exact P.numerator_length 0
    · exact P.numerator_length 1
    · exact P.numerator_length 2
    · exact hsH 3
    · exact hsH 4
    · exact hsH 5
    · exact hsH 6
  · intro j
    fin_cases j
    · exact hqH.trans hHh₀
    · exact P.denominator_length 0
    · exact P.denominator_length 1
    · exact P.denominator_length 2
    all_goals exact hqH
  · intro j
    fin_cases j
    · exact hh₀
    · exact hPH 0
    · exact hPH 1
    · exact hPH 2
    all_goals exact hHexp
  · intro j
    fin_cases j
    · exact hq_ne
    · exact P.denominator_ne_zero 0
    · exact P.denominator_ne_zero 1
    · exact P.denominator_ne_zero 2
    all_goals exact hq_ne
  · intro j
    fin_cases j
    · simpa [ellipticJetCoordinates, hq_eval] using hp₀eval
    · exact P.evaluation 0
    · exact P.evaluation 1
    · exact P.evaluation 2
    · simpa [ellipticJetCoordinates, hq_eval] using hs_eval 3
    · simpa [ellipticJetCoordinates, hq_eval] using hs_eval 4
    · simpa [ellipticJetCoordinates, hq_eval] using hs_eval 5
    · simpa [ellipticJetCoordinates, hq_eval] using hs_eval 6

