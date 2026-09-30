-- Prove2me | solution 1 for WeierstrassEllipticZeta.specialize_moving_elliptic_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T17:41:01.978728+00:00
-- url     : https://prove2.me/submissions/b8dde104-f60d-4239-986a-9ea37bccdadf

import Definitions.Def_WeierstrassEllipticZeta_GeneratorPolynomials
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.MvPolynomial.Degrees

noncomputable section

open MvPolynomial

namespace TranscendenceTheory

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

private lemma polyLength_pow {τ : Type} (p : MvPolynomial τ ℤ) (n : ℕ) :
    polyLength (p ^ n) ≤ polyLength p ^ n := by
  induction n with
  | zero => simp [polyLength_one]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (polyLength_mul _ _).trans (Nat.mul_le_mul_right _ ih)

private lemma polyLength_prod {τ ι : Type} (s : Finset ι)
    (f : ι → MvPolynomial τ ℤ) :
    polyLength (∏ i ∈ s, f i) ≤ ∏ i ∈ s, polyLength (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polyLength_one]
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (polyLength_mul _ _).trans (Nat.mul_le_mul_left _ ih)

/-- Clear separate coordinate denominators with degree and coefficient-length bounds. -/
theorem polynomial_clear_denominators_bound {σ τ A : Type} [Fintype σ] [CommRing A]
    (p : MvPolynomial σ ℤ) (k d H : σ → ℕ)
    (s q : σ → MvPolynomial τ ℤ)
    (hp : ∀ i, p.degreeOf i ≤ k i)
    (hs_degree : ∀ i, (s i).totalDegree ≤ d i)
    (hq_degree : ∀ i, (q i).totalDegree ≤ d i)
    (hs_length : ∀ i, (∑ m ∈ (s i).support, ((s i).coeff m).natAbs) ≤ H i)
    (hq_length : ∀ i, (∑ m ∈ (q i).support, ((q i).coeff m).natAbs) ≤ H i) :
    ∃ r : MvPolynomial τ ℤ,
      r.totalDegree ≤ ∑ i, k i * d i ∧
      (∑ m ∈ r.support, (r.coeff m).natAbs) ≤
        (∑ m ∈ p.support, (p.coeff m).natAbs) * ∏ i, H i ^ k i ∧
      ∀ (φ : MvPolynomial τ ℤ →+* A) (y : σ → A),
        (∀ i, φ (s i) = φ (q i) * y i) →
        φ r = (∏ i, φ (q i) ^ k i) * eval₂ (Int.castRingHom A) y p := by
  classical
  let term (m : σ →₀ ℕ) : MvPolynomial τ ℤ :=
    C (p.coeff m) * ∏ i, q i ^ (k i - m i) * s i ^ m i
  let r : MvPolynomial τ ℤ := ∑ m ∈ p.support, term m
  have hm (m : σ →₀ ℕ) (hmem : m ∈ p.support) (i : σ) : m i ≤ k i :=
    (monomial_le_degreeOf i hmem).trans (hp i)
  have hterm_degree (m : σ →₀ ℕ) (hmem : m ∈ p.support) :
      (term m).totalDegree ≤ ∑ i, k i * d i := by
    apply (totalDegree_mul _ _).trans
    simp only [totalDegree_C, zero_add]
    apply (totalDegree_finsetProd _ _).trans
    apply Finset.sum_le_sum
    intro i _
    calc
      _ ≤ (k i - m i) * (q i).totalDegree + m i * (s i).totalDegree :=
        (totalDegree_mul _ _).trans (Nat.add_le_add (totalDegree_pow _ _) (totalDegree_pow _ _))
      _ ≤ (k i - m i) * d i + m i * d i :=
        Nat.add_le_add (Nat.mul_le_mul_left _ (hq_degree i))
          (Nat.mul_le_mul_left _ (hs_degree i))
      _ = k i * d i := by rw [← Nat.add_mul, Nat.sub_add_cancel (hm m hmem i)]
  have hterm_length (m : σ →₀ ℕ) (hmem : m ∈ p.support) :
      polyLength (term m) ≤ (p.coeff m).natAbs * ∏ i, H i ^ k i := by
    apply (polyLength_mul _ _).trans
    rw [polyLength_C]
    apply Nat.mul_le_mul_left
    apply (polyLength_prod _ _).trans
    apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    intro i _
    calc
      _ ≤ polyLength (q i) ^ (k i - m i) * polyLength (s i) ^ m i :=
        (polyLength_mul _ _).trans (Nat.mul_le_mul (polyLength_pow _ _) (polyLength_pow _ _))
      _ ≤ H i ^ (k i - m i) * H i ^ m i :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (hq_length i) _) (Nat.pow_le_pow_left (hs_length i) _)
      _ = H i ^ k i := by rw [← pow_add, Nat.sub_add_cancel (hm m hmem i)]
  refine ⟨r, totalDegree_finsetSum_le hterm_degree, ?_, ?_⟩
  · change polyLength r ≤ polyLength p * _
    apply (polyLength_sum_le _ _).trans
    calc
      _ ≤ ∑ m ∈ p.support, (p.coeff m).natAbs * ∏ i, H i ^ k i :=
        Finset.sum_le_sum hterm_length
      _ = _ := by rw [← Finset.sum_mul]; rfl
  · intro φ y hy
    change φ (∑ m ∈ p.support, term m) = _
    rw [map_sum, eval₂_eq']
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hmem
    have hfactor (i : σ) :
        φ (q i) ^ (k i - m i) * φ (s i) ^ m i = φ (q i) ^ k i * y i ^ m i := by
      rw [hy i, mul_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (hm m hmem i)]
    simp only [term, map_mul, map_prod, map_pow]
    simp_rw [hfactor]
    rw [Finset.prod_mul_distrib]
    have hc : φ (C (p.coeff m)) = (Int.castRingHom A) (p.coeff m) := by
      simp
    rw [hc]
    ring

end TranscendenceTheory

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

private lemma period_index_bound (N : ℕ) (hN : (2 : ℝ) ≤ N) :
    (1 + 3 * auxiliaryS3 N : ℝ) ≤ (N : ℝ) ^ 4 := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hlog : Real.log N ≤ N := (Real.log_le_sub_one_of_pos hN0).trans (by linarith)
  have hp : (N : ℝ) ^ (5 / 8 : ℝ) ≤ N := by
    simpa using Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (5 / 8 : ℝ) ≤ 1)
  have hq := Nat.floor_le (by positivity :
    0 ≤ (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N / 64)
  have hprod := mul_le_mul hp hlog hlog0 (by positivity : (0 : ℝ) ≤ N)
  change (auxiliaryS3 N : ℝ) ≤ _ at hq
  have hq2 : (auxiliaryS3 N : ℝ) ≤ (N : ℝ) ^ 2 := by
    nlinarith only [hq, hprod, sq_nonneg (N : ℝ)]
  have hsq : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith only [hN]
  nlinarith only [hq2, hsq, sq_nonneg ((N : ℝ) ^ 2 - 4)]


/-- Specialize generator polynomials and clear the fixed denominator, with uniform bounds. -/
theorem solution
    (L : PeriodPair) (ω u₁ u₂ θ ν : ℂ)
    (d : ℤ[X]) (hd : Polynomial.aeval θ d ≠ 0)
    (h_generators : ∀ j : Fin 9, ∃ p : ℤ[X][X],
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = Polynomial.aeval θ d *
        ellipticArithmeticGenerators L ω u₁ u₂ j)
    (h_polynomials : EllipticGeneratorPolynomialData L ω u₁ u₂) :
    AuxiliaryMovingCoordinateData L ω u₁ u₂ θ ν := by
  classical
  choose p hp using h_generators
  let s : Fin 9 → MvPolynomial (Fin 2) ℤ := fun j => flatten (p j)
  let q : MvPolynomial (Fin 2) ℤ := flatten (Polynomial.C d)
  let D := q.totalDegree + Finset.univ.sup fun j => (s j).totalDegree
  let h := 1 + (∑ m ∈ q.support, (q.coeff m).natAbs) +
    Finset.univ.sup fun j => ∑ m ∈ (s j).support, ((s j).coeff m).natAbs
  have hsD (j : Fin 9) : (s j).totalDegree ≤ D := by
    have := Finset.le_sup (f := fun j => (s j).totalDegree) (Finset.mem_univ j)
    dsimp [D]; omega
  have hqD : q.totalDegree ≤ D := by dsimp [D]; omega
  have hsh (j : Fin 9) : (∑ m ∈ (s j).support, ((s j).coeff m).natAbs) ≤ h := by
    have := Finset.le_sup (f := fun j => ∑ m ∈ (s j).support,
      ((s j).coeff m).natAbs) (Finset.mem_univ j)
    dsimp [h]; omega
  have hqh : (∑ m ∈ q.support, (q.coeff m).natAbs) ≤ h := by dsimp [h]; omega
  have hqeval : eval₂ (Int.castRingHom ℂ) ![θ, ν] q = Polynomial.aeval θ d := by
    simpa [q] using flatten_eval (Polynomial.C d) θ ν
  have hseval (j : Fin 9) : eval₂ (Int.castRingHom ℂ) ![θ, ν] (s j) =
      eval₂ (Int.castRingHom ℂ) ![θ, ν] q * ellipticArithmeticGenerators L ω u₁ u₂ j := by
    rw [hqeval]
    exact (flatten_eval (p j) θ ν).trans (hp j)
  obtain ⟨C, H, _, _, hP⟩ := h_polynomials
  let M := H * h ^ (9 * C)
  let B := 9 * D * C * 19 + 19 * M + 4
  have hDB : 9 * D * C * 19 ≤ B := by dsimp [B]; omega
  have hMB : (19 * M : ℝ) ≤ B := by exact_mod_cast (show 19 * M ≤ B by dsimp [B]; omega)
  have h4B : (4 : ℝ) ≤ B := by exact_mod_cast (show 4 ≤ B by dsimp [B]; omega)
  refine ⟨B, ?_⟩
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop 2]
    with N hN v hv hvl
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hv
  let T := (a 0).val ^ 2 + (a 1).val ^ 2 + 1
  let K := C * T
  let J := (1 + (a 2).val) * H ^ T
  let b := (1 + (a 2).val) * M ^ T
  obtain ⟨P⟩ := hP (fun j => (a j).val) hvl
  have hT : T ≤ 19 * auxiliaryS N ^ 2 := by
    have ha : (a 0).val ≤ 3 * auxiliaryS N := Nat.le_of_lt (a 0).isLt
    have hb : (a 1).val ≤ 3 * auxiliaryS N := Nat.le_of_lt (a 1).isLt
    have hs : 1 ≤ auxiliaryS N := (Nat.one_le_floor_iff _).mpr
      (Real.one_le_rpow (by linarith : (1 : ℝ) ≤ N) (by norm_num))
    have ha2 := Nat.pow_le_pow_left ha 2
    have hb2 := Nat.pow_le_pow_left hb 2
    dsimp [T]
    nlinarith
  have hdegree : 9 * D * K ≤ B * auxiliaryS N ^ 2 := by
    calc
      _ = (9 * D * C) * T := by dsimp [K]; ring
      _ ≤ (9 * D * C) * (19 * auxiliaryS N ^ 2) := Nat.mul_le_mul_left _ hT
      _ = (9 * D * C * 19) * auxiliaryS N ^ 2 := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ hDB
  have hlength : J * h ^ (9 * K) = b := by
    simp only [J, K, b, M, mul_pow, ← pow_mul, mul_assoc]
  have hb : (b : ℝ) ≤ Real.exp (B * ((auxiliaryS N : ℝ) ^ 2 + Real.log N)) := by
    have hN0 : (0 : ℝ) < N := by linarith
    have hlog : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
    have hc : ((a 2).val : ℝ) ≤ 3 * auxiliaryS3 N := by
      exact_mod_cast (Nat.le_of_lt (a 2).isLt)
    have hperiod : (1 + (a 2).val : ℝ) ≤ Real.exp (4 * Real.log N) := by
      calc
        _ ≤ (1 + 3 * auxiliaryS3 N : ℝ) := by linarith
        _ ≤ (N : ℝ) ^ 4 := period_index_bound N hN
        _ = _ := by
          rw [← Real.rpow_natCast, Real.rpow_def_of_pos hN0]
          norm_num [mul_comm]
    have hMexp : (M : ℝ) ≤ Real.exp M := by linarith [Real.add_one_le_exp (M : ℝ)]
    have hTR : (T : ℝ) ≤ 19 * (auxiliaryS N : ℝ) ^ 2 := by exact_mod_cast hT
    have hpower : (M : ℝ) ^ T ≤ Real.exp ((19 * M : ℝ) * (auxiliaryS N : ℝ) ^ 2) := by
      calc
        _ ≤ (Real.exp M) ^ T := pow_le_pow_left₀ (by positivity) hMexp T
        _ = Real.exp ((M : ℝ) * T) := by rw [mul_comm, Real.exp_nat_mul]
        _ ≤ _ := Real.exp_le_exp.mpr (by
          nlinarith [mul_le_mul_of_nonneg_left hTR (by positivity : (0 : ℝ) ≤ M)])
    calc
      _ = (1 + (a 2).val : ℝ) * (M : ℝ) ^ T := by simp only [b, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow]
      _ ≤ Real.exp (4 * Real.log N) * Real.exp ((19 * M : ℝ) * (auxiliaryS N : ℝ) ^ 2) :=
        mul_le_mul hperiod hpower (by positivity) (by positivity)
      _ = Real.exp (4 * Real.log N + (19 * M : ℝ) * (auxiliaryS N : ℝ) ^ 2) :=
        (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by
        nlinarith [mul_le_mul_of_nonneg_right h4B hlog,
          mul_le_mul_of_nonneg_right hMB (sq_nonneg (auxiliaryS N : ℝ))])
  have hclear (P₀ : MvPolynomial (Fin 9) ℤ) (hPD : P₀.totalDegree ≤ K)
      (hPH : (∑ m ∈ P₀.support, (P₀.coeff m).natAbs) ≤ J) :
      ∃ r : MvPolynomial (Fin 2) ℤ,
        r.totalDegree ≤ B * auxiliaryS N ^ 2 ∧
        (∑ m ∈ r.support, (r.coeff m).natAbs) ≤ b ∧
        eval₂ (Int.castRingHom ℂ) ![θ, ν] r = Polynomial.aeval θ d ^ (9 * K) *
          eval₂ (Int.castRingHom ℂ) (ellipticArithmeticGenerators L ω u₁ u₂) P₀ := by
    obtain ⟨r, hrD, hrH, hreval⟩ := TranscendenceTheory.polynomial_clear_denominators_bound
      (A := ℂ) P₀ (fun _ => K) (fun _ => D) (fun _ => h) s (fun _ => q)
      (fun j => (degreeOf_le_totalDegree P₀ j).trans hPD)
      hsD (fun _ => hqD) hsh (fun _ => hqh)
    refine ⟨r, ?_, ?_, ?_⟩
    · apply le_trans _ hdegree
      simpa [mul_assoc, mul_left_comm, mul_comm] using hrD
    · rw [← hlength]
      apply hrH.trans
      simpa [← pow_mul, mul_comm] using Nat.mul_le_mul_right (h ^ (9 * K)) hPH
    · have he := hreval (eval₂Hom (Int.castRingHom ℂ) ![θ, ν])
        (ellipticArithmeticGenerators L ω u₁ u₂) hseval
      change eval₂ (Int.castRingHom ℂ) ![θ, ν] r =
        (∏ _ : Fin 9, eval₂ (Int.castRingHom ℂ) ![θ, ν] q ^ K) *
          eval₂ (Int.castRingHom ℂ) (ellipticArithmeticGenerators L ω u₁ u₂) P₀ at he
      simpa only [hqeval, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, ← pow_mul, Nat.mul_comm] using he
  obtain ⟨Q, hQD, hQH, hQeval⟩ := hclear P.denominator P.denominator_degree P.denominator_length
  have hnums (j : Fin 3) := hclear (P.numerator j) (P.numerator_degree j) (P.numerator_length j)
  choose R hRD hRH hReval using hnums
  refine ⟨{
    numerator := R
    denominator := fun _ => Q
    lengthBound := fun _ => b
    numerator_degree := hRD
    denominator_degree := fun _ => hQD
    numerator_length := hRH
    denominator_length := fun _ => hQH
    length_le := fun _ => hb
    denominator_ne_zero := ?_
    evaluation := ?_ }⟩
  · intro j
    rw [hQeval]
    exact mul_ne_zero (pow_ne_zero _ hd) P.denominator_ne_zero
  · intro j
    rw [hReval, P.evaluation, hQeval, mul_assoc]

