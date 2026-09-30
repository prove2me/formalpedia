-- Prove2me | solution 1 for WeierstrassEllipticZeta.line_anchor_gcd_criterion
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-22T17:15:11.179523+00:00
-- url     : https://prove2.me/submissions/13b307e7-b0e0-4f31-a81e-e2fac6481700

import Definitions.Def_WeierstrassEllipticZeta_LineAnchorGCD
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

noncomputable section
open scoped Classical
namespace WeierstrassEllipticZeta

private def restrictionPoly (S : Fin 5 → ℂ → ℂ) (b : ℂ)
    (T U : Polynomial ℂ) (Q : MvPolynomial (Fin 7) ℂ) : Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C
    ![1, T, Polynomial.C (S 0 b), Polynomial.C (S 1 b), Polynomial.C (S 2 b),
      Polynomial.C (S 3 b) + U * Polynomial.C (S 0 b),
      Polynomial.C (S 4 b) + U * Polynomial.C (S 2 b)] Q

private lemma substitution_degree (H : Fin 7 → Polynomial ℂ) (w : Fin 7 → ℕ)
    (hH : ∀ i, (H i).natDegree ≤ w i) (Q : MvPolynomial (Fin 7) ℂ)
    (N : ℕ) (hQ : ∀ d ∈ Q.support, ∑ i : Fin 7, d i * w i ≤ N) :
    (MvPolynomial.eval₂Hom Polynomial.C H Q).natDegree ≤ N := by
  rw [Q.as_sum, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  rw [MvPolynomial.eval₂Hom_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  calc
    _ ≤ (∏ i : Fin 7, H i ^ d i).natDegree := Polynomial.natDegree_C_mul_le _ _
    _ ≤ ∑ i : Fin 7, (H i ^ d i).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ i : Fin 7, d i * w i := by
      apply Finset.sum_le_sum
      intro i _
      exact Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hH i))
    _ ≤ N := hQ d hd

private lemma restriction_degree (S : Fin 5 → ℂ → ℂ) (b : ℂ)
    (T U : Polynomial ℂ) (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) :
    (restrictionPoly S b T U Q).natDegree ≤ m * T.natDegree + n * U.natDegree := by
  refine substitution_degree _ ![0, T.natDegree, 0, 0, 0, U.natDegree, U.natDegree] ?_ Q _ ?_
  · intro i
    fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one]
    · simp
    · exact le_rfl
    · simp
    · simp
    · simp
    · exact Polynomial.natDegree_add_le_of_degree_le (by simp)
        (Polynomial.natDegree_mul_C_le _ _)
    · exact Polynomial.natDegree_add_le_of_degree_le (by simp)
        (Polynomial.natDegree_mul_C_le _ _)
  · intro d hd
    obtain ⟨hm, hn⟩ := hQ d hd
    calc
      _ = d 1 * T.natDegree + (d 5 + d 6) * U.natDegree := by
        simp [Fin.sum_univ_succ]
        ring
      _ ≤ m * T.natDegree + n * U.natDegree :=
        Nat.add_le_add (Nat.mul_le_mul_right _ (by omega))
          (Nat.mul_le_mul_right _ (by omega))

private lemma restriction_eval (S : Fin 5 → ℂ → ℂ) (b : ℂ)
    (T U : Polynomial ℂ) (Q : MvPolynomial (Fin 7) ℂ) (s : ℂ) :
    (restrictionPoly S b T U Q).eval s =
      MvPolynomial.eval ![1, T.eval s, S 0 b, S 1 b, S 2 b,
        S 3 b + U.eval s * S 0 b, S 4 b + U.eval s * S 2 b] Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [restrictionPoly]
  | add P Q hP hQ => simp_all [restrictionPoly, map_add]
  | mul_X P i hP =>
    simp only [restrictionPoly, map_mul, MvPolynomial.eval₂Hom_X] at *
    rw [Polynomial.eval_mul, hP]
    congr 1
    fin_cases i <;> simp

private def locusValue (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (w : Fin 3 → ℂ) : ℂ :=
  MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
    S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q

private lemma linear_degree (a b : ℂ) :
    (Polynomial.C a + Polynomial.C b * Polynomial.X).natDegree ≤ 1 :=
  (Polynomial.natDegree_add_le _ _).trans
    (max_le (by simp) ((Polynomial.natDegree_C_mul_le _ _).trans (by simp)))


private lemma anchor_slice_eval (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (b α t β : ℂ) :
    (anchorSlice S Q b α t).eval β = locusValue S Q ![t, b, α * t + β] := by
  change (restrictionPoly S b (Polynomial.C t)
    (Polynomial.C (α * t) + Polynomial.X) Q).eval β = _
  rw [restriction_eval]
  simp only [Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_X]
  rfl

private lemma anchor_slice_degree (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) (b α t : ℂ) :
    (anchorSlice S Q b α t).natDegree ≤ n := by
  have h := restriction_degree S b (Polynomial.C t)
    (Polynomial.C (α * t) + Polynomial.X) Q m n hQ
  have hd : (Polynomial.C (α * t) + Polynomial.X).natDegree ≤ 1 := by
    simpa using linear_degree (α * t) 1
  simp only [Polynomial.natDegree_C, mul_zero, zero_add] at h
  exact h.trans ((Nat.mul_le_mul_left n hd).trans_eq (Nat.mul_one n))

private lemma gcd_obstruction_degree (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) (b α : ℂ) :
    (anchorObstruction S Q m b α).natDegree ≤ n := by
  unfold anchorObstruction
  split_ifs with h
  · exact anchor_slice_degree S Q m n hQ b α _
  · simp


private lemma line_samples_iff (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ) (b α β : ℂ) :
    (∀ w ∈ elementaryLocusSamples (.line α) ![0, b, β] m n, locusValue S Q w = 0) ↔
      ∀ j ∈ Finset.range (m + n + 1), (anchorSlice S Q b α j).eval β = 0 := by
  constructor
  · intro hz j hj
    have hv := hz (![0, b, β] + ![(j:ℂ), 0, α * j]) (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
    simpa [anchor_slice_eval, locusValue, add_comm] using hv
  · intro hz w hw
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
    simpa [anchor_slice_eval, locusValue, add_comm] using hz j hj

private lemma obstruction_sample (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ) (b α : ℂ)
    (hp : anchorObstruction S Q m b α ≠ 0) :
    ∃ j ∈ Finset.range (m + n + 1),
      anchorObstruction S Q m b α = anchorSlice S Q b α j ∧
      anchorSlice S Q b α j ≠ 0 := by
  have hex : ∃ j : ℕ, j ≤ m ∧ anchorSlice S Q b α j ≠ 0 := by
    by_contra hz
    exact hp (by simp [anchorObstruction, hz])
  refine ⟨Nat.find hex, Finset.mem_range.mpr ?_, ?_, (Nat.find_spec hex).2⟩
  · have hj := (Nat.find_spec hex).1
    omega
  · simp only [anchorObstruction, dif_pos hex]

private lemma anchor_gcd_ne_zero (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ) (b α : ℂ)
    (hp : anchorObstruction S Q m b α ≠ 0) : lineAnchorGCD S Q m n b α ≠ 0 := by
  rw [lineAnchorGCD, if_neg hp]
  obtain ⟨j, hj, _, hne⟩ := obstruction_sample S Q m n b α hp
  intro hz
  exact hne (Finset.gcd_eq_zero_iff.mp hz j hj)

private lemma anchor_gcd_dvd_obstruction (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ) (b α : ℂ)
    (hp : anchorObstruction S Q m b α ≠ 0) :
    lineAnchorGCD S Q m n b α ∣ anchorObstruction S Q m b α := by
  rw [lineAnchorGCD, if_neg hp]
  obtain ⟨j, hj, heq, _⟩ := obstruction_sample S Q m n b α hp
  rw [heq]
  exact Finset.gcd_dvd hj

private lemma anchor_gcd_degree (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) (b α : ℂ) :
    (lineAnchorGCD S Q m n b α).natDegree ≤ n := by
  by_cases hp : anchorObstruction S Q m b α = 0
  · simp [lineAnchorGCD, hp]
  · exact (Polynomial.natDegree_le_of_dvd
      (anchor_gcd_dvd_obstruction S Q m n b α hp) hp).trans
        (gcd_obstruction_degree S Q m n hQ b α)

private lemma anchor_roots_eq_gcd_roots (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ) (b α : ℂ) :
    lineAnchorRoots S Q m n b α = (lineAnchorGCD S Q m n b α).roots.toFinset := by
  by_cases hp : anchorObstruction S Q m b α = 0
  · simp [lineAnchorRoots, lineAnchorGCD, hp]
  have hg := anchor_gcd_ne_zero S Q m n b α hp
  ext β
  unfold lineAnchorRoots
  rw [Finset.mem_filter]
  change (β ∈ (anchorObstruction S Q m b α).roots.toFinset ∧
      ∀ w ∈ elementaryLocusSamples (.line α) ![0, b, β] m n, locusValue S Q w = 0) ↔ _
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hp, line_samples_iff,
    Multiset.mem_toFinset, Polynomial.mem_roots hg]
  constructor
  · rintro ⟨_, hz⟩
    apply Polynomial.dvd_iff_isRoot.mp
    rw [lineAnchorGCD, if_neg hp]
    apply Finset.dvd_gcd
    intro j hj
    exact Polynomial.dvd_iff_isRoot.mpr (hz j hj)
  · intro hroot
    have hd := Polynomial.dvd_iff_isRoot.mpr hroot
    constructor
    · exact Polynomial.dvd_iff_isRoot.mp
        (hd.trans (anchor_gcd_dvd_obstruction S Q m n b α hp))
    · intro j hj
      apply Polynomial.dvd_iff_isRoot.mp
      apply hd.trans
      rw [lineAnchorGCD, if_neg hp]
      exact Finset.gcd_dvd hj

private lemma anchor_roots_nonempty_iff (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ) (b α : ℂ) :
    (lineAnchorRoots S Q m n b α).Nonempty ↔
      0 < (lineAnchorGCD S Q m n b α).natDegree := by
  rw [anchor_roots_eq_gcd_roots]
  constructor
  · rintro ⟨β, hβ⟩
    have hc : 0 < (lineAnchorGCD S Q m n b α).roots.card :=
      Multiset.card_pos.mpr (by
        intro hz
        have hm := Multiset.mem_toFinset.mp hβ
        simpa only [hz, Multiset.notMem_zero] using hm)
    exact hc.trans_le (Polynomial.card_roots' _)
  · intro hd
    have hp : lineAnchorGCD S Q m n b α ≠ 0 := by
      intro hz
      simpa [hz] using hd
    obtain ⟨β, hβ⟩ := Complex.exists_root (Polynomial.natDegree_pos_iff_degree_pos.mp hd)
    exact ⟨β, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr hβ)⟩


end WeierstrassEllipticZeta
open WeierstrassEllipticZeta

theorem solution
    (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) :
    (∀ b α : ℂ,
      lineAnchorRoots S Q m n b α = (lineAnchorGCD S Q m n b α).roots.toFinset ∧
      (lineAnchorGCD S Q m n b α).natDegree ≤ n ∧
      ((lineAnchorRoots S Q m n b α).Nonempty ↔
        0 < (lineAnchorGCD S Q m n b α).natDegree)) ∧
    ∀ (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ) (X : Finset ℂ)
      (K : Set ℂ) (Z : Finset ℂ) (P : FiniteLocusCandidate Λ X → Prop),
      (∃ a : FibreEnumeratedAnchorCandidate Λ η X S Q m n K Z,
        P (fibreEnumeratedAnchorLocus Λ η X S Q m n K Z a)) ↔
      (∃ a : GCDAnchorCandidate Λ η X S Q m n K Z,
        P (gcdAnchorLocus Λ η X S Q m n K Z a)) := by
  classical
  refine ⟨fun b α => ⟨anchor_roots_eq_gcd_roots S Q m n b α,
    anchor_gcd_degree S Q m n hQ b α, anchor_roots_nonempty_iff S Q m n b α⟩, ?_⟩
  intro Λ η X K Z P
  constructor
  · rintro ⟨a, ha⟩
    rcases a with a | a
    · exact ⟨.inl (), ha⟩
    rcases a with b | ⟨p, b, β⟩
    · exact ⟨.inr (.inl b), ha⟩
    · have hd := (anchor_roots_nonempty_iff S Q m n b.val (periodPairSlope Λ η X p)).mp
        ⟨β.val, β.property⟩
      exact ⟨.inr (.inr ⟨p, ⟨b, hd⟩⟩), ha⟩
  · rintro ⟨a, ha⟩
    rcases a with a | a
    · exact ⟨.inl (), ha⟩
    rcases a with b | ⟨p, b⟩
    · exact ⟨.inr (.inl b), ha⟩
    · obtain ⟨β, hβ⟩ := (anchor_roots_nonempty_iff S Q m n b.val.val
        (periodPairSlope Λ η X p)).mpr b.property
      exact ⟨.inr (.inr ⟨p, b.val, ⟨β, hβ⟩⟩), ha⟩
