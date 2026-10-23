-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P44.genericGramConservation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:56:21.970631+00:00
-- url     : https://prove2.me/submissions/835197aa-6e9e-4bda-95bd-21d71f09b615

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

lemma X7_kraus_entry {d n : ℕ} (K : Fin n → Mat d) (X : Mat d) (r s : Fin d) :
    krausApply K X r s = ∑ a, ∑ p, ∑ q, K a r p * X p q * conj (K a s q) := by
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul, RCLike.star_def]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

lemma X7_kraus_unit {d n : ℕ} (K : Fin n → Mat d) (i j r s : Fin d) :
    krausApply K (matrixUnit i j) r s = inner ℂ (krausVector K s j) (krausVector K r i) := by
  rw [X7_kraus_entry, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [matrixUnit, Matrix.single_apply, krausVector, PiLp.toLp_apply, RCLike.inner_apply]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp [mul_comm]
    · intro q _ hq; simp [Ne.symm hq]
    · simp
  · intro p _ hp; simp [Ne.symm hp]
  · simp

end

end QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P44 in
theorem solution {d n : ℕ} (hd : 0 < d) (K : Fin n → Mat d)
    (gamma : Fin d → ℝ) (hgamma : ∀ i, 0 ≤ gamma i) (hsum : ∑ i, gamma i = 1) :
    (IsTracePreserving (krausApply K) → ∀ i j,
      (∑ r, inner ℂ (krausVector K r j) (krausVector K r i)) =
        if i = j then 1 else 0) ∧
    (krausApply K (Matrix.diagonal fun i => (gamma i : ℂ)) =
        Matrix.diagonal (fun i => (gamma i : ℂ)) → ∀ r s,
      (∑ i, (gamma i : ℂ) * inner ℂ (krausVector K s i) (krausVector K r i)) =
        if r = s then (gamma r : ℂ) else 0) := by
  constructor
  · intro hTP i j
    have h := hTP (matrixUnit i j)
    simp only [Matrix.trace, Matrix.diag, X7_kraus_unit] at h
    rw [h]
    simp only [matrixUnit, Matrix.single_apply]
    split_ifs with hij
    · subst hij; simp
    · rw [Finset.sum_eq_zero]; intro x _; rw [if_neg]; rintro ⟨rfl, rfl⟩; exact hij rfl
  · intro hfix r s
    have h := congrFun (congrFun hfix r) s
    rw [X7_kraus_entry] at h
    have lhs : (∑ i, (gamma i : ℂ) * inner ℂ (krausVector K s i) (krausVector K r i)) =
        ∑ a, ∑ p, ∑ q, K a r p * Matrix.diagonal (fun i => (gamma i : ℂ)) p q * conj (K a s q) := by
      simp only [Matrix.diagonal_apply, PiLp.inner_apply, krausVector, PiLp.toLp_apply,
        RCLike.inner_apply, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun p _ => ?_
      ring
    rw [lhs, h, Matrix.diagonal_apply]
    try (split_ifs <;> simp_all)

end
