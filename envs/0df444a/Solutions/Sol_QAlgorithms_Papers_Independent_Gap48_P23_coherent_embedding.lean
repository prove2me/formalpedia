-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P23.coherent_embedding
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T00:28:29.622602+00:00
-- url     : https://prove2.me/submissions/f2632bca-31ac-45ac-90dd-028b5abf4cdf

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23
noncomputable section

open QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)


lemma g74f_physPow (ell : ℕ) (psi : EuclideanSpace ℂ (Fin 2)) (x : QAlgorithms.Qubits ell) :
    (∏ i, psi (QAlgorithms.Papers.Independent.Support21.P18.bitIndex (x i))) =
      psi 0 ^ (ell - QAlgorithms.hammingWeight x) * psi 1 ^ QAlgorithms.hammingWeight x := by
  have h1 : ∀ i, psi (QAlgorithms.Papers.Independent.Support21.P18.bitIndex (x i)) =
      if x i = true then psi 1 else psi 0 := by
    intro i; cases x i <;> simp [QAlgorithms.Papers.Independent.Support21.P18.bitIndex]
  simp_rw [h1]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin ell))) (fun i : Fin ell => x i = true)
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  unfold QAlgorithms.hammingWeight
  rw [mul_comm]
  congr 2
  omega

theorem solution (ell : ℕ) (psi : EuclideanSpace ℂ (Fin 2)) :
    WithLp.toLp 2 ((symmetricEmbedding ell).mulVec (monomialKet ell psi)) =
      QAlgorithms.Papers.Independent.Support21.P18.physicalPower ell psi := by
  ext x
  simp only [QAlgorithms.Papers.Independent.Support21.P18.physicalPower, PiLp.toLp_apply]
  rw [g74f_physPow]
  simp only [Matrix.mulVec, dotProduct, symmetricEmbedding,
    QAlgorithms.Papers.Independent.Support21.P18.occupationEmbedding, monomialKet, PiLp.toLp_apply]
  have hle : QAlgorithms.hammingWeight x < ell + 1 := by
    have : QAlgorithms.hammingWeight x ≤ ell := by
      unfold QAlgorithms.hammingWeight
      exact (Finset.card_filter_le _ _).trans (by simp)
    omega
  rw [Finset.sum_eq_single ⟨QAlgorithms.hammingWeight x, hle⟩]
  · simp only [if_true]
    have hpos : (0:ℝ) < Real.sqrt (Nat.choose ell (QAlgorithms.hammingWeight x) : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Nat.choose_pos (by omega))
    have hne : ((Real.sqrt (Nat.choose ell (QAlgorithms.hammingWeight x) : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast hpos.ne'
    field_simp
  · intro b _ hb
    rw [if_neg]; · simp
    intro h; apply hb; ext; simp [h]
  · simp

end
