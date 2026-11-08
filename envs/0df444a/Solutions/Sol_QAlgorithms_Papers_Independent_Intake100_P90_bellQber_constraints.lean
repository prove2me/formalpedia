-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P90.bellQber_constraints
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T03:57:57.612669+00:00
-- url     : https://prove2.me/submissions/04237a9f-23a2-4101-9cac-725d34658d3b

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P90

noncomputable section

open scoped ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Intake100.P90 in
theorem solution (w : Fin 4 → ℝ)
    (hw : ∀ l, 0 ≤ w l) (hsum : ∑ l, w l = 1) :
    let Q := sourceZDisagreement (sourceBellDiagonal w)
    Q = w 2 + w 3 ∧ w 0 = 1 - Q - w 1 ∧ w 3 = Q - w 2 := by
  intro Q
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2' : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
    rw [← mul_inv, h2, one_div]
  have hQ : Q = w 2 + w 3 := by
    show sourceZDisagreement (sourceBellDiagonal w) = _
    simp [sourceZDisagreement, sourceBellDiagonal, Matrix.sum_apply, QAlgorithms.pureDensity,
      sourceBell, Fin.sum_univ_four]
    ring_nf
    rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    ring
  rw [Fin.sum_univ_four] at hsum
  refine ⟨hQ, ?_, ?_⟩ <;> linarith
