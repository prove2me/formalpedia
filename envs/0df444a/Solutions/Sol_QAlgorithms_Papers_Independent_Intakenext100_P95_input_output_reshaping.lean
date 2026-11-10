-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P95.input_output_reshaping
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T01:52:21.096403+00:00
-- url     : https://prove2.me/submissions/16f54320-f28d-4b77-acd7-000373d38bff

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P95

open scoped Matrix ComplexConjugate

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

open QAlgorithms.Papers.Independent.Intakenext100.P95 in
theorem solution {A1 A2 B : Type*}
    [Fintype A1] [Fintype A2] [Fintype B] [DecidableEq A1] [DecidableEq A2]
    (T : Matrix B (A2 × A1) ℂ) (hT : Tᴴ * T = 1) :
    (moveInput T)ᴴ * moveInput T = (Fintype.card A2 : ℂ) • 1 := by
  ext a1 a1'
  have h : ∀ a2, ∑ b, star (T b (a2, a1)) * T b (a2, a1') = if a1 = a1' then 1 else 0 := by
    intro a2
    have := congrFun (congrFun hT (a2, a1)) (a2, a1')
    rw [Matrix.mul_apply] at this
    simp only [Matrix.conjTranspose_apply] at this
    rw [this]
    by_cases ha : a1 = a1'
    · subst ha; simp
    · have : (a2, a1) ≠ (a2, a1') := fun h => ha (Prod.mk.inj h).2
      simp [Matrix.one_apply, this, ha]
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, moveInput, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [h]
  by_cases ha : a1 = a1'
  · subst ha; simp
  · simp [ha, Matrix.one_apply]
