-- Prove2me | solution 1 for RotationLadder.Protocol.rotation_circuit
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T01:43:25.043205+00:00
-- url     : https://prove2.me/submissions/cdb0e48c-e711-4298-9e17-c5bc62e5b063

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_RotationLadder_Protocol_cnotSecond
import Definitions.Def_RotationLadder_Protocol_ketZ
import Definitions.Def_RotationLadder_Protocol_postOut
import Definitions.Def_RotationLadder_Protocol_zRot

open RotationLadder.Protocol in
theorem solution :
    ∀ (α : ℝ) (ψ : EuclideanSpace ℂ Bool),
      postOut false (QAlgorithms.act cnotSecond (QAlgorithms.tensorVec (ketZ α) ψ)) =
          ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • QAlgorithms.act (zRot α) ψ ∧
      postOut true (QAlgorithms.act cnotSecond (QAlgorithms.tensorVec (ketZ α) ψ)) =
          (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * Complex.exp (Complex.I * (α : ℂ))) • QAlgorithms.act (zRot (-α)) ψ := by
  intro α ψ
  have hexp : Complex.exp (Complex.I * (α : ℂ)) * Complex.exp (Complex.I * ((-α : ℝ) : ℂ)) = 1 := by
    rw [← Complex.exp_add]; push_cast; ring_nf; exact Complex.exp_zero
  have hexp' : Complex.exp (Complex.I * (α : ℂ)) * Complex.exp (-(Complex.I * (α : ℂ))) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  constructor <;> ext q <;> cases q <;>
    simp [postOut, QAlgorithms.act, cnotSecond, QAlgorithms.tensorVec, ketZ, zRot,
      Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.diagonal_apply, hexp]
  all_goals first
    | ring1
    | linear_combination (-(((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * WithLp.ofLp ψ true)) * hexp'
