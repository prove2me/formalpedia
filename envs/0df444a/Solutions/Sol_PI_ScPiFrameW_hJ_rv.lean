-- Prove2me | solution 1 for PI.ScPiFrameW.hJ_rv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:58:55.877601+00:00
-- url     : https://prove2.me/submissions/7546567d-ab64-42ef-9419-ca4f1bfff84a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_Transfer
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ScPiFrameW
open PI.ScPiExists
namespace PI.ScPiFrameW
theorem _root_.solution (I : Formalism.MainNotions.S.AutInst) (v : NumberField.InfinitePlace I.F) (x y : Fin I.n → I.E) :
    hJ (I.ε v) (rv I v x) (rv I v y) = I.φ v (Formalism.UG.hform (starRingEnd I.E) I.J x y) := by
  have hstar : ∀ a : I.E, I.φ v (star a) = star (I.φ v a) := fun a =>
    I.cm.cmUnram.2.1 (I.φ v) a
  have hP : I.P v * (I.P v)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))
  have key : hJ (I.ε v) (rv I v x) (rv I v y) =
      star (fun i => I.φ v (x i)) ⬝ᵥ ((I.J.map (I.φ v)) *ᵥ fun j => I.φ v (y j)) := by
    unfold hJ rv
    rw [← I.P_spec v, Matrix.mulVec_mulVec, Matrix.mul_assoc, hP, Matrix.mul_one,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec,
      Matrix.mulVec_mulVec, hP, Matrix.one_mulVec]
  rw [key]
  simp only [Formalism.UG.hform, map_sum, map_mul, starRingEnd_apply, hstar, dotProduct, mulVec,
    Matrix.map_apply, Pi.star_apply, Finset.mul_sum, mul_assoc]
end PI.ScPiFrameW
