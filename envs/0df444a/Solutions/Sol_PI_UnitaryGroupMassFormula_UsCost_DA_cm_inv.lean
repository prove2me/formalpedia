-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.DA.cm_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:08:58.364782+00:00
-- url     : https://prove2.me/submissions/f39b47c2-3b04-4656-8124-1068a4b68b96

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_DerivA
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DA_cm_iff
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DA_c_det
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DA_cm_updateRow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.DA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {x : X}
namespace PI.UnitaryGroupMassFormula.UsCost.DA
theorem _root_.solution {a : ℕ} {F : X → Matrix (Fin a) (Fin a) ℂ} (hF : ContDiffAt ℝ n F x) (hu : (F x).det ≠ 0) :
    ContDiffAt ℝ n (fun y => (F y)⁻¹) x := by
  rw [cm_iff]
  intro i j
  have e : (fun y => (F y)⁻¹ i j)
      = fun y => ((F y).det)⁻¹ * ((F y).updateRow j (Pi.single i 1)).det := by
    funext y
    rw [Matrix.inv_def, Matrix.smul_apply, adjugate_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [e]
  exact ((c_det hF).inv hu).mul (c_det (cm_updateRow hF j _))
end PI.UnitaryGroupMassFormula.UsCost.DA
