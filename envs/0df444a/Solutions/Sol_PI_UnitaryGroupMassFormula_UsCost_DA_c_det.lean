-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.DA.c_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:58:13.570962+00:00
-- url     : https://prove2.me/submissions/5fe52444-3d37-47a4-985e-ea78bfeb496a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_DerivA
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DA_cm_iff

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
theorem _root_.solution {a : ℕ} {F : X → Matrix (Fin a) (Fin a) ℂ} (hF : ContDiffAt ℝ n F x) :
    ContDiffAt ℝ n (fun y => (F y).det) x := by
  rw [cm_iff] at hF
  simp only [Matrix.det_apply']
  exact ContDiffAt.sum fun σ _ => contDiffAt_const.mul (contDiffAt_prod fun i _ => hF _ _)
end PI.UnitaryGroupMassFormula.UsCost.DA
