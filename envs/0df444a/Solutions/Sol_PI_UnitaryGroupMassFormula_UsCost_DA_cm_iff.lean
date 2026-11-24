-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.DA.cm_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:17:26.051949+00:00
-- url     : https://prove2.me/submissions/cf6c166f-aa07-4b4f-ba29-efa8f989b6be

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_DerivA

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
theorem _root_.solution {a b : ℕ} {F : X → Matrix (Fin a) (Fin b) ℂ} :
    ContDiffAt ℝ n F x ↔ ∀ i j, ContDiffAt ℝ n (fun y => F y i j) x :=
  (contDiffAt_pi (Φ := F)).trans (forall_congr' fun _ => contDiffAt_pi)
end PI.UnitaryGroupMassFormula.UsCost.DA
