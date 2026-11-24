-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.DA.hd_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:58:14.705109+00:00
-- url     : https://prove2.me/submissions/c2c098df-331c-4b3f-8f8a-0720f8f8d0e5

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
variable {t : ℝ}
namespace PI.UnitaryGroupMassFormula.UsCost.DA
theorem _root_.solution {a b : ℕ} {F : ℝ → Matrix (Fin a) (Fin b) ℂ} {F' : Matrix (Fin a) (Fin b) ℂ} :
    HasDerivAt F F' t ↔ ∀ i j, HasDerivAt (fun y => F y i j) (F' i j) t :=
  (hasDerivAt_pi (φ := F)).trans (forall_congr' fun _ => hasDerivAt_pi)
end PI.UnitaryGroupMassFormula.UsCost.DA
