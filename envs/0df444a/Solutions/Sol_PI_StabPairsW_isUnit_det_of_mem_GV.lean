-- Prove2me | solution 1 for PI.StabPairsW.isUnit_det_of_mem_GV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:10:53.1708+00:00
-- url     : https://prove2.me/submissions/97fd8d8e-3439-4307-936e-7176cfc0924a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Theorems.Thm_PI_StabPairsW_det_ne_of_mem_GV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.StabPairsW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}
namespace PI.StabPairsW
theorem _root_.solution {g : B.Mat k r} (hg : g ∈ B.GV k r) : IsUnit g.det :=
  isUnit_iff_ne_zero.2 (det_ne_of_mem_GV hg)
end PI.StabPairsW
