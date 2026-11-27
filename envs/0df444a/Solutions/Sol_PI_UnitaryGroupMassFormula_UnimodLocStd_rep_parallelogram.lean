-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_parallelogram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:17:57.103728+00:00
-- url     : https://prove2.me/submissions/86d0c1d8-3f0f-4e64-acb0-41d9708f692b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable (L : PeriodPair) (m : Type) [Fintype m] [DecidableEq m]
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (f w : m → ℂ) :
    stdH L m (f - w) (f - w) + stdH L m (f - -w) (f - -w) = 2 * stdH L m f f + 2 * stdH L m w w := by
  simp only [map_sub, map_neg, LinearMap.sub_apply, LinearMap.neg_apply]
  ring
end PI.UnitaryGroupMassFormula.UnimodLocStd
