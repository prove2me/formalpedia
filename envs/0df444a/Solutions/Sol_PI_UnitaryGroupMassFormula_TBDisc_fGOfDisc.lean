-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.TBDisc.fGOfDisc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:19:35.530815+00:00
-- url     : https://prove2.me/submissions/111b221e-74ab-4f1a-bf07-0dd85cda261c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_RatIntUnifDiscrete
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_UniformDiscreteness_FgOfUnifDiscrete
import Theorems.Thm_PI_UnitaryGroupMassFormula_TBDisc_fg_of_unifDiscrete

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.TBDisc
open NumberField ReciprocityTheory.ChartRestriction.G.TB
namespace PI.UnitaryGroupMassFormula.TBDisc
theorem _root_.solution : FGOfDiscSt := fun _ _ _ _ _ _ _ _ _ Nf M hM => fg_of_unifDiscrete Nf M hM
end PI.UnitaryGroupMassFormula.TBDisc
