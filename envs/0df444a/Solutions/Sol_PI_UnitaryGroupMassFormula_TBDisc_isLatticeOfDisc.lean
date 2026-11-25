-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.TBDisc.isLatticeOfDisc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:20:26.594689+00:00
-- url     : https://prove2.me/submissions/95773720-17c4-4c7c-9991-0daad2eb4761

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
theorem _root_.solution : IsLatticeOfDiscSt := fun _ _ _ _ _ _ _ _ _ Nf M hM hsp => ⟨fg_of_unifDiscrete Nf M hM, hsp⟩
end PI.UnitaryGroupMassFormula.TBDisc
