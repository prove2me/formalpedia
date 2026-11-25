-- Prove2me | solution 1 for PI.VolSemiDirect.W.SR.stable_rank_one_infinite_adeles
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:03:10.916427+00:00
-- url     : https://prove2.me/submissions/f6e11b20-90a3-4d70-a097-603697ad6208

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HasStableRangeOne
import Theorems.Thm_PI_VolSemiDirect_W_SR_stable_rank_one_pi_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.SR
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped RestrictedProduct
namespace PI.VolSemiDirect.W.SR
theorem _root_.solution (F : Type) [Field F] [NumberField F] :
    Cj.HasStableRangeOne (InfiniteAdeleRing F) :=
  stable_rank_one_pi_field
end PI.VolSemiDirect.W.SR
