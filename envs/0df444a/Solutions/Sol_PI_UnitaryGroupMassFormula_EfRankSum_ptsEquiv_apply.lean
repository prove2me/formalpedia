-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.EfRankSum.ptsEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:40:29.295225+00:00
-- url     : https://prove2.me/submissions/791e447c-5e38-4da6-a23a-71cc8de6feb4

import Definitions.Def_Formalism_PeriodIntegrals_EfRankSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RamificationRankSum_Points

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.EfRankSum
open Formalism.MainNotions.Gaps.EtaleWeightGaps IsLocalRing
namespace PI.UnitaryGroupMassFormula.EfRankSum
theorem _root_.solution (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] [Algebra O A] (ζ : Pts O A) :
    ((ptsEquiv O A ζ : (maximalIdeal O).primesOver ↥(As O A)) : Ideal ↥(As O A)) = ζ.asIdeal := rfl
end PI.UnitaryGroupMassFormula.EfRankSum
