-- Prove2me | solution 1 for P2M_Formalism_CountingSumsFrames_Top_segSTopRoom__1a63d1655c17
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:50:54.86119+00:00
-- url     : https://prove2.me/submissions/fdbefc08-160b-43e9-b690-a31702c966f6

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentHypOfIntervalHyp
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentTopRoomPublished
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentBoundThreeHolds
import Definitions.Def_Formalism_PolynomialDimension_ChangeLatticeGoodRank
import Theorems.Thm_P2M_Formalism_CountingSumsFrames_segment_top_room__9bcf6696b84d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.Top
namespace Formalism.CountingSumsFrames.Top
theorem _root_.solution : Formalism.CountingSumsFrames.SegmentTopRoom := Formalism.CountingSumsFrames.segment_top_room₂
end Formalism.CountingSumsFrames.Top
