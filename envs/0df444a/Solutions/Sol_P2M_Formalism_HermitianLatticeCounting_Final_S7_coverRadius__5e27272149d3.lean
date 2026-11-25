-- Prove2me | solution 1 for P2M_Formalism_HermitianLatticeCounting_Final_S7_coverRadius__5e27272149d3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:44:40.160104+00:00
-- url     : https://prove2.me/submissions/fa77f12b-e8b5-43b7-ab44-ed41642bfede

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoveringOfTransferenceVariant
import Definitions.Def_Formalism_FlagUnipotentLattices_FinalTr
import Theorems.Thm_P2M_Formalism_HermitianLatticeCounting_P_covering_radius_bound__3b5882ae4a38


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.Final Formalism.HermitianLatticeCounting.Final.S7
namespace Formalism.HermitianLatticeCounting.Final.S7
theorem _root_.solution : Formalism.HermitianLatticeCounting.S7.CoveringRadius2 := Formalism.HermitianLatticeCounting.P.covering_radius_bound₂
end Formalism.HermitianLatticeCounting.Final.S7
