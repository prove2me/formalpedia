-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Host_four_le_n__da3ddea1485c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:32:23.580822+00:00
-- url     : https://prove2.me/submissions/90a77a05-333d-4f60-b60b-7f2b84ba0fbc

import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Theorems.Thm_Formalism_BasicNotions_Ranks_two_pow_le_n
import Theorems.Thm_Formalism_BasicNotions_Host_four_le_two_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.FrobeniusOrbits Formalism.HC
open Formalism Formalism.BasicNotions
open Formalism.BasicNotions.Host
variable {R : Ranks} (H : Host R)
include H
namespace Formalism.BasicNotions.Host
theorem _root_.solution : 4 ≤ R.n := le_trans (four_le_two_pow H) R.two_pow_le_n
end Formalism.BasicNotions.Host
