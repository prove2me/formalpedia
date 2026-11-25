-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Host_finrank_E__2a7c74e41420
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:32:38.924086+00:00
-- url     : https://prove2.me/submissions/1f055a86-6c5e-4c52-852c-6ca98a207148

import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_LocalRingCardinality_HostCls

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
namespace Formalism.BasicNotions.Host
theorem _root_.solution : Module.finrank ℚ H.E = 2 * R.f := by
  rw [H.der.finrank_E]
  show 4 * R.ord = 2 * (2 * R.ord)
  ring
end Formalism.BasicNotions.Host
