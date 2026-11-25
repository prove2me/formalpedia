-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__gAtPExample_d_f5f7418bdaa1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:52:55.994066+00:00
-- url     : https://prove2.me/submissions/98f184f9-23a0-46d1-bcd7-b0d0935fe5ad

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_DataS
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GPlacesExampleNatAct
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__gAtPExample_M_0eadaf3839f7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
open Formalism.BasicNotions NumberField IsDedekindDomain
open Formalism.MainNotions.G
namespace Formalism.BasicNotions.Examples₂
theorem _root_.solution (p : ℕ) : (gAtPExample p).d = 0 := by
  unfold GAtP.d
  rw [gAtPExample_M]
  exact finrank_bot _ _
end Formalism.BasicNotions.Examples₂
