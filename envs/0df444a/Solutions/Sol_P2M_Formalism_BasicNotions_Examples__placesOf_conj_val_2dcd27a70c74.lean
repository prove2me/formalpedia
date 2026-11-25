-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__placesOf_conj_val_2dcd27a70c74
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:55:14.392022+00:00
-- url     : https://prove2.me/submissions/ca030c83-dab3-4973-8398-cd5a362c87eb

import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Places
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__PlacesToy_valW_conjW_54cdb2d01ef8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
variable (K : Type) [Field K] [NumberField K] [StarRing K]
namespace Formalism.BasicNotions.Examples₂
theorem _root_.solution (w : (placesOf K).Pl) (x : K) :
    (placesOf K).val ((placesOf K).conj w) x = (placesOf K).val w (star x) :=
  PlacesToy.valW_conjW w x
end Formalism.BasicNotions.Examples₂
