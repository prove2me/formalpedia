-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__bridge_unit_rule_holds_169e1c751cc8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:24.179702+00:00
-- url     : https://prove2.me/submissions/f40f7649-c7fc-4213-9b34-f5342751387c

import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Places
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__PlacesToy_prime_mem_unique_e91ad699f71a

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
namespace Formalism.BasicNotions.Examples₂
theorem _root_.solution : Formalism.BasicNotions.bridge_unit_rule := by
  intro K _ _ l w hl hlw
  obtain rfl := PlacesToy.prime_mem_unique w hl (PlacesToy.resCharW_prime w) hlw
    (PlacesToy.resCharW_mem w)
  exact PlacesToy.vAdd_resCharW w
end Formalism.BasicNotions.Examples₂
