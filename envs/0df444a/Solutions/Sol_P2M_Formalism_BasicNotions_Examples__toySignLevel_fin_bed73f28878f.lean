-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__toySignLevel_fin_bed73f28878f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:49:32.059176+00:00
-- url     : https://prove2.me/submissions/b8d4a7d5-fb6c-45a2-81b0-7021a5ea055d

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_DataS
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GPlacesExampleNatAct

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
theorem _root_.solution (p : ℕ) : (toySignLevel p).FinClasses := by
  refine ⟨{default}, fun _ _ v => v.elim0, fun L _ => ⟨default,
    Finset.mem_singleton_self _, 1, Subsingleton.elim _ _⟩⟩
end Formalism.BasicNotions.Examples₂
