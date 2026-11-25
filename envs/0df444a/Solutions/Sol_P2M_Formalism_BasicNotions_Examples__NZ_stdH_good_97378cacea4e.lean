-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_stdH_good_97378cacea4e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:40:58.633831+00:00
-- url     : https://prove2.me/submissions/4dc06485-73c6-4a06-b9a4-ff4c763e5bf3

import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataForms
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZRowA
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_stdH_span_4803d385f5ba
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_stdH_frames_91564ebb4ca5

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open NumberField IsDedekindDomain Formalism.BasicNotions
variable (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ)
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution : (stdH K n).Good :=
  ⟨stdH_frames K n, Submodule.fg_span (Set.finite_range _), stdH_span K n⟩
end Formalism.BasicNotions.Examples₂.NZ
