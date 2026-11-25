-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__gAtPExample_M_0eadaf3839f7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:41:50.903043+00:00
-- url     : https://prove2.me/submissions/cd0412a8-9e5c-4ba5-8d33-7effd4352988

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_DataS
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GPlacesExampleNatAct
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__toySignLevel_M_345e95b890e8

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
theorem _root_.solution (p : ℕ) : (gAtPExample p).M = ⊥ := by
  rw [eq_bot_iff]
  intro F hF
  rw [Submodule.mem_bot]
  funext i
  have h : F i ∈ (toySignLevel p).M := hF i (Set.mem_univ i)
  rw [toySignLevel_M] at h
  exact h
end Formalism.BasicNotions.Examples₂
