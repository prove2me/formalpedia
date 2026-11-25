-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_mem_placeJ_8e5da26ccc5a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:41:56.850126+00:00
-- url     : https://prove2.me/submissions/60db0104-f301-48c3-8aeb-8610834c3e52

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocA
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_mem_ball_a4fbc7617a44

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LB
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Pointwise
variable (l : ℕ) [hl : Fact l.Prime]
variable {l} {Ω : Type} [Field Ω]
namespace Formalism.BasicNotions.Examples₂.LB
theorem _root_.solution (j : Ω →+* PadicAlgCl l) (x : Ω) : x ∈ placeJ j ↔ ‖j x‖ ≤ 1 := by
  rw [placeJ, ValuationSubring.mem_comap, mem_ball]
end Formalism.BasicNotions.Examples₂.LB
