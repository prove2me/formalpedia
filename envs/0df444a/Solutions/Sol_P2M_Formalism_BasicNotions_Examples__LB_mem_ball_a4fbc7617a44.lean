-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_mem_ball_a4fbc7617a44
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:30:57.555883+00:00
-- url     : https://prove2.me/submissions/2ea80b7f-639a-4ed3-a416-d75e41a9089e

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocA

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
namespace Formalism.BasicNotions.Examples₂.LB
theorem _root_.solution (x : PadicAlgCl l) : x ∈ ball l ↔ ‖x‖ ≤ 1 := by
  rw [ball, Valuation.mem_valuationSubring_iff]
  first
    | exact Iff.rfl
    | (rw [← NNReal.coe_le_coe]; rfl)
    | simp
end Formalism.BasicNotions.Examples₂.LB
