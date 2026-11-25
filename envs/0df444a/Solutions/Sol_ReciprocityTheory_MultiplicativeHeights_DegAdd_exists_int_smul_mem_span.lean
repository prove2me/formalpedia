-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.DegAdd.exists_int_smul_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:43:39.389149+00:00
-- url     : https://prove2.me/submissions/22e7f5ae-d821-4641-b51d-76ca3aba653c

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_Lemmata_GeneralBFactBisAlt_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsIntSmulMemSpan
import Theorems.Thm_Bl_general_b_fact_bis_other_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open ReciprocityTheory.MultiplicativeHeights.DegAdd
open NumberField
namespace ReciprocityTheory.MultiplicativeHeights.DegAdd
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r n : ℕ}
    (v : Fin n → Fin r → K) {x : Fin r → K} (hx : x ∈ Submodule.span K (Set.range v)) :
    ∃ d : ℤ, d ≠ 0 ∧ d • x ∈ Submodule.span (𝓞 K) (Set.range v) := by
  first | exact Bl.general_b_fact_bis_other.goal1 .. | (apply Bl.general_b_fact_bis_other.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_bis_other.goal1 <;> assumption)
end ReciprocityTheory.MultiplicativeHeights.DegAdd
