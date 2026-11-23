-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sc_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:16.920221+00:00
-- url     : https://prove2.me/submissions/ddde1c65-cfe5-48ac-acb8-01d54b86b5bf

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_Lemmata_GeneralBFactSecond_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiContractC
import Theorems.Thm_Bl_general_b_fact_second_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField Module
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} (L : Submodule (𝓞 K) (Fin r → K))
    (hL : Submodule.span K (L : Set (Fin r → K)) = ⊤) (x : Fin r → K) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ L := by
  first | exact Bl.general_b_fact_second.goal1 .. | (apply Bl.general_b_fact_second.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second.goal1 <;> assumption)
end ReciprocityTheory.MultiplicativeHeights
