-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.clear_denom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:44:39.803944+00:00
-- url     : https://prove2.me/submissions/4223eaaf-fd29-4149-8f2c-c02762e30a74

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegZ
import Definitions.Def_Lemmata_GeneralBFactSecondAlt_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegZA
import Theorems.Thm_Bl_general_b_fact_second_alt_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ}
    (L : Submodule (𝓞 K) (Fin r → K)) (v : Fin r → K)
    (hv : v ∈ Submodule.span K (L : Set (Fin r → K))) : ∃ a : 𝓞 K, a ≠ 0 ∧ a • v ∈ L := by
  first | exact Bl.general_b_fact_second_alt.goal1 .. | (apply Bl.general_b_fact_second_alt.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_alt.goal1 <;> assumption)
end ReciprocityTheory.MultiplicativeHeights.SemiPt
