-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.finite_place_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:25.762058+00:00
-- url     : https://prove2.me/submissions/d531fc7e-91de-4e5a-915e-691d97123d8d

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_Lemmata_GeneralBFactLeftExtra_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussAbsMulOfMonomialOrder
import Theorems.Thm_Bl_general_b_fact_left_extra_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open NumberField
variable {K : Type*} [Field K] [NumberField K] {σ : Type*}
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {ι : Type*} (w : FinitePlace K) (t : Finset ι) (a : ι → K) {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ i ∈ t, w (a i) ≤ M) : w (∑ i ∈ t, a i) ≤ M := by
  first | exact Bl.general_b_fact_left_extra.goal1 .. | (apply Bl.general_b_fact_left_extra.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_extra.goal1 <;> assumption)
end ReciprocityTheory.MultiplicativeHeights
