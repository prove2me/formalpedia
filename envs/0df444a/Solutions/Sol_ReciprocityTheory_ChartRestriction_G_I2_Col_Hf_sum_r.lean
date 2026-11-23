-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.Col.Hf_sum_r
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:33.388359+00:00
-- url     : https://prove2.me/submissions/102161a8-4ce3-49df-96b7-4d16f480269a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SecondProjectionOrthogonalComplement
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_Hf_add_r

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex
open scoped InnerProductSpace
noncomputable section
open ReciprocityTheory.ChartRestriction.G.I2.Col
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.I2.Col
theorem _root_.solution {κ : Type} (s : Finset κ) (v : EuclideanSpace ℂ ι) (f : κ → EuclideanSpace ℂ ι) :
    Hf v (∑ k ∈ s, f k) = ∑ k ∈ s, Hf v (f k) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [Hf]
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Hf_add_r, ih]
end ReciprocityTheory.ChartRestriction.G.I2.Col
