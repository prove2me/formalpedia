-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.logHeight_le_torusHeight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:32:00.221726+00:00
-- url     : https://prove2.me/submissions/2fded6f2-3f09-4737-86a0-59245da94252

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ContinuousTorusPoint
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_map_ne_zero_of_ne_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_Closed_sphereLeTorus
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_isMultiHomogeneous_map_ring


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {K : Type} [Field K] [NumberField K] {B n : ℕ} (hn : 0 < n) (a : Fin B → ℕ)
    (f : MvPolynomial (Fin B × Fin n) K) (hf : f ≠ 0) (ha : IsMultiHomogeneous a f) :
    h0 f ≤ hTX5 f := by
  unfold h0 hTX5
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  refine add_le_add le_rfl (Finset.sum_le_sum fun σ _ => ?_)
  exact sphereLeTorus B n a _ hn (map_ne_zero_of_ne_zero hf σ) (isMultiHomogeneous_map_ring a f ha σ)
end ReciprocityTheory.ChartRestriction.G.T0
