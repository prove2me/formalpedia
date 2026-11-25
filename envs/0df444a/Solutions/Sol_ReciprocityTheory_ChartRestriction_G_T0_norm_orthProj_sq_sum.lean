-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.norm_orthProj_sq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:56:02.002295+00:00
-- url     : https://prove2.me/submissions/45fc60df-adb7-4550-a128-cb0add09e6c5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SingleMemStandardLattice
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsNeZeroMemNormSqLeGramDetDivRelIndex
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsSmallSaturatingVector
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_quotDist_eq_sqrt_norm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_norm_realCoords_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Matrix NumberField
open scoped ComplexOrder
variable {K : Type} [Field K] [NumberField K] {r k : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {b : Fin k → Fin r → K} (hb : LinearIndependent K b) (q : Fin r → K) :
    ‖hpv b q‖ ^ 2 = ∑ σ, hQdist σ b q ^ 2 := by
  rw [hpv, norm_realCoords_sq]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [quotDist_eq_sqrt_norm σ hb, Real.sq_sqrt (by unfold hns; positivity)]
end ReciprocityTheory.ChartRestriction.G.T0
