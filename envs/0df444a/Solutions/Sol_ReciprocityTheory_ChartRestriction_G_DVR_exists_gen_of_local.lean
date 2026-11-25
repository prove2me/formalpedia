-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:01:07.283928+00:00
-- url     : https://prove2.me/submissions/9093ec83-b9bc-4b24-a041-2f26a08b8234

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_exists_gen_of_isLB_local
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_linComb_isLB


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {V : Type} [CommRing V] [IsLocalRing V] {X : Scheme.{0}} (L : LB X) (hL : L.IsLB)
    {K : Type} [Fintype K] (φ : K → (Spec (CommRingCat.of V) ⟶ X)) (ε : K → ℤ) :
    ∃ e : LB.Gen (LB.LinComb L φ ε), e.IsGen := exists_gen_of_isLB_local _ (linComb_isLB (L := L) (φ := φ) (ε := ε) hL)
end ReciprocityTheory.ChartRestriction.G.DVR
