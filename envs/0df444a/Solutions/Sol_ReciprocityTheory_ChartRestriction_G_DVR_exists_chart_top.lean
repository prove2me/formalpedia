-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.exists_chart_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:18.13518+00:00
-- url     : https://prove2.me/submissions/257f3ebc-b649-4078-9d71-406d5bfc4872

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_eq_top_of_closedPoint_mem

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
    ∃ j₀ : K → L.ι, LB.wchart L φ j₀ = ⊤ := by
  have hc : ∀ k, ∃ i, (φ k).base (IsLocalRing.closedPoint V) ∈ L.U i := by
    intro k
    have : (φ k).base (IsLocalRing.closedPoint V) ∈ (⊤ : X.Opens) := trivial
    rw [← hL.cover] at this
    exact TopologicalSpace.Opens.mem_iSup.1 this
  choose j₀ hj₀ using hc
  exact ⟨j₀, eq_top_of_closedPoint_mem _ (Set.mem_iInter.2 fun k => hj₀ k)⟩
end ReciprocityTheory.ChartRestriction.G.DVR
