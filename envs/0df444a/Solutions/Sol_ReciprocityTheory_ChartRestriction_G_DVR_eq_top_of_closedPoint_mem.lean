-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.eq_top_of_closedPoint_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:29:38.213117+00:00
-- url     : https://prove2.me/submissions/bfa2e4af-5c41-4945-bb79-ae590d8f88cd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC

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
theorem _root_.solution {V : Type} [CommRing V] [IsLocalRing V] (U : (Spec (CommRingCat.of V)).Opens)
    (hU : (IsLocalRing.closedPoint V : Spec (CommRingCat.of V)) ∈ U) : U = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  exact (IsLocalRing.specializes_closedPoint (R := V) x).mem_open U.isOpen hU
end ReciprocityTheory.ChartRestriction.G.DVR
