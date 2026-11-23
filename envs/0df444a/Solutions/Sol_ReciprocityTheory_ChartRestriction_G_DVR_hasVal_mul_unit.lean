-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.hasVal_mul_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:29:51.338064+00:00
-- url     : https://prove2.me/submissions/9e0865f6-9267-412b-b214-0951c4b3dc86

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
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {c : FractionRing V} {n : ℤ} (hn : HasVal ϖ c n) (v : Vˣ) :
    HasVal ϖ (c * algebraMap V (FractionRing V) (v : V)) n := by
  obtain ⟨u, hu⟩ := hn
  refine ⟨u * v, ?_⟩
  rw [hu, Units.val_mul, map_mul]
  ring
end ReciprocityTheory.ChartRestriction.G.DVR
