-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.ne_zero_of_hasVal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:25.785771+00:00
-- url     : https://prove2.me/submissions/08551c82-e4a5-4b5a-8f9b-921e824a7605

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalB

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
theorem _root_.solution {c : FractionRing V} {n : ℤ} (hϖ : Irreducible ϖ) (hn : HasVal ϖ c n) : c ≠ 0 := by
  obtain ⟨u, hu⟩ := hn
  rw [hu]
  have hinj := IsFractionRing.injective V (FractionRing V)
  refine mul_ne_zero (zpow_ne_zero _ ?_) ?_
  · exact (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  · exact (map_ne_zero_iff _ hinj).2 u.ne_zero
end ReciprocityTheory.ChartRestriction.G.DVR
