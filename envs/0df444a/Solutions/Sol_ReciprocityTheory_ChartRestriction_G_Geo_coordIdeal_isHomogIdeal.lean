-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.coordIdeal_isHomogIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:42.10923+00:00
-- url     : https://prove2.me/submissions/8bcf1c5f-5b31-41b5-a7ae-00f86dc02fa1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_coneMap_of_isHomogeneous
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_coeff_coneMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
variable (o : Type*) {Ω : Type*} [CommRing o] [CommRing Ω] [Algebra o Ω] {ι : Type*}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (x : ι → Ω) : IsHomogIdeal o (coordIdeal o x) := by
  intro f hf d
  rw [coordIdeal, RingHom.mem_ker] at hf ⊢
  rw [coneMap_of_isHomogeneous o x (homogeneousComponent_isHomogeneous d f), ← coeff_coneMap, hf,
    Polynomial.coeff_zero, map_zero, zero_mul]
end ReciprocityTheory.ChartRestriction.G.Geo
