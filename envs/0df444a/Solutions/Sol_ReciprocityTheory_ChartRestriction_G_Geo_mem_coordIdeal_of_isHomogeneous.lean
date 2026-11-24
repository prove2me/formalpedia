-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.mem_coordIdeal_of_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:39.509234+00:00
-- url     : https://prove2.me/submissions/5d8e5031-389d-43d6-841a-9ae3bc276dd5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_coneMap_of_isHomogeneous

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
theorem _root_.solution (x : ι → Ω) {f : MvPolynomial ι o} {n : ℕ}
    (hf : f.IsHomogeneous n) (h : aeval x f = 0) : f ∈ coordIdeal o x := by
  rw [coordIdeal, RingHom.mem_ker, coneMap_of_isHomogeneous o x hf, h, map_zero, zero_mul]
end ReciprocityTheory.ChartRestriction.G.Geo
