-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.qmap_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:01.071575+00:00
-- url     : https://prove2.me/submissions/35878944-f4a7-41cd-9447-b67f8baf4ad6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
variable {σ : Type}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution : Function.Injective (qmap : MvPolynomial σ ℤ → MvPolynomial σ ℚ) := MvPolynomial.map_injective _ Int.cast_injective
end ReciprocityTheory.ChartRestriction.G.Geo
