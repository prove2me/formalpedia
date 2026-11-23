-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.jetAug_zero_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:48:14.869844+00:00
-- url     : https://prove2.me/submissions/450b1b4a-852b-424f-88cb-cab83d6ea84f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow


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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR epsScaleR IsTangent IsLieComb IsLieBasis)
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution (κ : Type) : Function.Injective (jetAug R κ 0) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have h : RingHom.ker (jetAug R κ 0) = ⊥ := by
    rw [← pow_one (RingHom.ker (jetAug R κ 0))]
    exact ker_jetAug_pow (R := R) κ 0
  have : a ∈ RingHom.ker (jetAug R κ 0) := ha
  rw [h] at this
  exact this
end ReciprocityTheory.ChartRestriction.G.Chart
