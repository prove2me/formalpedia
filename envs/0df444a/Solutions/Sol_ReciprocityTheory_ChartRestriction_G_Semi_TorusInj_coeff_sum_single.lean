-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.TorusInj.coeff_sum_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:16.075097+00:00
-- url     : https://prove2.me/submissions/4db2b1ad-68e3-4e4e-9683-36e93932ecd7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory
open scoped AlgebraMonoidAlgebra
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.TorusInj
variable {S : Scheme.{0}} (X : Type) [AddCommGroup X] (Y : Over S)
namespace ReciprocityTheory.ChartRestriction.G.Semi.TorusInj
theorem _root_.solution {A : Type} [CommRing A] (s : Finset X) (g : X → A) (χ₀ : X) (h : χ₀ ∈ s) :
    (∑ c ∈ s, AddMonoidAlgebra.single c (g c)).coeff χ₀ = g χ₀ := by
  classical
  first
  | simp [AddMonoidAlgebra.coeff, Finsupp.finset_sum_apply, Finsupp.single_apply, h]
  | simp [Finsupp.finset_sum_apply, Finsupp.single_apply, h]
  | simp [AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single, h]
end ReciprocityTheory.ChartRestriction.G.Semi.TorusInj
