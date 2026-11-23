-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.TorusInj.appLE_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:10.115868+00:00
-- url     : https://prove2.me/submissions/12f7fc4b-3279-4b87-ba52-6d109dd1912c

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
variable {X Y} {V : Y.left.Opens} (hV : IsAffineOpen V)
attribute [local instance] zuAlg
namespace ReciprocityTheory.ChartRestriction.G.Semi.TorusInj
theorem _root_.solution {A B : Scheme.{0}} {f g : A ⟶ B} (hfg : f = g) {U : B.Opens} {W : A.Opens}
    (e : W ≤ f ⁻¹ᵁ U) : f.appLE U W e = g.appLE U W (hfg ▸ e) := by
  subst hfg
  rfl
end ReciprocityTheory.ChartRestriction.G.Semi.TorusInj
