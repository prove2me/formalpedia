-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.TorusInj.charUnit_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:10.396051+00:00
-- url     : https://prove2.me/submissions/d33341a9-eafe-437c-bb0f-09a9fe94557d

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
theorem _root_.solution (χ : X) :
    (charUnit S X χ).val = ((tFst (S := S) X).appLE ⊤ ⊤
      (tle _)).hom
      ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom (AddMonoidAlgebra.single χ 1)) := by
  simp [charUnit, res, pullU, Scheme.Hom.appLE, AddMonoidAlgebra.of_apply]
  rfl
end ReciprocityTheory.ChartRestriction.G.Semi.TorusInj
