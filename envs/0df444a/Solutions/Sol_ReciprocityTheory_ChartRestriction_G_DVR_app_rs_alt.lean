-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.app_rs_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:48:58.160455+00:00
-- url     : https://prove2.me/submissions/e09061bc-b962-49a6-9294-eaac3d2df351

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RValue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExpandsAtScale

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable {G : Over (Spec (CommRingCat.of V))}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {Y Z : Scheme.{0}} (φ : Y ⟶ Z) {U U' : Z.Opens} {W : Y.Opens} (o : U ≤ U') (w : W ≤ φ ⁻¹ᵁ U)
    (w' : W ≤ φ ⁻¹ᵁ U') (z : Γ(Z, U')) : rs w ((φ.app U).hom (rs o z)) = rs w' ((φ.app U').hom z) := by
  simp only [rs, ← CommRingCat.comp_apply]
  rw [Scheme.Hom.naturality, Category.assoc, ← Functor.map_comp]
  rfl
end ReciprocityTheory.ChartRestriction.G.DVR
