-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.comp_app_rs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:07:36.592506+00:00
-- url     : https://prove2.me/submissions/de35393b-2038-40ea-a89c-4103b2759c21

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
theorem _root_.solution {X Y Z : Scheme.{0}} (φ : Y ⟶ Z) (ψ : Z ⟶ X) {U : X.Opens} {W : Y.Opens}
    (w : W ≤ (φ ≫ ψ) ⁻¹ᵁ U) (w' : W ≤ φ ⁻¹ᵁ (ψ ⁻¹ᵁ U)) (z : Γ(X, U)) :
    rs w (((φ ≫ ψ).app U).hom z) = rs w' ((φ.app (ψ ⁻¹ᵁ U)).hom ((ψ.app U).hom z)) := by
  rw [Scheme.Hom.comp_app]
  rfl
end ReciprocityTheory.ChartRestriction.G.DVR
