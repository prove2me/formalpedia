-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.app_resTop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:51:05.082825+00:00
-- url     : https://prove2.me/submissions/ee971a69-7d29-4628-83e4-be9d700f2d03

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
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {Y Z : Scheme.{0}} (φ : Y ⟶ Z) (U : Z.Opens) {W : Y.Opens} (h : W ≤ φ ⁻¹ᵁ U) (c : Γ(Z, ⊤)) :
    (Y.presheaf.map (homOfLE h).op).hom ((φ.app U).hom (resTop U c)) = resTop W (φ.appTop.hom c) := by
  simp only [resTop]
  have key := congrArg (fun f => (CommRingCat.Hom.hom f) c) (φ.naturality (homOfLE (le_top : U ≤ ⊤)).op)
  simp only [CommRingCat.comp_apply] at key
  rw [key, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl
end ReciprocityTheory.ChartRestriction.G.DVR
