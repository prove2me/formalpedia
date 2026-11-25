-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.app_resTop_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:15:34.429177+00:00
-- url     : https://prove2.me/submissions/ebf15825-00e0-4664-ae06-5d9194118881

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RValue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExpandsAtScale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_app_resTop

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
theorem _root_.solution {Y Z : Scheme.{0}} (φ : Y ⟶ Z) {U : Z.Opens} {W : Y.Opens} (w : W ≤ φ ⁻¹ᵁ U) (c : Γ(Z, ⊤)) :
    rs w ((φ.app U).hom (resTop U c)) = resTop W (φ.appTop.hom c) := app_resTop φ U w c
end ReciprocityTheory.ChartRestriction.G.DVR
