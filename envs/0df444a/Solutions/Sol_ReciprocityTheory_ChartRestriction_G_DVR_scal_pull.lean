-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.scal_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:06:12.591458+00:00
-- url     : https://prove2.me/submissions/17656b27-763a-4166-bb3e-c3e94128fda8

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
theorem _root_.solution {Y Z : Scheme.{0}} (φ : Y ⟶ Z) (pY : Y ⟶ Spec (CommRingCat.of V)) (pZ : Z ⟶ Spec (CommRingCat.of V))
    (hφ : φ ≫ pZ = pY) (r : V) : φ.appTop.hom (scal pZ r) = scal pY r := by
  subst hφ
  simp only [scal, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
end ReciprocityTheory.ChartRestriction.G.DVR
