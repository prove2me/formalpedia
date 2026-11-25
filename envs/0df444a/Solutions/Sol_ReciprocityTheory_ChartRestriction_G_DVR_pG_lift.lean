-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.pG_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:00:44.681899+00:00
-- url     : https://prove2.me/submissions/bb32d0c5-0218-450b-b329-971adcde7dab

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RsAppPullGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_MemFinsetInf

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
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e : ℕ) (χ : D.toPre.X) :
    (U.gt e).pG.left ≫ (lift (toUnit D.toPre.P.A ≫ D.toPre.c χ) (𝟙 D.toPre.P.A)).left =
      (lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG).left := by
  first
    | rw [← Over.comp_left, comp_lift, comp_toUnit_assoc, Category.comp_id]
    | simp [← Over.comp_left]
end ReciprocityTheory.ChartRestriction.G.DVR
