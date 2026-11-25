-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.rv_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:13:56.090968+00:00
-- url     : https://prove2.me/submissions/b858ce6c-7907-4a9b-9e79-b3fb0193651f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RValue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RValuePf

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
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (x y : D.toPre.X) :
    (lift (toUnit (TF (R := V) F) ≫ D.toPre.c x) (toUnit (TF (R := V) F) ≫ D.toPre.c y) :
      TF (R := V) F ⟶ D.toPre.P.A ⊗ D.toPre.P.A).left = jFK (R := V) F ≫ D.toPre.pt2 x y := by
  have e : (Over.homMk (jFK (R := V) F) rfl : TF (R := V) F ⟶ TK V) ≫
      lift (toUnit (TK V) ≫ D.toPre.c x) (toUnit (TK V) ≫ D.toPre.c y) =
      lift (toUnit _ ≫ D.toPre.c x) (toUnit _ ≫ D.toPre.c y) := by
    rw [comp_lift, ← Category.assoc, ← Category.assoc, toUnit_unique (_ ≫ toUnit (TK V)) (toUnit _)]
  rw [← e]; rfl
end ReciprocityTheory.ChartRestriction.G.DVR
