-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_DVR_GC_fam__eq_3a137bedd551
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:16.988029+00:00
-- url     : https://prove2.me/submissions/1d7ca10b-f940-4b55-abf5-5e13f52478cc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_QuadTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc

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
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.GC
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
  [Algebra (FractionRing R) F]
namespace ReciprocityTheory.ChartRestriction.G.DVR.GC
theorem _root_.solution (α : D.X) (k : Fin 4) :
    DegPre.famφ D F α k = (DegPre.prB D F).left ≫ D.famφB α k := by
  fin_cases k
  · show (DegPre.prB D F).left = (DegPre.prB D F).left ≫ 𝟙 _
    simp
  · show (padd D.P.A (DegPre.prB D F) (toUnit _ ≫ D.c α)).left =
      (DegPre.prB D F).left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left
    rw [← Over.comp_left]; congr 1; simp [padd, comp_lift_assoc]
  · show (toUnit _ ≫ D.c α).left = (DegPre.prB D F).left ≫ (toUnit D.P.A ≫ D.c α).left
    rw [← Over.comp_left]; congr 1; simp
  · show (toUnit _ ≫ η[D.P.A]).left = (DegPre.prB D F).left ≫ (toUnit D.P.A ≫ η[D.P.A]).left
    rw [← Over.comp_left]; congr 1; simp
end ReciprocityTheory.ChartRestriction.G.DVR.GC
