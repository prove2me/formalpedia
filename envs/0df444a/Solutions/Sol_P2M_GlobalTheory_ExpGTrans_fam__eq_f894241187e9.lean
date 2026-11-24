-- Prove2me | solution 1 for P2M_GlobalTheory_ExpGTrans_fam__eq_f894241187e9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:05.187255+00:00
-- url     : https://prove2.me/submissions/3a5f2b3e-e88f-4eae-bfe0-147d04cd3d8a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsGTransport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.ExpGTrans
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ExpTrans
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
  {D : DegPre R} {D' : DegPre R'}
namespace GlobalTheory.ExpGTrans
theorem _root_.solution (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (α : D.X) (κ : Fin 4) :
    DegPre.famφ D F α κ = (DegPre.prB D F).left ≫ D.famφB α κ := by
  unfold DegPre.famφ DegPre.famφB
  fin_cases κ <;> dsimp
  · simp
  · show _ = (D.prB F).left ≫ _
    rw [← Over.comp_left]
    congr 1
    unfold padd
    rw [CartesianMonoidalCategory.comp_lift_assoc, Category.comp_id, CartesianMonoidalCategory.comp_toUnit_assoc]
  · rw [pullback.condition, Category.assoc]
  · rw [pullback.condition, Category.assoc]
end GlobalTheory.ExpGTrans
