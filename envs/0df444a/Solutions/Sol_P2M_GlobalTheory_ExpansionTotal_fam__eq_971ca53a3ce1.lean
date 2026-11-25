-- Prove2me | solution 1 for P2M_GlobalTheory_ExpansionTotal_fam__eq_971ca53a3ce1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:31:51.880502+00:00
-- url     : https://prove2.me/submissions/e84a9711-02b4-47f3-9ca5-4a4e4b25a878

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_OneTmulNeZeroOfDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsNoetherianModelOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoAppTopOfIsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecLinOfSecScal
import Theorems.Thm_GlobalTheory_ExpansionTotal_toBK_prB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP


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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ExpansionTotal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange
variable {R : Type} [CommRing R] [IsDomain R] {F F' : Type} [Field F] [Algebra (FractionRing R) F]
  [Field F'] [Algebra (FractionRing R) F'] (θ : TF (R := R) F ⟶ TF (R := R) F') (D : DegPre R)
namespace GlobalTheory.ExpansionTotal
theorem _root_.solution (α : D.X) (i : Fin 4) :
    DegPre.famφ D F α i = (toBK θ D).left ≫ DegPre.famφ D F' α i := by
  have e₀ := toBK_prB θ D
  have e₂ := comp_cP D (toBK θ D) α
  fin_cases i
  · exact congrArg (fun q => q.left) e₀.symm
  · exact congrArg (fun q => q.left) ((MonObj.comp_mul (toBK θ D) (DegPre.prB D _) (cP D _ α)).trans
      (congrArg₂ (· * ·) e₀ e₂)).symm
  · exact congrArg (fun q => q.left) e₂.symm
  · exact congrArg (fun q : DegPre.BF D F ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (toBK θ D)).symm
end GlobalTheory.ExpansionTotal
