-- Prove2me | solution 1 for P2M_GlobalTheory_FamSpan_fam_B_comm_3ace86c881b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:30:30.559242+00:00
-- url     : https://prove2.me/submissions/6efbafa9-4081-424b-82b0-46efa2b7bc19

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsRepresentativesModNsmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsBasisOfEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FamEqOnClassOfEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTwistBasisOffPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFamOfIsPullDegStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IntegralFamilyPrescribedTermUnitAtPrimeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIntegralFamiliesSpanPullDegeneration
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FamSpan
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}
namespace GlobalTheory.FamSpan
theorem _root_.solution (hD : IsPullDeg φ D D') (x : D'.X) (κ : Fin 4) :
    D'.famφB x κ ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) =
      (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ≫ D.famφB (hD.xe x) κ := by
  have gp := pull_grp hD
  let U := pushPt gp.1.w (𝟙 D'.P.A)
  have hU : U.left = hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) := Category.id_comp _
  have hw : (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ≫ D.P.A.hom = D'.P.A.hom ≫ specOf φ := gp.1.w
  have h2 : (toUnit D'.P.A ≫ D'.c x).left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) =
      (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ≫ (toUnit D.P.A ≫ D.c (hD.xe x)).left := by
    show (D'.P.A.hom ≫ (D'.c x).left) ≫ _ = _ ≫ D.P.A.hom ≫ (D.c (hD.xe x)).left
    rw [Category.assoc, hD.c_pr, ← Category.assoc, ← hw, Category.assoc]
  fin_cases κ
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · have e := gp.2 D'.P.A (𝟙 _) (toUnit _ ≫ D'.c x) (U ≫ 𝟙 _) (U ≫ toUnit _ ≫ D.c (hD.xe x))
      (by rw [Category.comp_id]; rfl) (by rw [Over.comp_left, hU]; exact h2.symm)
    rw [← MonObj.comp_mul, Over.comp_left, hU] at e
    exact e.symm
  · exact h2
  · show (D'.P.A.hom ≫ eSec D'.P.A) ≫ _ = _ ≫ D.P.A.hom ≫ eSec D.P.A
    rw [Category.assoc, hD.he, ← Category.assoc, ← hw, Category.assoc]
end GlobalTheory.FamSpan
