-- Prove2me | solution 1 for P2M_GlobalTheory_ExpGTrans_fam_B_pull_88ae84d64707
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:35:35.057824+00:00
-- url     : https://prove2.me/submissions/ac94879e-db99-440c-bccf-a817b194ba34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsGTransport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
theorem _root_.solution (hD : IsPullDeg φ D D') (x : D'.X) (κ : Fin 4) :
    D'.famφB x κ ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) =
      (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ≫ D.famφB (hD.xe x) κ := by
  obtain ⟨G1, G2⟩ := pull_grp hD
  have he := hD.he
  unfold eSec at he
  have k2 : (toUnit D'.P.A ≫ D'.c x).left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) =
      (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ≫ (toUnit D.P.A ≫ D.c (hD.xe x)).left := by
    dsimp
    rw [← Category.assoc _ D.P.A.hom, G1.w, Category.assoc, Category.assoc, hD.c_pr x]
  have k3 : (toUnit D'.P.A ≫ η).left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) =
      (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ≫ (toUnit D.P.A ≫ η).left := by
    dsimp
    rw [← Category.assoc _ D.P.A.hom, G1.w, Category.assoc, Category.assoc, he]
  let x₀ : Over.mk (D'.P.A.hom ≫ spMap φ) ⟶ D.P.A :=
    Over.homMk (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) G1.w
  have h1 := G2 D'.P.A (𝟙 _) (toUnit _ ≫ D'.c x) x₀ (x₀ ≫ toUnit D.P.A ≫ D.c (hD.xe x))
    (Category.id_comp _).symm k2.symm
  have h2 : x₀ * (x₀ ≫ toUnit D.P.A ≫ D.c (hD.xe x)) =
      x₀ ≫ padd D.P.A (𝟙 _) (toUnit D.P.A ≫ D.c (hD.xe x)) := by
    unfold padd
    rw [Hom.mul_def, CartesianMonoidalCategory.comp_lift_assoc, Category.comp_id]
  have h3 : (𝟙 D'.P.A) * (toUnit _ ≫ D'.c x) = padd D'.P.A (𝟙 _) (toUnit _ ≫ D'.c x) := by
    unfold padd
    rw [Hom.mul_def]
  rw [h2, h3, Over.comp_left] at h1
  unfold DegPre.famφB
  fin_cases κ
  · simp
  · exact h1.symm
  · exact k2
  · exact k3
end GlobalTheory.ExpGTrans
