-- Prove2me | solution 1 for P2M_GlobalTheory_UU_BiLift_exists_defect__8566bdf03e89
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:06:49.806679+00:00
-- url     : https://prove2.me/submissions/b3b80787-066d-4885-a58b-2edfe4b1d9b9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGenLiftOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsPullLam
import Theorems.Thm_GlobalTheory_UU_BiLift_exists_pull_lam
import Theorems.Thm_GlobalTheory_UU_BiLift_exists_defect
import Theorems.Thm_GlobalTheory_UU_BiLift_formEq_symm
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply



set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.BiLift
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)
variable {H Y : Over S} [GrpObj H] {i : H ⟶ G} [IsMonHom i] {x : Y ⟶ G}
omit [IsMonHom i] [GrpObj H]
namespace GlobalTheory.UU.BiLift
theorem _root_.solution (s : LB.Gen (LB.LinComb L.L (lam (fst H G ≫ i) (snd H G)) Oε)) (hs : s.IsGen) :
    ∃ f : Γ((H ⊗ G ⊗ G).left, ⊤)ˣ, ∀ (Z : Over S) (t : Z ⟶ H) (y : Z ⟶ G ⊗ G) (z : Z.left) (J), Good L.L z J →
      val s (lift t (y ≫ fst _ _ * y ≫ snd _ _)).left z J = gm (lift t y).left z ⊤ f *
        (cubV c z J (t ≫ i) (y ≫ fst _ _) (y ≫ snd _ _) * val s (lift t (y ≫ fst _ _)).left z J *
          val s (lift t (y ≫ snd _ _)).left z J) := by
  let p : H ⊗ G ⊗ G ⟶ H := fst _ _
  let q : H ⊗ G ⊗ G ⟶ G := snd _ _ ≫ fst _ _
  let q' : H ⊗ G ⊗ G ⟶ G := snd _ _ ≫ snd _ _
  obtain ⟨s₁, g₁, e₁⟩ := exists_pull_lam (lift p (q * q')) (lift_fst_assoc _ _ _) (lift_snd _ _) s hs
  obtain ⟨s₂, g₂, e₂⟩ := exists_pull_lam (lift p q) (lift_fst_assoc _ _ _) (lift_snd _ _) s hs
  obtain ⟨s₃, g₃, e₃⟩ := exists_pull_lam (lift p q') (lift_fst_assoc _ _ _) (lift_snd _ _) s hs
  obtain ⟨f, hf⟩ := exists_defect c _ _ _ (formEq_symm _ _) (formEq_symm _ _) (formEq_symm _ _) s₁ s₂ s₃ g₁ g₂ g₃
  refine ⟨f, fun Z t y z J hJ => ?_⟩
  have e := hf Z (lift t y) z J hJ
  rw [e₁ _ _ z J hJ, e₂ _ _ z J hJ, e₃ _ _ z J hJ, (isCub_cubV c hJ).s12, (isCub_cubV c hJ).s01] at e
  simpa only [← Over.comp_left, comp_lift, MonObj.comp_mul, p, q, q', lift_fst, lift_snd, lift_fst_assoc,
    lift_snd_assoc, Category.assoc] using e
end GlobalTheory.UU.BiLift
