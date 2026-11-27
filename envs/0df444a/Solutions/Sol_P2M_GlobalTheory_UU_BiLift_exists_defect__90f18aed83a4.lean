-- Prove2me | solution 1 for P2M_GlobalTheory_UU_BiLift_exists_defect__90f18aed83a4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:53:29.139534+00:00
-- url     : https://prove2.me/submissions/bf8ad9ff-dfa5-4c5d-91f4-94a667c535b3

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
import Theorems.Thm_GlobalTheory_UU_BiLift_formEq_refl
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
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
namespace GlobalTheory.UU.BiLift
theorem _root_.solution (s : LB.Gen (LB.LinComb L.L (lam (fst H Y ≫ i) (snd H Y ≫ x)) Oε)) (hs : s.IsGen) :
    ∃ f : Γ((H ⊗ H ⊗ Y).left, ⊤)ˣ, ∀ (Z : Over S) (t t' : Z ⟶ H) (y : Z ⟶ Y) (z : Z.left) (J), Good L.L z J →
      val s (lift (t * t') y).left z J = gm (lift t (lift t' y)).left z ⊤ f *
        (cubV c z J (t ≫ i) (t' ≫ i) (y ≫ x) * val s (lift t y).left z J * val s (lift t' y).left z J) := by
  let p : H ⊗ H ⊗ Y ⟶ H := fst _ _
  let p' : H ⊗ H ⊗ Y ⟶ H := snd _ _ ≫ fst _ _
  let q : H ⊗ H ⊗ Y ⟶ Y := snd _ _ ≫ snd _ _
  obtain ⟨s₁, g₁, e₁⟩ := exists_pull_lam (lift (p * p') q) (a' := p ≫ i * p' ≫ i) (x' := q ≫ x)
    (by rw [lift_fst_assoc, MonObj.mul_comp]) (lift_snd_assoc _ _ _) s hs
  obtain ⟨s₂, g₂, e₂⟩ := exists_pull_lam (lift p q) (lift_fst_assoc _ _ _) (lift_snd_assoc _ _ _) s hs
  obtain ⟨s₃, g₃, e₃⟩ := exists_pull_lam (lift p' q) (lift_fst_assoc _ _ _) (lift_snd_assoc _ _ _) s hs
  obtain ⟨f, hf⟩ := exists_defect c _ _ _ (formEq_refl _) (formEq_refl _) (formEq_refl _) s₁ s₂ s₃ g₁ g₂ g₃
  refine ⟨f, fun Z t t' y z J hJ => ?_⟩
  have e := hf Z (lift t (lift t' y)) z J hJ
  rw [e₁ _ _ z J hJ, e₂ _ _ z J hJ, e₃ _ _ z J hJ] at e
  simpa only [← Over.comp_left, comp_lift, MonObj.comp_mul, p, p', q, lift_fst, lift_snd, lift_fst_assoc,
    lift_snd_assoc, Category.assoc] using e
end GlobalTheory.UU.BiLift
