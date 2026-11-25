-- Prove2me | solution 1 for P2M_GlobalTheory___cechClass_89909f0dccc0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:10:04.68088+00:00
-- url     : https://prove2.me/submissions/2eef1f16-df64-47a3-ba64-6ad410e04165

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PresheafCubeExactAtSuccOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsAddEquivOfSurjectiveOfKerIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CechModulesFunctorShortExactOfAcyclic
import Theorems.Thm_GlobalTheory_Cube_SemiHom_homology_cechClass
import Theorems.Thm_GlobalTheory_SheafLES_map_id
import Theorems.Thm_GlobalTheory_SheafLES_map_zero_hom
import Theorems.Thm_GlobalTheory_SheafLES_res_id
import Theorems.Thm_GlobalTheory_SheafLES_toAbSheaf_map_hom
import Theorems.Thm_GlobalTheory_SheafLES_toAbSheaf_obj_obj
import Theorems.Thm_GlobalTheory_cechAbAug_apply
import Theorems.Thm_GlobalTheory_cechAbCubeMap_app_apply
import Theorems.Thm_GlobalTheory_cechAbHMap_id
import Theorems.Thm_GlobalTheory_cechAbHZeroEquiv_symm_apply
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
import Theorems.Thm_GlobalTheory_presheafCechHZeroEquiv_symm_apply
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
import Theorems.Thm_P2M_GlobalTheory_SheafLES___apply_7b49c5df3cf6
import Theorems.Thm_P2M_GlobalTheory_SheafLES___map_026ec4bafb10
import Theorems.Thm_P2M_GlobalTheory_SheafLES_map___ee3a67e9aebf
import Theorems.Thm_P2M_GlobalTheory_cohOn___map_6ba3242e7e5e
import Theorems.Thm_P2M_GlobalTheory_cohOn_map___8dd9b9fe2c60
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Cube.SemiHom.homology_cechClass
attribute [local simp] GlobalTheory.SheafLES.map_id
attribute [local simp] GlobalTheory.SheafLES.map_zero_hom
attribute [local simp] GlobalTheory.SheafLES.res_id
attribute [local simp] GlobalTheory.SheafLES.toAbSheaf_map_hom
attribute [local simp] GlobalTheory.SheafLES.toAbSheaf_obj_obj
attribute [local simp] GlobalTheory.cechAbAug_apply
attribute [local simp] GlobalTheory.cechAbCubeMap_app_apply
attribute [local simp] GlobalTheory.cechAbHMap_id
attribute [local simp] GlobalTheory.cechAbHZeroEquiv_symm_apply
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id
attribute [local simp] GlobalTheory.presheafCechHZeroEquiv_symm_apply
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply
attribute [local simp] P2M_GlobalTheory_SheafLES___map_026ec4bafb10
attribute [local simp] P2M_GlobalTheory_SheafLES_map___ee3a67e9aebf
attribute [local simp] P2M_GlobalTheory_cohOn___map_6ba3242e7e5e
attribute [local simp] P2M_GlobalTheory_cohOn_map___8dd9b9fe2c60



set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
universe v u
noncomputable section
open GlobalTheory
variable {ι : Type} [LinearOrder ι] {R : Type v} [Ring R]
namespace GlobalTheory
theorem _root_.solution {S : ShortComplex (Cube.{u} ι R)}
    (hS : (S.map (cechFunctor ι R)).ShortExact) (p : ℕ)
    (x₃ : LinearMap.ker (Cube.d S.X₃ (p + 1))) (x₂ : Cube.Term S.X₂ (p + 1))
    (x₁ : LinearMap.ker (Cube.d S.X₁ (p + 1 + 1)))
    (h₂ : Cube.termMap S.g (p + 1) x₂ = x₃.1)
    (h₁ : Cube.termMap S.f (p + 1 + 1) x₁.1 = Cube.d S.X₂ (p + 1) x₂) :
    (hS.δ p (p + 1) rfl).hom (cechClass S.X₃ p x₃) = cechClass S.X₁ (p + 1) x₁ := by
  have hx₃ : (forget₂ (ModuleCat.{u} R) Ab).map ((S.map (cechFunctor ι R)).X₃.d p (p + 1)) x₃.1
      = 0 := by
    change ((cechComplex S.X₃).d p (p + 1)).hom x₃.1 = 0
    rw [cechComplex_d]
    exact x₃.2
  have hx₁ : (forget₂ (ModuleCat.{u} R) Ab).map ((S.map (cechFunctor ι R)).f.f (p + 1)) x₁.1 =
      (forget₂ (ModuleCat.{u} R) Ab).map ((S.map (cechFunctor ι R)).X₂.d p (p + 1)) x₂ := by
    change _ = ((cechComplex S.X₂).d p (p + 1)).hom x₂
    rw [cechComplex_d]
    exact h₁
  have key := hS.δ_apply p (p + 1) rfl x₃.1 hx₃ x₂ h₂ x₁.1 hx₁ (p + 1 + 1) (by simp)
  have aux (A : Cube.{u} ι R) (q j : ℕ) (x : LinearMap.ker (Cube.d A (q + 1)))
      (hj : (ComplexShape.up ℕ).next q = j)
      (hx : (forget₂ (ModuleCat.{u} R) Ab).map ((cechComplex A).d q j) x.1 = 0) :
      (forget₂ (ModuleCat.{u} R) Ab).map ((cechComplex A).homologyπ q)
        ((cechComplex A).cyclesMk x.1 j hj hx) = cechClass A q x := by
    refine congrArg ((cechComplex A).homologyπ q).hom
      (?_ : _ = (cechCyclesIso A q).inv.hom x)
    apply (ModuleCat.mono_iff_injective ((cechComplex A).iCycles q)).1 inferInstance
    exact ((cechComplex A).i_cyclesMk x.1 j hj hx).trans (iCycles_cechCyclesIso_inv A q x).symm
  exact (congrArg (hS.δ p (p + 1) rfl).hom (aux S.X₃ p _ x₃ _ _).symm).trans
    (key.trans (aux S.X₁ (p + 1) _ x₁ _ _))
end GlobalTheory
