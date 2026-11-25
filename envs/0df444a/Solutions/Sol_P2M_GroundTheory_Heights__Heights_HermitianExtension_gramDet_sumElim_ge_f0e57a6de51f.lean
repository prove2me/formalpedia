-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermitianExtension_gramDet_sumElim_ge_f0e57a6de51f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:42:27.717959+00:00
-- url     : https://prove2.me/submissions/b91a5ab5-9c35-4486-874c-8673e3eeaac5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_LinearIndependentSumElimOfExact
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_lTensor_complex_smul_450d1267bf4b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_re_det_gram_sumElim_ge_6194b3aa88ab


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
open scoped ComplexOrder
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Heights₂.Heights.HermitianExtension
variable {E' E E'' : HermitianBundle K} (X : HermitianExtension E' E E'')
namespace GroundTheory.Heights₂.Heights.HermitianExtension
theorem _root_.solution (σ : K →+* ℂ) {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (s' : m → E'.carrier) (u : n → E.carrier) :
    gramDet E'.metric σ s' * gramDet E''.metric σ (fun j ↦ X.proj (u j)) ≤
      gramDet E.metric σ (Sum.elim (fun k ↦ X.incl (s' k)) u) := by
  let L : FibreSpace E'.metric σ →ₗ[ℂ] FibreSpace E.metric σ :=
    { toFun := fun x ↦ X.incl.lTensor (ComplexAt σ) x
      map_add' := map_add _
      map_smul' := lTensor_complex_smul σ X.incl }
  let W := LinearMap.range L
  have : FiniteDimensional ℂ W := inferInstance
  have : CompleteSpace W := FiniteDimensional.complete ℂ W
  let a : m → FibreSpace E.metric σ := fun k ↦ fibreVec E.metric σ (X.incl (s' k))
  let b : n → FibreSpace E.metric σ := fun j ↦ fibreVec E.metric σ (u j)
  have ha : ∀ k, a k ∈ W := fun k ↦ ⟨fibreVec E'.metric σ (s' k), by
    change X.incl.lTensor (ComplexAt σ) ((1 : ComplexAt σ) ⊗ₜ s' k) = _
    rw [LinearMap.lTensor_tmul]
    rfl⟩
  have key := re_det_gram_sumElim_ge W a ha b
  have hga : gram ℂ a = gram ℂ (fun k ↦ fibreVec E'.metric σ (s' k)) := by
    ext i k
    exact X.incl_isometric σ (1 ⊗ₜ s' i) (1 ⊗ₜ s' k)
  let P : FibreSpace E.metric σ →ₗ[ℂ] FibreSpace E''.metric σ :=
    { toFun := fun x ↦ X.proj.lTensor (ComplexAt σ) x
      map_add' := map_add _
      map_smul' := lTensor_complex_smul σ X.proj }
  have hcomp : ∀ y : Fibre σ E'.carrier,
      X.proj.lTensor (ComplexAt σ) (X.incl.lTensor (ComplexAt σ) y) = 0 := by
    intro y
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, X.exact.linearMap_comp_eq_zero,
      LinearMap.lTensor_zero, LinearMap.zero_apply]
  have hPL : ∀ y, P (L y) = 0 := fun y ↦ hcomp y
  have hQ : ∀ j, P (Wᗮ.starProjection (b j)) = fibreVec E''.metric σ (X.proj (u j)) := by
    intro j
    rw [Submodule.starProjection_orthogonal_val, map_sub]
    obtain ⟨y, hy⟩ := W.starProjection_apply_mem (b j)
    rw [← hy, hPL, sub_zero]
    change X.proj.lTensor (ComplexAt σ) ((1 : ComplexAt σ) ⊗ₜ u j) = _
    rw [LinearMap.lTensor_tmul]
    rfl
  have hperp : ∀ j (w : Fibre σ E'.carrier),
      (E.metric.form σ).inner (X.incl.lTensor (ComplexAt σ) w) (Wᗮ.starProjection (b j)) = 0 :=
    fun j w ↦ Submodule.inner_right_of_mem_orthogonal (K := W) ⟨w, rfl⟩
      (Wᗮ.starProjection_apply_mem (b j))
  have hgq : gram ℂ (fun j ↦ Wᗮ.starProjection (b j)) =
      gram ℂ (fun j ↦ fibreVec E''.metric σ (X.proj (u j))) := by
    ext j k
    rw [gram_apply, gram_apply, ← hQ j, ← hQ k]
    exact (X.proj_coisometric σ _ _ (hperp j) (hperp k)).symm
  have hfam : (fun k ↦ fibreVec E.metric σ (Sum.elim (fun k ↦ X.incl (s' k)) u k)) =
      Sum.elim a b := by
    funext k
    rcases k with k | j <;> rfl
  simp only [gramDet]
  rw [hfam, ← hga, ← hgq]
  exact key
end GroundTheory.Heights₂.Heights.HermitianExtension
