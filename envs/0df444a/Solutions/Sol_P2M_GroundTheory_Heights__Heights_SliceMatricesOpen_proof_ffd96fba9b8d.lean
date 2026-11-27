-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceMatricesOpen_proof_ffd96fba9b8d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:09:12.894836+00:00
-- url     : https://prove2.me/submissions/e77dfc77-f838-4dd4-8133-09593a5f0d20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceMatricesOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGeneralProjection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceMatricesOpen
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sliceDeriv_apply_5c592b69efa7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_hasFDerivAt_slice_52338e47dd3d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_bijective_iff_det_ne_zero_9bac468e1b7a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GeneralProjection_proof_adead3c1f483


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
open Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace SliceMatricesOpen
theorem _root_.solution : SliceMatricesOpen.Statement := by
  intro n k m γ s hd hinj
  have hfd : ∀ (L : Matrix (Fin k) (Fin n) ℂ) b,
      fderiv ℂ (fun t => vecCons (t 0) (L *ᵥ γ b t)) (s b) = sliceDeriv L (fderiv ℂ (γ b) (s b)) :=
    fun L b => (hasFDerivAt_slice (hd b) L).fderiv
  constructor
  · have hset : {L : Matrix (Fin k) (Fin n) ℂ |
        ∀ b, Function.Bijective (fderiv ℂ (fun t => vecCons (t 0) (L *ᵥ γ b t)) (s b))} =
        ⋂ b, {L | LinearMap.det
          (sliceDeriv L (fderiv ℂ (γ b) (s b)) : (Fin (k + 1) → ℂ) →ₗ[ℂ] (Fin (k + 1) → ℂ)) ≠ 0} := by
      ext L
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, hfd, bijective_iff_det_ne_zero]
    rw [hset]
    refine isOpen_iInter_of_finite fun b => isOpen_ne_fun ?_ continuous_const
    simp_rw [← LinearMap.det_toMatrix']
    refine Continuous.matrix_det (continuous_matrix fun i j => ?_)
    simp only [LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe, sliceDeriv_apply]
    refine Fin.cases ?_ (fun r => ?_) i
    · simp only [Matrix.cons_val_zero]
      exact continuous_const
    · simp only [Matrix.cons_val_succ]
      exact (continuous_apply r).comp (continuous_id.matrix_mulVec continuous_const)
  · set Lb : Fin m → (Fin k → ℂ) →ₗ[ℂ] (Fin n → ℂ) := fun b =>
      (fderiv ℂ (γ b) (s b) : (Fin (k + 1) → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ
        ((Fin.consEquivL ℂ (fun _ : Fin (k + 1) => ℂ)).toLinearEquiv.toLinearMap ∘ₗ
          LinearMap.inr ℂ ℂ (Fin k → ℂ)) with hLbdef
    have hLapp : ∀ b w, Lb b w = fderiv ℂ (γ b) (s b) (Fin.cons 0 w) := fun b w => rfl
    have hL : ∀ b, Function.Injective (Lb b) := by
      intro b
      refine (injective_iff_map_eq_zero (Lb b)).2 fun w hw => ?_
      rw [hLapp] at hw
      have h0 := hinj b (Fin.cons 0 w) (by simp) hw
      funext i
      simpa using congrFun h0 i.succ
    obtain ⟨π, hπ⟩ := IndefiniteRowSideFullHecke.ComplexSets.GeneralProjection.proof n k m Lb hL
    refine ⟨π, fun b => ?_⟩
    rw [hfd]
    have hΦ : Function.Injective (sliceDeriv π (fderiv ℂ (γ b) (s b))) := by
      refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
      rw [sliceDeriv_apply] at hv
      have hv0 : v 0 = 0 := by simpa using congrFun hv 0
      have hvc : v = Fin.cons 0 (Fin.tail v) := by rw [← hv0, Fin.cons_self_tail]
      have hw : π *ᵥ Lb b (Fin.tail v) = π *ᵥ Lb b 0 := by
        rw [map_zero, Matrix.mulVec_zero, hLapp, ← hvc]
        funext r
        simpa using congrFun hv r.succ
      rw [hvc, hπ b hw]
      funext i
      exact Fin.cases rfl (fun j => rfl) i
    exact ⟨hΦ, (LinearMap.injective_iff_surjective
      (f := (sliceDeriv π (fderiv ℂ (γ b) (s b)) : (Fin (k + 1) → ℂ) →ₗ[ℂ] _))).1 hΦ⟩
end SliceMatricesOpen
end GroundTheory.Heights₂.Heights
