-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FrameJacobianSum_proof_e6c28fac6da2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:28:41.52373+00:00
-- url     : https://prove2.me/submissions/1fecaa2a-6dda-4ca9-bd9d-690b0b5ecab8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFrameJacobianSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFrameJacobianSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FrameJacobianSumAlt_areaJacobian_restrictScalars_31766ed81e91
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FrameJacobianSumAlt_det_adjoint_comp_cac87e9cc559
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CauchyBinet_proof_066722d63378


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
open Matrix Finset Module
noncomputable section
open FrameJacobianSumAlt
namespace GroundTheory.Heights₂.Heights
namespace FrameJacobianSum
theorem _root_.solution : FrameJacobianSum.Statement := by
  intro d n T b
  classical
  set e := EuclideanSpace.basisFun (Fin d) ℂ
  set N : Matrix (Fin n) (Fin d) ℂ := Matrix.of fun k j => inner ℂ (b k) (T (e j)) with hN
  have hI : ∀ (I : Finset (Fin n)) (h : I.card = d),
      areaJacobian ((frameProjLin b I ∘ₗ T).restrictScalars ℝ) = ‖(rowsOf N ⟨I, h⟩).det‖ ^ 2 := by
    intro I h
    rw [areaJacobian_restrictScalars, det_adjoint_comp]
    have hG : (Matrix.of fun i j : Fin d => inner ℂ ((frameProjLin b I ∘ₗ T) (e i))
        ((frameProjLin b I ∘ₗ T) (e j))) = (rowsOf N ⟨I, h⟩)ᴴ * rowsOf N ⟨I, h⟩ := by
      ext i j
      rw [Matrix.of_apply, PiLp.inner_apply, mul_apply, ← (I.orderIsoOfFin h).toEquiv.sum_comp]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp [rowsOf, hN, frameProjLin, conjTranspose_apply, e, RCLike.inner_apply, mul_comm]
    rw [hG, det_mul, det_conjTranspose, Complex.star_def, Complex.conj_mul', norm_pow,
      Complex.norm_real, norm_norm]
  have hT : LinearMap.det (LinearMap.adjoint T ∘ₗ T) =
      ∑ I : {I : Finset (Fin n) // I.card = d}, ((‖(rowsOf N I).det‖ ^ 2 : ℝ) : ℂ) := by
    rw [det_adjoint_comp]
    have hG : (Matrix.of fun i j : Fin d => inner ℂ (T (e i)) (T (e j))) = Nᴴ * N := by
      ext i j
      rw [Matrix.of_apply, ← b.sum_inner_mul_inner, mul_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [hN, conjTranspose_apply]
    rw [hG, CauchyBinet.proof]
    refine Finset.sum_congr rfl fun I _ => ?_
    have hc : colsOf Nᴴ I = (rowsOf N I)ᴴ := by
      ext i j
      simp [colsOf, rowsOf, conjTranspose_apply]
    rw [hc, det_conjTranspose, Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  rw [areaJacobian_restrictScalars, hT, ← Complex.ofReal_sum, Complex.norm_real,
    Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity),
    Finset.sum_subtype (univ.powersetCard d) (p := fun I : Finset (Fin n) => I.card = d)
      (fun I => by simp [mem_powersetCard])]
  exact Finset.sum_congr rfl fun I _ => (hI I.1 I.2).symm
end FrameJacobianSum
end GroundTheory.Heights₂.Heights
