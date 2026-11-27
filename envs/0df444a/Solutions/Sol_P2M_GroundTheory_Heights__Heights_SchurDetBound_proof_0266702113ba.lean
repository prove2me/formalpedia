-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SchurDetBound_proof_0266702113ba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:08:24.85158+00:00
-- url     : https://prove2.me/submissions/1ea51064-7cda-41ad-a34c-ef52bd3b541a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PSchurDetBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SchurDetBound_qf_reindex_eeb67ca4aecd

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
namespace SchurDetBound
theorem _root_.solution : SchurDetBound.Statement := by
  intro k G hsym hdet t ht
  set e : Fin (k + 1) ≃ Fin k ⊕ Fin 1 := finSumFinEquiv.symm with he
  set M := reindex e e G with hMdef
  set A := M.toBlocks₁₁ with hAdef
  set B := M.toBlocks₁₂ with hBdef
  set D := M.toBlocks₂₂ with hDdef
  have hA : A = G.submatrix Fin.castSucc Fin.castSucc := by
    ext i j
    simp [hAdef, hMdef, he, toBlocks₁₁, Fin.castSucc]
  have hAsymm : A.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    ext i j
    simp only [hAdef, hMdef, toBlocks₁₁, transpose_apply, of_apply, reindex_apply,
      submatrix_apply]
    exact congrFun (congrFun hsym _) _
  have hM : fromBlocks A B Bᴴ D = M := by
    rw [← fromBlocks_toBlocks M]
    congr 1
    rw [conjTranspose_eq_transpose_of_trivial]
    ext i j
    simp only [hBdef, hMdef, toBlocks₁₂, toBlocks₂₁, transpose_apply, of_apply, reindex_apply,
      submatrix_apply]
    exact congrFun (congrFun hsym _) _
  have hdetA : 0 < A.det := by rw [hA]; exact hdet
  have : Invertible A := invertibleOfIsUnitDet A hdetA.ne'.isUnit
  set S := D - Bᴴ * A⁻¹ * B with hSdef
  have hdetG : G.det = A.det * S 0 0 := by
    rw [← det_reindex_self e G, ← hMdef, ← hM, det_fromBlocks₁₁, invOf_eq_nonsing_inv,
      Matrix.det_unique (D - Bᴴ * A⁻¹ * B)]
    rfl

  set y : Fin 1 → ℝ := fun _ => 1 with hy
  set x : Fin k → ℝ := -((A⁻¹ * B) *ᵥ y) with hx
  have hval : MCSchur.qf G ((Sum.elim x y) ∘ e) = S 0 0 := by
    rw [SchurDetBound.qf_reindex, ← hMdef, ← hM]
    have h := schur_complement_eq₁₁ B D x y hAsymm
    simp only [star_trivial] at h
    simp only [MCSchur.qf, dotProduct_mulVec]
    rw [show (Sum.elim x y) = x ⊕ᵥ y from rfl, h, hx, neg_add_cancel]
    simp [hy, dotProduct, vecMul, hSdef]
  have hlast : ((Sum.elim x y) ∘ e) (Fin.last k) = 1 := by
    simp [he, hy]
  have hts := ht _ hlast
  rw [hval] at hts
  rw [hdetG, ← hA, mul_comm t]
  exact mul_le_mul_of_nonneg_left hts hdetA.le
end SchurDetBound
end GroundTheory.Heights₂.Heights
