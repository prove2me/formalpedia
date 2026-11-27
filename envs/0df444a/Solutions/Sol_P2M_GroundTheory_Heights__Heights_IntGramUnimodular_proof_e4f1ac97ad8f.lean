-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IntGramUnimodular_proof_e4f1ac97ad8f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:01:43.050226+00:00
-- url     : https://prove2.me/submissions/4e3c7b40-d0b2-4cd0-8db3-29d3bf1778f9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PIntGramUnimodular

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
namespace IntGramUnimodular
theorem _root_.solution : IntGramUnimodular.Statement := by
  intro d k S N U hU
  have hmap : (N * U).map (Int.cast : ℤ → ℝ) =
      N.map (Int.cast : ℤ → ℝ) * U.map (Int.cast : ℤ → ℝ) :=
    Matrix.map_mul (f := Int.castRingHom ℝ)
  have hdet : (U.map (Int.cast : ℤ → ℝ)).det = ((U.det : ℤ) : ℝ) :=
    ((Int.castRingHom ℝ).map_det U).symm
  have hsq : ((U.det : ℤ) : ℝ) * (U.det : ℝ) = 1 := by
    rcases Int.isUnit_iff.mp hU with h | h <;> rw [h] <;> norm_num
  unfold intGram
  rw [hmap, transpose_mul]
  have e : (U.map (Int.cast : ℤ → ℝ))ᵀ * (N.map (Int.cast : ℤ → ℝ))ᵀ * S *
      (N.map (Int.cast : ℤ → ℝ) * U.map (Int.cast : ℤ → ℝ)) =
      (U.map (Int.cast : ℤ → ℝ))ᵀ * ((N.map (Int.cast : ℤ → ℝ))ᵀ * S * N.map (Int.cast : ℤ → ℝ)) *
        U.map (Int.cast : ℤ → ℝ) := by
    simp only [Matrix.mul_assoc]
  rw [e, det_mul, det_mul, det_transpose, hdet]
  calc (U.det : ℝ) * ((N.map (Int.cast : ℤ → ℝ))ᵀ * S * N.map (Int.cast : ℤ → ℝ)).det * (U.det : ℝ)
      = ((U.det : ℤ) : ℝ) * (U.det : ℝ) *
          ((N.map (Int.cast : ℤ → ℝ))ᵀ * S * N.map (Int.cast : ℤ → ℝ)).det := by ring
    _ = _ := by rw [hsq, one_mul]
end IntGramUnimodular
end GroundTheory.Heights₂.Heights
