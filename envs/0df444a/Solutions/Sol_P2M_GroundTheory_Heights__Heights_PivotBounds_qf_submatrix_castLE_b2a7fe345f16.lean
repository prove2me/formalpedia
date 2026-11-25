-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PivotBounds_qf_submatrix_castLE_b2a7fe345f16
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:46:29.678553+00:00
-- url     : https://prove2.me/submissions/68c0fe83-cdcf-4a28-9d27-858dfd5aabfa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PPivotBounds

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
open GroundTheory.Heights₂.Heights.PivotBounds
namespace GroundTheory.Heights₂.Heights.PivotBounds
theorem _root_.solution {d m : ℕ} (h : m ≤ d) (S : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin m → ℝ) :
    MCSchur.qf (S.submatrix (Fin.castLE h) (Fin.castLE h)) x =
      MCSchur.qf S (Function.extend (Fin.castLE h) x 0) := by
  have hinj : Function.Injective (Fin.castLE h) := Fin.castLE_injective h
  set y := Function.extend (Fin.castLE h) x 0 with hy
  have hyc : ∀ a, y (Fin.castLE h a) = x a := fun a => hinj.extend_apply x 0 a
  have hy0 : ∀ b ∉ Set.range (Fin.castLE h), y b = 0 := by
    intro b hb
    rw [hy, Function.extend_apply' _ _ _ (by rintro ⟨a, rfl⟩; exact hb ⟨a, rfl⟩)]
    rfl
  unfold MCSchur.qf
  simp only [dotProduct, mulVec]
  refine Fintype.sum_of_injective _ hinj _ _ (fun b hb => by rw [hy0 b hb, zero_mul]) ?_
  intro a
  rw [hyc]
  congr 1
  refine Fintype.sum_of_injective _ hinj _ _ (fun b hb => by rw [hy0 b hb, mul_zero]) ?_
  intro b
  rw [hyc]
  rfl
end GroundTheory.Heights₂.Heights.PivotBounds
