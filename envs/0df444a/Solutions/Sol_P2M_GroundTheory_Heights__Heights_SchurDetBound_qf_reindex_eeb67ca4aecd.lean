-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SchurDetBound_qf_reindex_eeb67ca4aecd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:14:57.773828+00:00
-- url     : https://prove2.me/submissions/5a3e9150-5716-4e5f-a906-91963334016e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PSchurDetBound

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
open GroundTheory.Heights₂.Heights.SchurDetBound
namespace GroundTheory.Heights₂.Heights.SchurDetBound
theorem _root_.solution {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (G : Matrix ι ι ℝ)
    (w : κ → ℝ) : MCSchur.qf G (w ∘ e) = MCSchur.qf (reindex e e G) w := by
  simp only [MCSchur.qf, dotProduct, mulVec, reindex_apply, submatrix_apply, Function.comp_apply]
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← e.sum_comp]
  simp
end GroundTheory.Heights₂.Heights.SchurDetBound
