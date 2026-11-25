-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CuspCovolume_inv_diag_le_of_ge_d220717e0ddd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:45.498246+00:00
-- url     : https://prove2.me/submissions/ccb0c510-7b1f-49a3-8697-d9eb794cf53a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PCuspCovolume
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCCusp_inv_diag_le_31afacab59f5


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
open GroundTheory.Heights₂.Heights.CuspCovolume
namespace GroundTheory.Heights₂.Heights.CuspCovolume
theorem _root_.solution {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} (hY : Y.PosDef) {c : ℝ}
    (hc : 0 < c) (h : ∀ x : Fin g → ℝ, c * ∑ k, x k ^ 2 ≤ MCSchur.qf Y x) (k : Fin g) :
    Y⁻¹ k k ≤ 1 / c := by
  refine MCCusp.inv_diag_le hY k hc fun x => ?_
  have hs : x k ^ 2 ≤ ∑ j, x j ^ 2 :=
    Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg (x j)) (Finset.mem_univ k)
  have := h x
  nlinarith
end GroundTheory.Heights₂.Heights.CuspCovolume
