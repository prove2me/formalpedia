-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CuspCoordinateBound_coord_sq_le_6e27dd9a7003
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:44.855068+00:00
-- url     : https://prove2.me/submissions/65d65fc3-7ce6-472c-898f-c9df12c14866

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PCuspCoordinateBound

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
open GroundTheory.Heights₂.Heights.CuspCoordinateBound
namespace GroundTheory.Heights₂.Heights.CuspCoordinateBound
theorem _root_.solution {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (c : ℝ) (hc : 0 < c)
    (hY : ∀ x : Fin g → ℝ, c * ∑ l, x l ^ 2 ≤ MCSchur.qf Y x) (β : Fin g → ℝ) (k : Fin g) :
    c * β k ^ 2 ≤ MCSchur.qf Y β := by
  have h1 : β k ^ 2 ≤ ∑ l, β l ^ 2 :=
    Finset.single_le_sum (f := fun l => β l ^ 2) (fun l _ => sq_nonneg _) (Finset.mem_univ k)
  nlinarith [hY β]
end GroundTheory.Heights₂.Heights.CuspCoordinateBound
