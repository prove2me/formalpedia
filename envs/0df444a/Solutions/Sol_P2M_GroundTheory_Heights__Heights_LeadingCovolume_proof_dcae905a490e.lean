-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LeadingCovolume_proof_dcae905a490e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:02:34.185017+00:00
-- url     : https://prove2.me/submissions/d8c5d0d0-dd12-4c31-ac1d-fbc9a8f96da0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PLeadingCovolume
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LeadingCovolume_periodBasis_of_lt_3607769c3abd

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
namespace LeadingCovolume
theorem _root_.solution : LeadingCovolume.Statement := by
  intro g τ r h
  unfold covolume leadMinor
  congr 2
  ext a b
  have ha : (a : ℕ) < g + g := by omega
  have hb : (b : ℕ) < g + g := by omega
  rw [Matrix.of_apply, Matrix.of_apply, dif_pos ⟨ha, hb⟩, periodGram, Matrix.of_apply,
    LeadingCovolume.periodBasis_of_lt τ a (by omega) ha,
    LeadingCovolume.periodBasis_of_lt τ b (by omega) hb]
  rfl
end LeadingCovolume
end GroundTheory.Heights₂.Heights
