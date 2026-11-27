-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LeadMinorBasic_proof_ac6ce8f9f4df
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:04:12.992995+00:00
-- url     : https://prove2.me/submissions/712d2bc0-9623-45e1-9725-91e448e45b9c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PLeadMinorBasic

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
namespace LeadMinorBasic
theorem _root_.solution : LeadMinorBasic.Statement := by
  intro d S
  refine ⟨?_, ?_, ?_⟩
  · simp [leadMinor]
  · unfold leadMinor
    congr 1
    ext a b
    simp only [Matrix.of_apply]
    rw [dif_pos ⟨a.2, b.2⟩]
  · intro hS i hi
    have e : (Matrix.of fun a b : Fin i =>
        if h : (a : ℕ) < d ∧ (b : ℕ) < d then S ⟨a, h.1⟩ ⟨b, h.2⟩ else 0) =
        S.submatrix (Fin.castLE hi) (Fin.castLE hi) := by
      ext a b
      simp only [Matrix.of_apply, Matrix.submatrix_apply]
      rw [dif_pos ⟨a.2.trans_le hi, b.2.trans_le hi⟩]
      rfl
    unfold leadMinor
    rw [e]
    exact (hS.submatrix (Fin.castLE_injective hi)).det_pos
end LeadMinorBasic
end GroundTheory.Heights₂.Heights
