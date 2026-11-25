-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LeadingCovolume_periodBasis_of_lt_3607769c3abd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:04:49.348559+00:00
-- url     : https://prove2.me/submissions/86c2d95a-885c-4bff-b46c-78c340a8ed90

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PLeadingCovolume

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
open GroundTheory.Heights₂.Heights.LeadingCovolume
namespace GroundTheory.Heights₂.Heights.LeadingCovolume
theorem _root_.solution {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (i : ℕ) (hi : i < g)
    (hi' : i < g + g) : periodBasis τ ⟨i, hi'⟩ = Pi.single (⟨i, hi⟩ : Fin g) 1 := by
  have e : (⟨i, hi'⟩ : Fin (g + g)) = Fin.castAdd g ⟨i, hi⟩ := rfl
  rw [e, periodBasis, Fin.append_left]
end GroundTheory.Heights₂.Heights.LeadingCovolume
