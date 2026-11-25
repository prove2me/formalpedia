-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CuspLeadingMinima_single_linearIndependent_7ac4c2702ca9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:52.204611+00:00
-- url     : https://prove2.me/submissions/644dff05-efcd-48ff-8a8e-2a8d009cbe1f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PCuspLeadingMinima

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
open GroundTheory.Heights₂.Heights.CuspLeadingMinima
namespace GroundTheory.Heights₂.Heights.CuspLeadingMinima
theorem _root_.solution {g r : ℕ} (h : r ≤ g) :
    LinearIndependent ℤ (fun j : Fin r => (Pi.single (Fin.castLE h j) (1 : ℂ) : Fin g → ℂ)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have := congrFun hc (Fin.castLE h i)
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, Pi.single_apply,
    (Fin.castLE_injective h).eq_iff] at this
  simpa using this
end GroundTheory.Heights₂.Heights.CuspLeadingMinima
