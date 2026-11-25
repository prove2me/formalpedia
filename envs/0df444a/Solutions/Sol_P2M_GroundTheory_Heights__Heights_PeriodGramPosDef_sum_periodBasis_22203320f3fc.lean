-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PeriodGramPosDef_sum_periodBasis_22203320f3fc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:47:16.318807+00:00
-- url     : https://prove2.me/submissions/727653ee-9658-4281-9618-727492f39da4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PPeriodGramPosDef

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
open GroundTheory.Heights₂.Heights.PeriodGramPosDef
namespace GroundTheory.Heights₂.Heights.PeriodGramPosDef
theorem _root_.solution {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (x : Fin (g + g) → ℝ) :
    ∑ i, (x i : ℂ) • periodBasis τ i =
      (fun k => (x (Fin.castAdd g k) : ℂ)) + τ *ᵥ fun k => (x (Fin.natAdd g k) : ℂ) := by
  rw [Fin.sum_univ_add]
  simp only [periodBasis, Fin.append_left, Fin.append_right, ← mulVec_smul, ← mulVec_sum]
  congr 1
  · funext l
    simp [Finset.sum_apply, Pi.single_apply]
  · congr 1
    funext l
    simp [Finset.sum_apply, Pi.single_apply]
end GroundTheory.Heights₂.Heights.PeriodGramPosDef
