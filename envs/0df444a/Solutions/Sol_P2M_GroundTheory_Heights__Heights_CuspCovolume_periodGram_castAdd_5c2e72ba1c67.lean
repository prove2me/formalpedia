-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CuspCovolume_periodGram_castAdd_5c2e72ba1c67
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:48.473697+00:00
-- url     : https://prove2.me/submissions/a6a79bb1-d081-4409-aa6d-ca39ece7bbb7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PCuspCovolume
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCSchur_hermValue_eq_qf_16537984ce33


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
theorem _root_.solution {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (k : Fin g) :
    periodGram τ (Fin.castAdd g k) (Fin.castAdd g k) = (τ.map Complex.im)⁻¹ k k := by
  simp only [periodGram, of_apply, periodBasis, Fin.append_left]
  rw [show hermPair (τ.map Complex.im)⁻¹ (Pi.single k 1) (Pi.single k 1) =
      hermValue (τ.map Complex.im)⁻¹ (Pi.single k 1) from rfl, MCSchur.hermValue_eq_qf]
  have h1 : (fun j => ((Pi.single k (1 : ℂ) : Fin g → ℂ) j).re) = Pi.single k (1 : ℝ) := by
    ext j
    by_cases h : j = k
    · subst h; simp
    · simp [h]
  have h2 : (fun j => ((Pi.single k (1 : ℂ) : Fin g → ℂ) j).im) = 0 := by
    ext j
    by_cases h : j = k
    · subst h; simp
    · simp [h]
  rw [h1, h2]
  simp [MCSchur.qf, mulVec_single]
end GroundTheory.Heights₂.Heights.CuspCovolume
