-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CuspShortVectors_intVec_eq_d2880f61d088
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:54.600322+00:00
-- url     : https://prove2.me/submissions/db6e416a-5dad-4678-9b46-32a15926c771

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PCuspShortVectors

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
open GroundTheory.Heights₂.Heights.CuspShortVectors
namespace GroundTheory.Heights₂.Heights.CuspShortVectors
theorem _root_.solution {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a n : Fin g → ℤ) :
    intVecC a + τ *ᵥ intVecC n =
      (fun k => ((a k : ℝ) : ℂ)) + τ *ᵥ fun k => ((n k : ℝ) : ℂ) := by
  unfold intVecC
  simp
end GroundTheory.Heights₂.Heights.CuspShortVectors
