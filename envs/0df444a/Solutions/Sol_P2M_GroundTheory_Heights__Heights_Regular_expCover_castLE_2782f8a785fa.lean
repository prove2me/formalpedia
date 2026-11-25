-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_expCover_castLE_2782f8a785fa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:49:56.140812+00:00
-- url     : https://prove2.me/submissions/5109153d-650d-417c-b045-1bae2d155d17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PosSemidefOfIntQuadNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Matrix Topology Filter
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution {n a : ℕ} (h : a ≤ n) (w : Fin n → ℂ) (i : Fin a) :
    expCover a w (Fin.castLE h i) = Complex.exp (w (Fin.castLE h i)) := by
  simp [expCover, i.isLt]
end GroundTheory.Heights₂.Heights.Regular
