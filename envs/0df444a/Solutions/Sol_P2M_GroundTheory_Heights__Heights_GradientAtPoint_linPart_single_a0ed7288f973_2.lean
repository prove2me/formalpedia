-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_GradientAtPoint_linPart_single_a0ed7288f973
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:56:04.901964+00:00
-- url     : https://prove2.me/submissions/d4e8b3c8-3438-4f8e-88ff-2d9d696de0b7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GradientAtPoint

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.GradientAtPoint
variable {σ : Type*} (w : σ → ℂ)
namespace GroundTheory.Heights₂.Heights.GradientAtPoint
theorem _root_.solution [Fintype σ] [DecidableEq σ] (j : σ) : linPart w (Pi.single j 1) = X j - C (w j) := by
  rw [linPart, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · simp
end GroundTheory.Heights₂.Heights.GradientAtPoint
