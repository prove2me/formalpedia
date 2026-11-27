-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GradientAtPoint_linPart_single_a0ed7288f973
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:19:16.008464+00:00
-- url     : https://prove2.me/submissions/7094e1a4-b6f3-4fbe-9eb9-308ec89badaa

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
theorem _root_.solution [Fintype σ] [DecidableEq σ] (j : σ) : linPart w (Pi.single j 1) = X j - C (w j) := by
  first
  | simp [linPart, Pi.single_apply, Finset.sum_ite_eq', ite_mul]
  | (unfold GroundTheory.Heights₂.Heights.GradientAtPoint.linPart; rw [Finset.sum_eq_single j] <;> simp +contextual [Pi.single_apply])



