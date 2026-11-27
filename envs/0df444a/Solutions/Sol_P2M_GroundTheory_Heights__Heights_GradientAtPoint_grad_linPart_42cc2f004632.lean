-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_linPart_42cc2f004632
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:20:41.407275+00:00
-- url     : https://prove2.me/submissions/5db9464b-043c-49c8-895a-baddbd315575

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
theorem _root_.solution [Fintype σ] (c : σ → ℂ) : grad w (linPart w c) = c := by
  funext j
  change (aeval w) ((pderiv j) (∑ x, C (c x) * (X x - C (w x)))) = c j
  rw [map_sum, map_sum, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [MvPolynomial.pderiv_X_of_ne hb]
  · simp



