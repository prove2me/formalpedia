-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_GradientAtPoint_eval_linPart_0d7a1dbc4716
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:55:54.140117+00:00
-- url     : https://prove2.me/submissions/072d2239-6c78-4173-a9f0-addfd411a48a

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
theorem _root_.solution [Fintype σ] (c : σ → ℂ) : eval w (linPart w c) = 0 := by
  simp [linPart]
end GroundTheory.Heights₂.Heights.GradientAtPoint
