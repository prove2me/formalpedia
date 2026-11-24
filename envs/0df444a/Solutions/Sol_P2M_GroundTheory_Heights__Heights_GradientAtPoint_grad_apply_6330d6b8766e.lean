-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_apply_6330d6b8766e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:48.8648+00:00
-- url     : https://prove2.me/submissions/c24ee89d-baf5-4e3d-9fe2-0b3ed65d3ad3

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
theorem _root_.solution (p : MvPolynomial σ ℂ) (i : σ) : grad w p i = eval w (pderiv i p) := by
  simp [grad]
end GroundTheory.Heights₂.Heights.GradientAtPoint
