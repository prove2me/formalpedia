-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_mul_206fa499c46e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:48.778422+00:00
-- url     : https://prove2.me/submissions/97e3732d-29d2-4e06-b16c-4839eecf4426

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GradientAtPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_apply_6330d6b8766e

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
theorem _root_.solution (a b : MvPolynomial σ ℂ) :
    grad w (a * b) = eval w a • grad w b + eval w b • grad w a := by
  ext i
  simp only [grad_apply, Derivation.leibniz, smul_eq_mul, map_add, map_mul, Pi.add_apply, Pi.smul_apply]
end GroundTheory.Heights₂.Heights.GradientAtPoint
