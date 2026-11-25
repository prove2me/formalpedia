-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.blockPoint_blockRot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:34:13.871923+00:00
-- url     : https://prove2.me/submissions/973c6376-0fc7-4a5f-848a-1df0ace492af

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_rotLIE_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric
open scoped Pointwise
private theorem coe_circle_exp_two_pi_mul (t : ℝ) :
    ((Circle.exp (2 * Real.pi * t) : Circle) : ℂ) = Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) := by
  rw [Circle.coe_exp]
  congr 1
  push_cast
  ring
end ReciprocityTheory.MultiplicativeHeights
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric
open scoped Pointwise
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {B n : ℕ} (θ : Fin B × Fin n → ℝ) (z : BlockSphere B n) :
    blockPoint (blockRot θ z) = fun p => blockPoint z p * torusPoint θ p := by
  funext p
  obtain ⟨b, j⟩ := p
  show WithLp.ofLp (rotLIE (fun j' => Circle.exp (2 * Real.pi * θ (b, j')))
      (z b : EuclideanSpace ℂ (Fin n))) j =
    WithLp.ofLp (z b : EuclideanSpace ℂ (Fin n)) j * torusPoint θ (b, j)
  rw [rotLIE_apply]
  simp only [coe_circle_exp_two_pi_mul, torusPoint]
  ring
end ReciprocityTheory.MultiplicativeHeights
