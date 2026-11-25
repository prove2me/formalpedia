-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.E.tstar_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:42:47.275029+00:00
-- url     : https://prove2.me/submissions/18426fc2-1d48-4da7-9511-86e99f310e23

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_BasicIdentityStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HasCompactSupportDTw
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_TstarNormSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_tStarPoint
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.E
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.E
theorem _root_.solution (n : ℕ) {M : Type*} [TopologicalSpace M] (z : M → V n)
    (hz : IsLocalHomeomorph z) (ph ψ : M → ℝ) (f : M → V n) (hph : CkR n z 1 ph)
    (hψ : CkR n z 1 ψ) (hf : ∀ j, Ck n z 1 (fun x => f x j)) (x : M) :
    ‖tstar n z (fun y => ph y - 2 * ψ y) (fun y => ph y - ψ y) f x‖ ^ 2 *
        Real.exp (-(ph x - 2 * ψ x)) =
      ‖∑ j, (dTw n z ph j (fun y => f y j) x + f x j * d n z j (fun y => (ψ y : ℂ)) x)‖ ^ 2 *
        Real.exp (-ph x) := by
  have hp := tStarPoint n M z hz ph ψ f hph hψ hf x
  set S := ∑ j, (dTw n z ph j (fun y => f y j) x + f x j * d n z j (fun y => (ψ y : ℂ)) x) with hS
  set T := tstar n z (fun y => ph y - 2 * ψ y) (fun y => ph y - ψ y) f x with hT
  have he := Real.exp_pos (ψ x)
  have hn : Real.exp (ψ x) * ‖T‖ = ‖S‖ := by
    have h1 := congrArg (fun w : ℂ => ‖w‖) hp
    simp only [norm_mul, norm_neg] at h1
    rw [← h1]
    congr 1
    first
      | rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos he]
      | simp [abs_of_pos he]
  have hT' : ‖T‖ = ‖S‖ * Real.exp (-ψ x) := by
    rw [Real.exp_neg, ← hn]
    first
      | rw [mul_comm (Real.exp (ψ x)), mul_assoc, mul_inv_cancel₀ he.ne', mul_one]
      | field_simp
  have hx : Real.exp (-ψ x) ^ 2 * Real.exp (-(ph x - 2 * ψ x)) = Real.exp (-ph x) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hT', mul_pow, mul_assoc, hx]
end ReciprocityTheory.L2DbarEstimates.E
