-- Prove2me | solution 1 for ThreeSum.Parameters.phi_le_gamma_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:11:47.214372+00:00
-- url     : https://prove2.me/submissions/15c5cee9-c9fa-49d5-8bb4-c7813e28b597

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_Parameters
import Theorems.Thm_ThreeSum_Parameters_log_two_pos
import Theorems.Thm_ThreeSum_Parameters_gamma_formula
import Theorems.Thm_ThreeSum_Parameters_hasDerivAt_phi
import Theorems.Thm_ThreeSum_Parameters_hasDerivAt_gammaNumerator
import Theorems.Thm_ThreeSum_Parameters_gamma_derivative_above_phi

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Parameters
open Set Real
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.Parameters
theorem _root_.solution {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    phi t ≤ gamma t := by
  let F : ℝ → ℝ := fun y => gammaNumerator y - Real.log 2 * phi y
  let F' : ℝ → ℝ := fun y =>
    Real.log (255 + y) - Real.log (1 - y) - Real.log 2 * phiDeriv y
  have hd : ∀ y ∈ Icc (0 : ℝ) (1 / 2), HasDerivAt F (F' y) y := by
    intro y hy
    exact (hasDerivAt_gammaNumerator hy).sub ((hasDerivAt_phi y).const_mul (Real.log 2))
  have hm : MonotoneOn F (Icc (0 : ℝ) (1 / 2)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) (1 / 2))
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
    intro y hy
    exact sub_nonneg.mpr (gamma_derivative_above_phi (interior_subset hy))
  have hmono := hm (by constructor <;> norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) (1 / 2)) ht ht.1
  have hzero : F 0 = 0 := by norm_num [F, gammaNumerator, phi]
  rw [hzero] at hmono
  rw [gamma_formula ht, le_div_iff₀ log_two_pos]
  dsimp [F] at hmono
  nlinarith
end ThreeSum.Parameters
