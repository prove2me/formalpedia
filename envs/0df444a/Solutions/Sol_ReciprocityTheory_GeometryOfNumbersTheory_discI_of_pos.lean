-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.discI_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:42:55.744201+00:00
-- url     : https://prove2.me/submissions/a5e8ebbe-1598-4975-9105-5f34647d4706

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_DiscSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_pgds_discI_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Filter Topology
open Set
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
    discI a R = Real.pi * (1 - Real.exp (-(a * R ^ 2))) / a := by
  rw [pgds_discI_eq a hR]
  have hd : ∀ x ∈ uIcc 0 R, HasDerivAt (fun s => -(Real.pi / a) * Real.exp (-(a * s ^ 2)))
      (2 * Real.pi * (x * Real.exp (-(a * x ^ 2)))) x := by
    intro x _
    have := (((hasDerivAt_pow 2 x).const_mul a).neg.exp).const_mul (-(Real.pi / a))
    refine this.congr_deriv ?_
    rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]
    simp only [Pi.neg_apply, Nat.cast_ofNat]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, neg_zero,
    Real.exp_zero, mul_one]
  ring
end ReciprocityTheory.GeometryOfNumbersTheory
