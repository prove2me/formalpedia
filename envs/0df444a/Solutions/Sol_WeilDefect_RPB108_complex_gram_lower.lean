-- Prove2me | solution 1 for WeilDefect.RPB108.complex_gram_lower
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T04:00:39.226535+00:00
-- url     : https://prove2.me/submissions/06382d20-e4da-48f1-a9d1-cb08f0ca8489

import Theorems.Thm_WeilDefect_RPB108_real_gram_lower
import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem solution (A : Fin 3 → Fin 3 → ℝ) (d u : Fin 3 → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hd : ∀ i, d i ≤ A i i)
    (ha : ∀ i j, i ≠ j → |A i j| ≤ offWeights u i j)
    (z : Fin 3 → ℂ) :
    (∑ i, rowMargins d u i*‖z i‖^2) ≤ complexGram A z := by
  have hre := real_gram_lower A d u hu hd ha (fun i => (z i).re)
  have him := real_gram_lower A d u hu hd ha (fun i => (z i).im)
  have hnorm (i : Fin 3) : ‖z i‖^2 = (z i).re^2+(z i).im^2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, pow_two]
  have hid : complexGram A z =
      realGram A (fun i => (z i).re)+realGram A (fun i => (z i).im) := by
    simp [complexGram, realGram, Complex.mul_re, mul_add,
      Finset.sum_add_distrib, mul_assoc]
  rw [hid]
  have hs : (∑ i, rowMargins d u i*‖z i‖^2) =
      (∑ i, rowMargins d u i*(z i).re^2)+
      (∑ i, rowMargins d u i*(z i).im^2) := by
    simp_rw [hnorm, mul_add]
    rw [Finset.sum_add_distrib]
  rw [hs]
  exact add_le_add hre him
