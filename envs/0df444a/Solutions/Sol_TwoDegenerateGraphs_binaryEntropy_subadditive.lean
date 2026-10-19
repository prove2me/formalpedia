-- Prove2me | solution 1 for TwoDegenerateGraphs.binaryEntropy_subadditive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/985f5a27-8af5-4705-a1ad-043d29d6ddaa

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_binaryEntropy_scale_le

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hsum : x + y ≤ 1) :
    binaryEntropy (x + y) ≤ binaryEntropy x + binaryEntropy y := by
  by_cases hzero : x + y = 0
  · have hxzero : x = 0 := by linarith
    have hyzero : y = 0 := by linarith
    simp [hxzero, hyzero]
  have hpositive : 0 < x + y :=
    lt_of_le_of_ne (add_nonneg hx hy) (Ne.symm hzero)
  have hxscale : 0 ≤ x / (x + y) :=
    div_nonneg hx hpositive.le
  have hyscale : 0 ≤ y / (x + y) :=
    div_nonneg hy hpositive.le
  have hxscale_one : x / (x + y) ≤ 1 := by
    apply (div_le_one hpositive).mpr
    linarith
  have hyscale_one : y / (x + y) ≤ 1 := by
    apply (div_le_one hpositive).mpr
    linarith
  have hxentropy := binaryEntropy_scale_le (x + y) (x / (x + y))
    (add_nonneg hx hy) hsum hxscale hxscale_one
  have hyentropy := binaryEntropy_scale_le (x + y) (y / (x + y))
    (add_nonneg hx hy) hsum hyscale hyscale_one
  have hxidentity : x / (x + y) * (x + y) = x := by
    field_simp [hpositive.ne']
  have hyidentity : y / (x + y) * (x + y) = y := by
    field_simp [hpositive.ne']
  rw [hxidentity] at hxentropy
  rw [hyidentity] at hyentropy
  have hcombined := add_le_add hxentropy hyentropy
  have hleft :
      x / (x + y) * binaryEntropy (x + y) +
          y / (x + y) * binaryEntropy (x + y) =
        binaryEntropy (x + y) := by
    field_simp [hpositive.ne']
  rw [hleft] at hcombined
  exact hcombined
end TwoDegenerateGraphs
