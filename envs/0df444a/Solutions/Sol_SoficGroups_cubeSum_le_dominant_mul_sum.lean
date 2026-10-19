-- Prove2me | solution 1 for SoficGroups.cubeSum_le_dominant_mul_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/06d146f5-3500-45ed-b2f9-48b5d6697fc3

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution (ps : List ℝ) (m : ℝ)
    (hpos : ∀ p ∈ ps, 0 ≤ p)
    (hone : ∀ p ∈ ps, p ≤ 1)
    (hdom : ∀ p ∈ ps, p ≤ m) :
    (ps.map fun p => p ^ 3).sum ≤ m * ps.sum := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      have hp : 0 ≤ p := hpos p (by simp)
      have hpone : p ≤ 1 := hone p (by simp)
      have hpm : p ≤ m := hdom p (by simp)
      have hsq : p * p ≤ m := calc
        p * p ≤ p * 1 := mul_le_mul_of_nonneg_left hpone hp
        _ = p := by ring
        _ ≤ m := hpm
      have hcube : p ^ 3 ≤ m * p := calc
        p ^ 3 = (p * p) * p := by ring
        _ ≤ m * p := mul_le_mul_of_nonneg_right hsq hp
      have htailpos : ∀ q ∈ ps, 0 ≤ q := by
        intro q hq
        exact hpos q (by simp [hq])
      have htailone : ∀ q ∈ ps, q ≤ 1 := by
        intro q hq
        exact hone q (by simp [hq])
      have htaildom : ∀ q ∈ ps, q ≤ m := by
        intro q hq
        exact hdom q (by simp [hq])
      have htail := ih htailpos htailone htaildom
      simpa [mul_add] using add_le_add hcube htail
end SoficGroups
