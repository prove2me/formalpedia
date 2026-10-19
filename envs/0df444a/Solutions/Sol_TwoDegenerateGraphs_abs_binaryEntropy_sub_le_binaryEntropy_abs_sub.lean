-- Prove2me | solution 1 for TwoDegenerateGraphs.abs_binaryEntropy_sub_le_binaryEntropy_abs_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/b7e1210e-baa4-44a6-acff-44f28349b2c7

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_binaryEntropy_subadditive

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (x y : ℝ)
    (hxzero : 0 ≤ x) (hxone : x ≤ 1)
    (hyzero : 0 ≤ y) (hyone : y ≤ 1) :
    |binaryEntropy x - binaryEntropy y| ≤
      binaryEntropy |x - y| := by
  have hordered :
      ∀ x y : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → x ≤ y →
        |binaryEntropy x - binaryEntropy y| ≤ binaryEntropy |x - y| := by
    intro a b hazero haone hbzero hbone hab
    have hdifference : 0 ≤ b - a := sub_nonneg.mpr hab
    have hforward :
        binaryEntropy b ≤ binaryEntropy a + binaryEntropy (b - a) := by
      have h := binaryEntropy_subadditive a (b - a)
        hazero hdifference (by linarith)
      have hargument : a + (b - a) = b := by ring
      rwa [hargument] at h
    have hbackward :
        binaryEntropy a ≤ binaryEntropy b + binaryEntropy (b - a) := by
      have h := binaryEntropy_subadditive (1 - b) (b - a)
        (sub_nonneg.mpr hbone) hdifference (by linarith)
      have hargument : 1 - b + (b - a) = 1 - a := by ring
      rw [hargument, binaryEntropy_one_sub, binaryEntropy_one_sub] at h
      exact h
    rw [abs_of_nonpos (sub_nonpos.mpr hab), abs_le]
    have hneg : -(a - b) = b - a := by ring
    rw [hneg]
    constructor <;> linarith
  by_cases hxy : x ≤ y
  · exact hordered x y hxzero hxone hyzero hyone hxy
  · have hyx : y ≤ x := le_of_not_ge hxy
    have h := hordered y x hyzero hyone hxzero hxone hyx
    simpa [abs_sub_comm] using h
end TwoDegenerateGraphs
