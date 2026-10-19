-- Prove2me | solution 1 for SoficGroups.diagonalRadius_eventually_error_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/4f306d8c-3592-49c9-bf8b-936a4bf8cb9e

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution (e : ℕ → ℕ → ℝ)
    (he : ∀ k, Tendsto (fun n => e n k) atTop (𝓝 0)) :
    ∀ᶠ n in atTop,
      e n (diagonalRadius e n) <
        1 / ((diagonalRadius e n : ℝ) + 1) := by
  classical
  have htol : (0 : ℝ) < 1 / ((0 : ℝ) + 1) := by
    norm_num
  have herr : ∀ᶠ n in atTop,
      e n 0 < 1 / ((0 : ℝ) + 1) :=
    (he 0).eventually (gt_mem_nhds htol)
  filter_upwards [herr] with n hn
  change
    (fun k : ℕ => e n k < 1 / ((k : ℝ) + 1))
      (Nat.findGreatest (fun k => e n k < 1 / ((k : ℝ) + 1)) n)
  exact Nat.findGreatest_spec
    (P := fun k => e n k < 1 / ((k : ℝ) + 1))
    (Nat.zero_le n) (by simpa using hn)
end SoficGroups
