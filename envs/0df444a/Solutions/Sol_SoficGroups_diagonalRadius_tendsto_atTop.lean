-- Prove2me | solution 1 for SoficGroups.diagonalRadius_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/06cd5fa3-ef48-41ff-a99d-720be0cabf7c

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
    Tendsto (diagonalRadius e) atTop atTop := by
  classical
  apply Filter.tendsto_atTop.2
  intro k
  have htol : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by
    positivity
  have herr : ∀ᶠ n in atTop, e n k < 1 / ((k : ℝ) + 1) :=
    (he k).eventually (gt_mem_nhds htol)
  filter_upwards [eventually_ge_atTop k, herr] with n hn hn'
  exact Nat.le_findGreatest hn hn'
end SoficGroups
