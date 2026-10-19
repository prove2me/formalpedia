-- Prove2me | solution 1 for TwoDegenerateGraphs.exists_manuscriptVertexCount_bracket
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/a4dff229-4b1b-4ac5-aead-78646c52f958

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_manuscriptVertexCount_tendsto_atTop

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution
    (minimum n : ℕ)
    (hminimum : manuscriptVertexCount minimum ≤ n) :
    ∃ dimension : ℕ,
      minimum ≤ dimension ∧
      manuscriptVertexCount dimension ≤ n ∧
      n < manuscriptVertexCount (dimension + 1) := by
  have hlarge :
      ∀ᶠ dimension : ℕ in Filter.atTop,
        n < manuscriptVertexCount dimension := by
    have hevent := Filter.tendsto_atTop.1
      manuscriptVertexCount_tendsto_atTop (n + 1)
    filter_upwards [hevent] with dimension hdimension
    omega
  obtain ⟨dimension, hdimension, hafter⟩ :=
    (hlarge.and (Filter.eventually_ge_atTop minimum)).exists
  have hexists :
      ∃ offset : ℕ,
        n < manuscriptVertexCount (minimum + offset) := by
    refine ⟨dimension - minimum, ?_⟩
    rw [Nat.add_sub_of_le hafter]
    exact hdimension
  let offset : ℕ := Nat.find hexists
  have hnext :
      n < manuscriptVertexCount (minimum + offset) :=
    Nat.find_spec hexists
  have hoffset : 0 < offset := by
    by_contra hnot
    have hzero : offset = 0 := Nat.eq_zero_of_not_pos hnot
    simp [hzero] at hnext
    omega
  refine ⟨minimum + (offset - 1), by omega, ?_, ?_⟩
  · have hbefore :
        ¬ n < manuscriptVertexCount (minimum + (offset - 1)) := by
      exact Nat.find_min hexists (by omega)
    exact Nat.le_of_not_gt hbefore
  · rw [show minimum + (offset - 1) + 1 = minimum + offset by omega]
    exact hnext
end TwoDegenerateGraphs
