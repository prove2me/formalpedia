-- Prove2me | solution 1 for TwoDegenerateGraphs.retainedVertex_card_le_manuscriptVertexCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/6fa2d0eb-baf5-404e-9c9a-52b9ca50e011

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingRetainedVertexCount_eq_card

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
open Classical
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension : ℕ)
    (retained : Set (Bool × HammingWord dimension))
    (hvertices :
      hammingRetainedVertexCount dimension retained <
        3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ)) :
    Fintype.card retained ≤ manuscriptVertexCount dimension := by
  have hreal :
      (Fintype.card retained : ℝ) ≤
        (manuscriptVertexCount dimension : ℝ) := by
    calc
      (Fintype.card retained : ℝ) =
          hammingRetainedVertexCount dimension retained :=
        (hammingRetainedVertexCount_eq_card dimension retained).symm
      _ ≤ 3 * hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ) := hvertices.le
      _ ≤ (⌈3 * hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ)⌉₊ : ℝ) :=
        Nat.le_ceil _
      _ = (manuscriptVertexCount dimension : ℝ) := rfl
  exact_mod_cast hreal
end TwoDegenerateGraphs
