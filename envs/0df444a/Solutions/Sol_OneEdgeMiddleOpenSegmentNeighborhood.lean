-- Prove2me | solution 1 for OneEdgeMiddleOpenSegmentNeighborhood
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T22:31:24.831989+00:00
-- url     : https://prove2.me/submissions/adef5222-d959-4c78-8064-cdfe735f6c5a

import Mathlib.Tactic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

open Classical
noncomputable section

theorem solution
    (a b : EuclideanSpace ℝ (Fin 2))
    (ra rb t0 t1 : ℝ)
    (middleRect : Set (EuclideanSpace ℝ (Fin 2)))
    (hab : a ≠ b)
    (ht0 : 0 < t0) (ht01 : t0 < t1) (ht1 : t1 < 1)
    (ht0_reaches_a : t0 * dist a b < ra)
    (ht1_reaches_b : (1 - t1) * dist a b < rb)
    (hline_t0_ball_a : AffineMap.lineMap a b t0 ∈ Metric.ball a ra)
    (hline_t1_ball_b : AffineMap.lineMap a b t1 ∈ Metric.ball b rb)
    (hmiddleRect_open : IsOpen middleRect)
    (haxis_subset :
      AffineMap.lineMap a b '' Set.Ioo t0 t1 ⊆ middleRect) :
    IsOpen ((Metric.ball a ra ∪ middleRect) ∪ Metric.ball b rb) ∧
      openSegment ℝ a b ⊆
        ((Metric.ball a ra ∪ middleRect) ∪ Metric.ball b rb) := by
  classical
  have hdist_pos : 0 < dist a b := dist_pos.mpr hab
  have hcuts_order : 0 < t0 ∧ t0 < t1 ∧ t1 < 1 :=
    ⟨ht0, ht01, ht1⟩
  constructor
  · exact (Metric.isOpen_ball.union hmiddleRect_open).union Metric.isOpen_ball
  · intro x hx
    rw [openSegment_eq_image_lineMap] at hx
    rcases hx with ⟨t, ht, rfl⟩
    rcases lt_trichotomy t t0 with ht_lt_t0 | ht_eq_t0 | ht0_lt_t
    · left
      left
      rw [Metric.mem_ball, dist_lineMap_left]
      have ht_mul_lt :
          t * dist a b < t0 * dist a b :=
        mul_lt_mul_of_pos_right ht_lt_t0 hdist_pos
      exact lt_trans (by
        simpa [Real.norm_eq_abs, abs_of_pos ht.1] using ht_mul_lt)
        ht0_reaches_a
    · left
      left
      simpa [ht_eq_t0] using hline_t0_ball_a
    · rcases lt_trichotomy t t1 with ht_lt_t1 | ht_eq_t1 | ht1_lt_t
      · left
        right
        exact haxis_subset ⟨t, ⟨ht0_lt_t, ht_lt_t1⟩, rfl⟩
      · right
        simpa [ht_eq_t1] using hline_t1_ball_b
      · right
        rw [Metric.mem_ball, dist_lineMap_right]
        have hsub_lt : 1 - t < 1 - t1 := by
          linarith
        have hsub_mul_lt :
            (1 - t) * dist a b < (1 - t1) * dist a b :=
          mul_lt_mul_of_pos_right hsub_lt hdist_pos
        have hsub_pos : 0 < 1 - t := by
          exact sub_pos.mpr ht.2
        exact lt_trans (by
          simpa [Real.norm_eq_abs, abs_of_pos hsub_pos] using hsub_mul_lt)
          ht1_reaches_b
