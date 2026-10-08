-- Prove2me | solution 1 for OneEdgeEndpointRadiusRefinement
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T22:30:59.169988+00:00
-- url     : https://prove2.me/submissions/ff0d8b21-7e38-4848-b75d-d3fc44ff8c8c

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

open Classical
noncomputable section

theorem solution
    (V : Finset (EuclideanSpace ℝ (Fin 2)))
    (E : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
    (a b : EuclideanSpace ℝ (Fin 2))
    (ρa ρb : ℝ)
    (hab : a ≠ b)
    (hρa_pos : 0 < ρa) (hρb_pos : 0 < ρb)
    (hρa_vertices :
      ∀ v : EuclideanSpace ℝ (Fin 2),
        v ∈ V → v ≠ a → v ∉ Metric.ball a ρa)
    (hρa_edges :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → e.1 ≠ a → e.2 ≠ a →
          Disjoint (Metric.ball a ρa) (segment ℝ e.1 e.2))
    (hρb_vertices :
      ∀ v : EuclideanSpace ℝ (Fin 2),
        v ∈ V → v ≠ b → v ∉ Metric.ball b ρb)
    (hρb_edges :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → e.1 ≠ b → e.2 ≠ b →
          Disjoint (Metric.ball b ρb) (segment ℝ e.1 e.2)) :
    ∃ ra rb : ℝ,
      0 < ra ∧ 0 < rb ∧
        ra ≤ ρa ∧ rb ≤ ρb ∧
        ra < dist a b / 3 ∧ rb < dist a b / 3 ∧
        ra + rb < dist a b ∧
        (∀ v : EuclideanSpace ℝ (Fin 2),
          v ∈ V → v ≠ a → v ∉ Metric.ball a ra) ∧
        (∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
          e ∈ E → e.1 ≠ a → e.2 ≠ a →
            Disjoint (Metric.ball a ra) (segment ℝ e.1 e.2)) ∧
        (∀ v : EuclideanSpace ℝ (Fin 2),
          v ∈ V → v ≠ b → v ∉ Metric.ball b rb) ∧
        (∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
          e ∈ E → e.1 ≠ b → e.2 ≠ b →
            Disjoint (Metric.ball b rb) (segment ℝ e.1 e.2)) := by
  classical
  have hdist_pos : 0 < dist a b := dist_pos.mpr hab
  let ra : ℝ := min ρa (dist a b / 6)
  let rb : ℝ := min ρb (dist a b / 6)
  have hra_pos : 0 < ra := by
    dsimp [ra]
    exact lt_min hρa_pos (by positivity)
  have hrb_pos : 0 < rb := by
    dsimp [rb]
    exact lt_min hρb_pos (by positivity)
  have hra_le : ra ≤ ρa := by
    dsimp [ra]
    exact min_le_left _ _
  have hrb_le : rb ≤ ρb := by
    dsimp [rb]
    exact min_le_left _ _
  have hra_lt_third : ra < dist a b / 3 := by
    dsimp [ra]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hrb_lt_third : rb < dist a b / 3 := by
    dsimp [rb]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hsum_lt : ra + rb < dist a b := by
    have hra_le_six : ra ≤ dist a b / 6 := by
      dsimp [ra]
      exact min_le_right _ _
    have hrb_le_six : rb ≤ dist a b / 6 := by
      dsimp [rb]
      exact min_le_right _ _
    linarith
  refine ⟨ra, rb, hra_pos, hrb_pos, hra_le, hrb_le, hra_lt_third,
    hrb_lt_third, hsum_lt, ?_, ?_, ?_, ?_⟩
  · intro v hv hvne hvball
    exact hρa_vertices v hv hvne (Metric.ball_subset_ball hra_le hvball)
  · intro e he hsrc htgt
    exact (hρa_edges e he hsrc htgt).mono_left (Metric.ball_subset_ball hra_le)
  · intro v hv hvne hvball
    exact hρb_vertices v hv hvne (Metric.ball_subset_ball hrb_le hvball)
  · intro e he hsrc htgt
    exact (hρb_edges e he hsrc htgt).mono_left (Metric.ball_subset_ball hrb_le)
