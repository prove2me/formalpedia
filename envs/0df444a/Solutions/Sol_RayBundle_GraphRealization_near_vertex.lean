-- Prove2me | solution 1 for RayBundle.GraphRealization.near_vertex
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-10-08T18:57:39.773331+00:00
-- url     : https://prove2.me/submissions/b9c211b4-0572-45b5-882e-2fff399d63e6

import Definitions.Def_RayBundle_UnitEdgeGraphGeometry
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Gluing
import Mathlib.Topology.MetricSpace.Isometry

-- Source: RayBundle.Thm_Cayley_UnitEdgeRealization_edge_isometry
namespace RayBundle

universe u

theorem UnitEdgeRealization.edge_isometry {V : Type u} [MetricSpace V]
    (a b : ℕ → V) (hab : ∀ n, dist (a n) (b n) = 1) (n : ℕ) :
    Isometry (edge a b hab n) :=
  (Metric.toInductiveLimit_isometry (UnitEdgeStage.sequenceStep_isometry a b hab) (n + 1)).comp
    ((UnitEdgeStage.sequence a b hab n).attach (a n) (b n) (hab n)).edgeIsometry

end RayBundle

-- Source: RayBundle.Thm_Cayley_UnitEdgeRealization_vertex_at_stage
namespace RayBundle

universe u

theorem UnitEdgeRealization.vertex_at_stage {V : Type u} [MetricSpace V]
    (a b : ℕ → V) (hab : ∀ n, dist (a n) (b n) = 1) (n : ℕ) (v : V) :
    Metric.toInductiveLimit (UnitEdgeStage.sequenceStep_isometry a b hab) n
      ((UnitEdgeStage.sequence a b hab n).vertex v) = vertex a b hab v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (congrArg (Metric.toInductiveLimit
      (UnitEdgeStage.sequenceStep_isometry a b hab) (n + 1))
      (((UnitEdgeStage.sequence a b hab n).attach (a n) (b n) (hab n)).vertex_eq v)).trans
      ((congrFun (Metric.toInductiveLimit_commute
        (UnitEdgeStage.sequenceStep_isometry a b hab) n)
        ((UnitEdgeStage.sequence a b hab n).vertex v)).trans ih)

end RayBundle

-- Source: RayBundle.Thm_Cayley_UnitEdgeRealization_edge_zero
namespace RayBundle

universe u

theorem UnitEdgeRealization.edge_zero {V : Type u} [MetricSpace V]
    (a b : ℕ → V) (hab : ∀ n, dist (a n) (b n) = 1) (n : ℕ) :
    edge a b hab n ⟨0, by simp⟩ = vertex a b hab (a n) := by
  exact (congrArg (Metric.toInductiveLimit
    (UnitEdgeStage.sequenceStep_isometry a b hab) (n + 1))
    ((UnitEdgeStage.sequence a b hab n).attach (a n) (b n) (hab n)).edge_zero).trans
    (vertex_at_stage a b hab (n + 1) (a n))

end RayBundle

-- Source: RayBundle.Thm_Cayley_UnitEdgeRealization_edge_one
namespace RayBundle

universe u

theorem UnitEdgeRealization.edge_one {V : Type u} [MetricSpace V]
    (a b : ℕ → V) (hab : ∀ n, dist (a n) (b n) = 1) (n : ℕ) :
    edge a b hab n ⟨1, by simp⟩ = vertex a b hab (b n) := by
  exact (congrArg (Metric.toInductiveLimit
    (UnitEdgeStage.sequenceStep_isometry a b hab) (n + 1))
    ((UnitEdgeStage.sequence a b hab n).attach (a n) (b n) (hab n)).edge_one).trans
    (vertex_at_stage a b hab (n + 1) (b n))

end RayBundle

-- Source: RayBundle.Thm_Cayley_UnitEdgeRealization_stage_covered
namespace RayBundle

universe u

theorem UnitEdgeRealization.stage_covered {V : Type u} [MetricSpace V]
    (a b : ℕ → V) (hab : ∀ n, dist (a n) (b n) = 1) (n : ℕ) :
    ∀ x : (UnitEdgeStage.sequence a b hab n).carrier,
      (∃ v, Metric.toInductiveLimit (UnitEdgeStage.sequenceStep_isometry a b hab) n x =
        vertex a b hab v) ∨
      ∃ k t, Metric.toInductiveLimit (UnitEdgeStage.sequenceStep_isometry a b hab) n x =
        edge a b hab k t := by
  induction n with
  | zero => exact fun x => Or.inl ⟨x, rfl⟩
  | succ n ih =>
    intro x
    refine Quotient.inductionOn x ?_
    intro y
    rcases y with y | t
    · have he := congrFun (Metric.toInductiveLimit_commute
        (UnitEdgeStage.sequenceStep_isometry a b hab) n) y
      change Metric.toInductiveLimit (UnitEdgeStage.sequenceStep_isometry a b hab) (n + 1)
        (UnitEdgeStage.sequenceStep a b hab n y) =
        Metric.toInductiveLimit (UnitEdgeStage.sequenceStep_isometry a b hab) n y at he
      rcases ih y with ⟨v, hv⟩ | ⟨k, t, ht⟩
      · exact Or.inl ⟨v, he.trans hv⟩
      · exact Or.inr ⟨k, t, he.trans ht⟩
    · exact Or.inr ⟨n, t, rfl⟩

end RayBundle

-- Source: RayBundle.Thm_Cayley_UnitEdgeRealization_covered
namespace RayBundle

universe u

theorem UnitEdgeRealization.covered {V : Type u} [MetricSpace V]
    (a b : ℕ → V) (hab : ∀ n, dist (a n) (b n) = 1) (p : UnitEdgeRealization a b hab) :
    (∃ v, p = vertex a b hab v) ∨ ∃ n t, p = edge a b hab n t := by
  refine Quotient.inductionOn p ?_
  rintro ⟨n, x⟩
  exact stage_covered a b hab n x

end RayBundle

-- Source: RayBundle.Thm_Cayley_UnitEdgeRealization_near_vertex
namespace RayBundle

universe u

theorem UnitEdgeRealization.near_vertex {V : Type u} [MetricSpace V]
    (a b : ℕ → V) (hab : ∀ n, dist (a n) (b n) = 1) (p : UnitEdgeRealization a b hab) :
    ∃ v, dist p (vertex a b hab v) ≤ (1 / 2 : ℝ) := by
  rcases covered a b hab p with ⟨v, rfl⟩ | ⟨n, t, rfl⟩
  · exact ⟨v, by simp⟩
  · by_cases ht : t.val ≤ (1 / 2 : ℝ)
    · refine ⟨a n, ?_⟩
      rw [← edge_zero a b hab n, (edge_isometry a b hab n).dist_eq]
      change |t.val - 0| ≤ (1 / 2 : ℝ)
      simpa only [sub_zero, abs_of_nonneg t.property.1] using ht
    · refine ⟨b n, ?_⟩
      rw [← edge_one a b hab n, (edge_isometry a b hab n).dist_eq]
      change |t.val - 1| ≤ (1 / 2 : ℝ)
      rw [abs_of_nonpos (by linarith [t.property.2])]
      linarith

end RayBundle

-- Source: RayBundle.Thm_Cayley_GraphRealization_near_vertex
namespace RayBundle

universe u

end RayBundle

open RayBundle
universe u
theorem solution {V : Type u} (T : SimpleGraph V)
    (hT : T.Connected) (e : ℕ ≃ T.edgeSet) (p : RayBundle.GraphRealization T hT e) :
    ∃ v, dist p (RayBundle.GraphRealization.vertex T hT e v) ≤ (1 / 2 : ℝ) := by
  let := RayBundle.connectedGraphMetric T hT
  exact RayBundle.UnitEdgeRealization.near_vertex _ _ _ p

namespace RayBundle


end RayBundle
