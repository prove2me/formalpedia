-- Prove2me | solution 1 for RayBundle.GraphRealization.integer_distance_vertex
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-10-08T18:57:53.254978+00:00
-- url     : https://prove2.me/submissions/15eba988-b6cd-4333-bd1e-e56d80287ea0

import Definitions.Def_RayBundle_UnitEdgeGraphGeometry
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Gluing
import Mathlib.Topology.MetricSpace.Isometry

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

-- Source: RayBundle.Thm_Cayley_GraphRealization_edge_zero
namespace RayBundle

universe u

theorem GraphRealization.edge_zero {V : Type u} (T : SimpleGraph V)
    (hT : T.Connected) (e : ℕ ≃ T.edgeSet) (n : ℕ) :
    edge T hT e n ⟨0, by simp⟩ = vertex T hT e (graphEdgePair T e n).1 := by
  let := connectedGraphMetric T hT
  exact UnitEdgeRealization.edge_zero _ _ _ n

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

-- Source: RayBundle.Thm_Cayley_GraphRealization_edge_one
namespace RayBundle

universe u

theorem GraphRealization.edge_one {V : Type u} (T : SimpleGraph V)
    (hT : T.Connected) (e : ℕ ≃ T.edgeSet) (n : ℕ) :
    edge T hT e n ⟨1, by simp⟩ = vertex T hT e (graphEdgePair T e n).2 := by
  let := connectedGraphMetric T hT
  exact UnitEdgeRealization.edge_one _ _ _ n

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

-- Source: RayBundle.Thm_Cayley_GraphRealization_covered
namespace RayBundle

universe u

theorem GraphRealization.covered {V : Type u} (T : SimpleGraph V)
    (hT : T.Connected) (e : ℕ ≃ T.edgeSet) (p : GraphRealization T hT e) :
    (∃ v, p = vertex T hT e v) ∨ ∃ n t, p = edge T hT e n t := by
  let := connectedGraphMetric T hT
  exact UnitEdgeRealization.covered _ _ _ p

end RayBundle

-- Source: RayBundle.Thm_Cayley_UnitEdgeStage_attach_edge_old_dist
namespace RayBundle

/-- Distance from a newly attached edge to the old space uses one of its endpoints. -/
theorem UnitEdgeStage.attach_edge_old_dist {V : Type*} [MetricSpace V]
    (A : UnitEdgeStage V) (a b : V) (hab : dist a b = 1)
    (t : Set.Icc (0 : ℝ) 1) (x : A.carrier) :
    let E := A.attach a b hab
    dist (E.edge t) (E.old x) =
      min (t.val + dist (A.vertex a) x) (1 - t.val + dist (A.vertex b) x) := by
  let Z := {r : ℝ // r = 0 ∨ r = 1}
  let : Nonempty Z := ⟨⟨0, Or.inl rfl⟩⟩
  let F : Z → ℝ := fun z => dist x (if z.val = 0 then A.vertex a else A.vertex b) + |t.val - z.val|
  change (⨅ z : Z, F z) + 0 = _
  rw [add_zero]
  have h0 : F ⟨0, Or.inl rfl⟩ = t.val + dist (A.vertex a) x := by
    simp [F, abs_of_nonneg t.property.1, dist_comm, add_comm]
  have h1 : F ⟨1, Or.inr rfl⟩ = 1 - t.val + dist (A.vertex b) x := by
    simp [F, abs_of_nonpos (sub_nonpos.mpr t.property.2), dist_comm]
    ring
  have hb : BddBelow (Set.range F) := ⟨0, by
    rintro _ ⟨z, rfl⟩
    exact add_nonneg dist_nonneg (abs_nonneg _)⟩
  apply le_antisymm
  · apply le_min
    · simpa only [h0] using ciInf_le hb (⟨0, Or.inl rfl⟩ : Z)
    · simpa only [h1] using ciInf_le hb (⟨1, Or.inr rfl⟩ : Z)
  · apply le_ciInf
    intro z
    rcases z.property with hz | hz
    · have he : z = ⟨0, Or.inl rfl⟩ := Subtype.ext hz
      rw [he, h0]
      exact min_le_left _ _
    · have he : z = ⟨1, Or.inr rfl⟩ := Subtype.ext hz
      rw [he, h1]
      exact min_le_right _ _

end RayBundle

-- Source: RayBundle.Thm_Cayley_UnitEdgeRealization_edge_vertex_dist
namespace RayBundle

/-- The exact endpoint formula survives the metric inductive limit. -/
theorem UnitEdgeRealization.edge_vertex_dist {V : Type*} [MetricSpace V]
    (a b : ℕ → V) (hab : ∀ n, dist (a n) (b n) = 1) (n : ℕ)
    (t : Set.Icc (0 : ℝ) 1) (v : V) :
    dist (edge a b hab n t) (vertex a b hab v) =
      min (t.val + dist (a n) v) (1 - t.val + dist (b n) v) := by
  let A := UnitEdgeStage.sequence a b hab n
  let E := A.attach (a n) (b n) (hab n)
  have hi := Metric.toInductiveLimit_isometry (UnitEdgeStage.sequenceStep_isometry a b hab) (n + 1)
  have hv : Metric.toInductiveLimit (UnitEdgeStage.sequenceStep_isometry a b hab) (n + 1)
      (E.old (A.vertex v)) = vertex a b hab v :=
    (congrFun (Metric.toInductiveLimit_commute
      (UnitEdgeStage.sequenceStep_isometry a b hab) n) (A.vertex v)).trans
      (vertex_at_stage a b hab n v)
  calc
    dist (edge a b hab n t) (vertex a b hab v) = dist (E.edge t) (E.old (A.vertex v)) := by
      rw [← hv]
      exact hi.dist_eq _ _
    _ = min (t.val + dist (A.vertex (a n)) (A.vertex v))
        (1 - t.val + dist (A.vertex (b n)) (A.vertex v)) :=
      A.attach_edge_old_dist (a n) (b n) (hab n) t (A.vertex v)
    _ = _ := by rw [A.vertexIsometry.dist_eq, A.vertexIsometry.dist_eq]

end RayBundle

-- Source: RayBundle.Thm_Cayley_GraphRealization_edge_vertex_dist
namespace RayBundle

theorem GraphRealization.edge_vertex_dist {V : Type*} (T : SimpleGraph V)
    (hT : T.Connected) (e : ℕ ≃ T.edgeSet) (n : ℕ)
    (t : Set.Icc (0 : ℝ) 1) (v : V) :
    dist (edge T hT e n t) (vertex T hT e v) =
      min (t.val + (T.dist (graphEdgePair T e n).1 v : ℝ))
        (1 - t.val + (T.dist (graphEdgePair T e n).2 v : ℝ)) := by
  let := connectedGraphMetric T hT
  exact UnitEdgeRealization.edge_vertex_dist _ _ _ n t v

end RayBundle

-- Source: RayBundle.Thm_Cayley_GraphRealization_integer_distance_vertex
namespace RayBundle

end RayBundle

open RayBundle
universe u
/-- In a unit-edge graph, an integer-distance sphere about a vertex contains only vertices. -/
theorem solution {V : Type*} (T : SimpleGraph V)
    (hT : T.Connected) (e : ℕ ≃ T.edgeSet) (p : RayBundle.GraphRealization T hT e)
    (v : V) (n : ℕ) (hn : dist p (RayBundle.GraphRealization.vertex T hT e v) = (n : ℝ)) :
    ∃ w, p = RayBundle.GraphRealization.vertex T hT e w := by
  rcases RayBundle.GraphRealization.covered T hT e p with h | ⟨j, t, rfl⟩
  · exact h
  · by_cases h0 : t.val = 0
    · exact ⟨(RayBundle.graphEdgePair T e j).1, by
        have ht : t = ⟨0, by simp⟩ := Subtype.ext h0
        rw [ht, RayBundle.GraphRealization.edge_zero]⟩
    by_cases h1 : t.val = 1
    · exact ⟨(RayBundle.graphEdgePair T e j).2, by
        have ht : t = ⟨1, by simp⟩ := Subtype.ext h1
        rw [ht, RayBundle.GraphRealization.edge_one]⟩
    have ht0 : 0 < t.val := lt_of_le_of_ne t.property.1 (Ne.symm h0)
    have ht1 : t.val < 1 := lt_of_le_of_ne t.property.2 h1
    rw [RayBundle.GraphRealization.edge_vertex_dist] at hn
    let A := T.dist (RayBundle.graphEdgePair T e j).1 v
    let B := T.dist (RayBundle.graphEdgePair T e j).2 v
    let k := min A B
    have hkA : (k : ℝ) ≤ A := by exact_mod_cast (min_le_left A B)
    have hkB : (k : ℝ) ≤ B := by exact_mod_cast (min_le_right A B)
    have hlow : (k : ℝ) < n := by
      rw [← hn]
      apply lt_min <;> change (k : ℝ) < _ <;> linarith
    have hupp : (n : ℝ) < (k : ℝ) + 1 := by
      rcases le_total A B with hAB | hBA
      · have hk : k = A := min_eq_left hAB
        rw [← hn, hk]
        exact lt_of_le_of_lt (min_le_left _ _) (by change t.val + (A : ℝ) < _; linarith)
      · have hk : k = B := min_eq_right hBA
        rw [← hn, hk]
        exact lt_of_le_of_lt (min_le_right _ _) (by change 1 - t.val + (B : ℝ) < _; linarith)
    have hlow' : k < n := by exact_mod_cast hlow
    have hupp' : n < k + 1 := by exact_mod_cast hupp
    omega

namespace RayBundle


end RayBundle
