-- Prove2me | solution 1 for RayBundle.GraphRealization.intrinsicEDist_eq
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-10-08T18:57:04.191049+00:00
-- url     : https://prove2.me/submissions/50c21ac0-4880-4b92-9dab-c621f485d86a

import Definitions.Def_RayBundle_UnitEdgeGraphGeometry
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Gluing
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Path

-- Source: RayBundle.Def_Cayley_GraphRealization_DirectedUnitEdge
namespace RayBundle

/-- A unit edge directed from a specified initial vertex to a final vertex. -/
structure GraphRealization.DirectedUnitEdge {V : Type*} (T : SimpleGraph V)
    (hT : T.Connected) (e : ℕ ≃ T.edgeSet) (a b : V) where
  map : Set.Icc (0 : ℝ) 1 → GraphRealization T hT e
  isometry : Isometry map
  zero : map ⟨0, by simp⟩ = vertex T hT e a
  one : map ⟨1, by simp⟩ = vertex T hT e b
  vertex_parameter : ∀ t v, map t = vertex T hT e v → t.val = 0 ∨ t.val = 1

end RayBundle

-- Source: RayBundle.Thm_Cayley_UnitEdgeRealization_edge_isometry
namespace RayBundle

universe u

theorem UnitEdgeRealization.edge_isometry {V : Type u} [MetricSpace V]
    (a b : ℕ → V) (hab : ∀ n, dist (a n) (b n) = 1) (n : ℕ) :
    Isometry (edge a b hab n) :=
  (Metric.toInductiveLimit_isometry (UnitEdgeStage.sequenceStep_isometry a b hab) (n + 1)).comp
    ((UnitEdgeStage.sequence a b hab n).attach (a n) (b n) (hab n)).edgeIsometry

end RayBundle

-- Source: RayBundle.Thm_Cayley_GraphRealization_edge_isometry
namespace RayBundle

universe u

theorem GraphRealization.edge_isometry {V : Type u} (T : SimpleGraph V)
    (hT : T.Connected) (e : ℕ ≃ T.edgeSet) (n : ℕ) : Isometry (edge T hT e n) := by
  let := connectedGraphMetric T hT
  exact UnitEdgeRealization.edge_isometry _ _ _ n

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

-- Source: RayBundle.Thm_Cayley_UnitEdgeRealization_edge_vertex_lower
namespace RayBundle

universe u

theorem UnitEdgeRealization.edge_vertex_lower {V : Type u} [MetricSpace V]
    (a b : ℕ → V) (hab : ∀ n, dist (a n) (b n) = 1) (n : ℕ)
    (t : Set.Icc (0 : ℝ) 1) (v : V) :
    min t.val (1 - t.val) ≤ dist (edge a b hab n t) (vertex a b hab v) := by
  let E := (UnitEdgeStage.sequence a b hab n).attach (a n) (b n) (hab n)
  have h := E.edge_old_lower t ((UnitEdgeStage.sequence a b hab n).vertex v)
  have hi := Metric.toInductiveLimit_isometry (UnitEdgeStage.sequenceStep_isometry a b hab) (n + 1)
  have hv : Metric.toInductiveLimit (UnitEdgeStage.sequenceStep_isometry a b hab) (n + 1)
      (E.old ((UnitEdgeStage.sequence a b hab n).vertex v)) = vertex a b hab v :=
    (congrFun (Metric.toInductiveLimit_commute
      (UnitEdgeStage.sequenceStep_isometry a b hab) n)
      ((UnitEdgeStage.sequence a b hab n).vertex v)).trans (vertex_at_stage a b hab n v)
  calc
    min t.val (1 - t.val) ≤ dist (E.edge t) (E.old ((UnitEdgeStage.sequence a b hab n).vertex v)) := h
    _ = dist (edge a b hab n t) (vertex a b hab v) := by
      exact (hi.dist_eq (E.edge t)
        (E.old ((UnitEdgeStage.sequence a b hab n).vertex v))).symm.trans
        (congrArg (fun z => dist (edge a b hab n t) z) hv)

end RayBundle

-- Source: RayBundle.Thm_Cayley_UnitEdgeRealization_vertex_isometry
namespace RayBundle

universe u

theorem UnitEdgeRealization.vertex_isometry {V : Type u} [MetricSpace V]
    (a b : ℕ → V) (hab : ∀ n, dist (a n) (b n) = 1) : Isometry (vertex a b hab) :=
  Metric.toInductiveLimit_isometry (UnitEdgeStage.sequenceStep_isometry a b hab) 0

end RayBundle

-- Source: RayBundle.Thm_Cayley_UnitEdgeRealization_edge_eq_vertex_iff
namespace RayBundle

universe u

theorem UnitEdgeRealization.edge_eq_vertex_iff {V : Type u} [MetricSpace V]
    (a b : ℕ → V) (hab : ∀ n, dist (a n) (b n) = 1) (n : ℕ)
    (t : Set.Icc (0 : ℝ) 1) (v : V) :
    edge a b hab n t = vertex a b hab v ↔
      (t.val = 0 ∧ v = a n) ∨ (t.val = 1 ∧ v = b n) := by
  constructor
  · intro h
    have hl := edge_vertex_lower a b hab n t v
    rw [h, dist_self] at hl
    have ht0 := t.property.1
    have ht1 := t.property.2
    rcases min_le_iff.mp hl with h0 | h1
    · have ht : t = ⟨0, by simp⟩ := Subtype.ext (by linarith)
      subst ht
      rw [edge_zero] at h
      exact Or.inl ⟨rfl, ((vertex_isometry a b hab).injective h).symm⟩
    · have ht : t = ⟨1, by simp⟩ := Subtype.ext (by linarith)
      subst ht
      rw [edge_one] at h
      exact Or.inr ⟨rfl, ((vertex_isometry a b hab).injective h).symm⟩
  · rintro (⟨ht, rfl⟩ | ⟨ht, rfl⟩)
    · have he : t = ⟨0, by simp⟩ := Subtype.ext ht
      subst he
      exact edge_zero a b hab n
    · have he : t = ⟨1, by simp⟩ := Subtype.ext ht
      subst he
      exact edge_one a b hab n

end RayBundle

-- Source: RayBundle.Thm_Cayley_GraphRealization_edge_eq_vertex_iff
namespace RayBundle

universe u

theorem GraphRealization.edge_eq_vertex_iff {V : Type u} (T : SimpleGraph V)
    (hT : T.Connected) (e : ℕ ≃ T.edgeSet) (n : ℕ)
    (t : Set.Icc (0 : ℝ) 1) (v : V) :
    edge T hT e n t = vertex T hT e v ↔
      (t.val = 0 ∧ v = (graphEdgePair T e n).1) ∨
      (t.val = 1 ∧ v = (graphEdgePair T e n).2) := by
  let := connectedGraphMetric T hT
  exact UnitEdgeRealization.edge_eq_vertex_iff _ _ _ n t v

end RayBundle

-- Source: RayBundle.Def_Cayley_GraphRealization_orientedEdge
namespace RayBundle

/-- Orient the enumerated edge joining adjacent vertices. -/
noncomputable def GraphRealization.orientedEdge {V : Type*} (T : SimpleGraph V)
    (hT : T.Connected) (e : ℕ ≃ T.edgeSet) (a b : V) (hab : T.Adj a b) :
    DirectedUnitEdge T hT e a b := by
  classical
  let k := e.symm ⟨s(a, b), hab⟩
  have hp : s((graphEdgePair T e k).1, (graphEdgePair T e k).2) = s(a, b) :=
    (Quot.out_eq (e k).val).trans (congrArg Subtype.val (e.apply_symm_apply ⟨s(a, b), hab⟩))
  by_cases h : (graphEdgePair T e k).1 = a ∧ (graphEdgePair T e k).2 = b
  · exact
      { map := edge T hT e k
        isometry := edge_isometry T hT e k
        zero := (edge_zero T hT e k).trans (congrArg (vertex T hT e) h.1)
        one := (edge_one T hT e k).trans (congrArg (vertex T hT e) h.2)
        vertex_parameter := fun t v hv =>
          ((edge_eq_vertex_iff T hT e k t v).mp hv).elim
            (fun hx => Or.inl hx.1) (fun hx => Or.inr hx.1) }
  · have h := (Sym2.eq_iff.mp hp).resolve_left h
    let flip : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 :=
      fun t => ⟨1 - t.val, by constructor <;> linarith [t.property.1, t.property.2]⟩
    have hf : Isometry flip := by
      apply Isometry.of_dist_eq
      intro s t
      change |(1 - s.val) - (1 - t.val)| = |s.val - t.val|
      rw [show (1 - s.val) - (1 - t.val) = -(s.val - t.val) by ring, abs_neg]
    refine
      { map := edge T hT e k ∘ flip
        isometry := (edge_isometry T hT e k).comp hf
        zero := ?_
        one := ?_
        vertex_parameter := ?_ }
    · simpa [flip, Function.comp_def] using
        (edge_one T hT e k).trans (congrArg (vertex T hT e) h.2)
    · simpa [flip, Function.comp_def] using
        (edge_zero T hT e k).trans (congrArg (vertex T hT e) h.1)
    · intro t v hv
      rcases (edge_eq_vertex_iff T hT e k (flip t) v).mp hv with hz | ho
      · right
        have ht : 1 - t.val = 0 := hz.1
        linarith
      · left
        have ht : 1 - t.val = 1 := ho.1
        linarith

end RayBundle

-- Source: RayBundle.Def_Cayley_MetricSegment_of_short_map
namespace RayBundle

/-- A nonexpanding parametrization attaining the endpoint distance is geodesic. -/
noncomputable def MetricSegment.of_short_map {X : Type*} [MetricSpace X] {a b : X}
    (f : Set.Icc (0 : ℝ) (dist a b) → X)
    (hshort : ∀ u v, dist (f u) (f v) ≤ dist u v)
    (hstart : f ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = a)
    (hfinish : f ⟨dist a b, ⟨dist_nonneg, le_rfl⟩⟩ = b) : MetricSegment a b := by
  refine ⟨f, Isometry.of_dist_eq ?_, hstart, hfinish⟩
  have ordered (u v : Set.Icc (0 : ℝ) (dist a b)) (huv : u.val ≤ v.val) :
      dist (f u) (f v) = dist u v := by
    have hs := hshort ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ u
    have ht := hshort v ⟨dist a b, ⟨dist_nonneg, le_rfl⟩⟩
    rw [hstart] at hs
    rw [hfinish] at ht
    change dist a (f u) ≤ |0 - u.val| at hs
    change dist (f v) b ≤ |v.val - dist a b| at ht
    have hs' : dist a (f u) ≤ u.val := by
      simpa [Real.dist_eq, abs_of_nonneg u.property.1] using hs
    have ht' : dist (f v) b ≤ dist a b - v.val := by
      simpa [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr v.property.2)] using ht
    have huv' : dist u v = v.val - u.val := by
      change |u.val - v.val| = _
      rw [abs_of_nonpos (sub_nonpos.mpr huv)]
      ring
    apply le_antisymm (hshort u v)
    rw [huv']
    have h := dist_triangle4 a (f u) (f v) b
    linarith
  intro u v
  rcases le_total u.val v.val with h | h
  · exact ordered u v h
  · simpa only [dist_comm] using ordered v u h

end RayBundle

-- Source: RayBundle.Thm_Cayley_MetricSegment_dist_start
namespace RayBundle

theorem MetricSegment.dist_start {X : Type*} [MetricSpace X] {a b : X}
    (c : MetricSegment a b) (t : Set.Icc (0 : ℝ) (dist a b)) : dist a (c.map t) = t.val := by
  calc
    dist a (c.map t) = dist (c.map ⟨0, ⟨le_rfl, dist_nonneg⟩⟩) (c.map t) :=
      congrArg (fun p => dist p (c.map t)) c.start.symm
    _ = dist (⟨0, ⟨le_rfl, dist_nonneg⟩⟩ : Set.Icc (0 : ℝ) (dist a b)) t := c.isometry.dist_eq _ _
    _ = t.val := by
      change |0 - t.val| = t.val
      simp [abs_of_nonneg t.property.1]

end RayBundle

-- Source: RayBundle.Thm_Cayley_MetricSegment_dist_finish
namespace RayBundle

theorem MetricSegment.dist_finish {X : Type*} [MetricSpace X] {a b : X}
    (c : MetricSegment a b) (t : Set.Icc (0 : ℝ) (dist a b)) :
    dist (c.map t) b = dist a b - t.val := by
  calc
    dist (c.map t) b = dist (c.map t) (c.map ⟨dist a b, ⟨dist_nonneg, le_rfl⟩⟩) :=
      congrArg (dist (c.map t)) c.finish.symm
    _ = dist t (⟨dist a b, ⟨dist_nonneg, le_rfl⟩⟩ : Set.Icc (0 : ℝ) (dist a b)) := c.isometry.dist_eq _ _
    _ = dist a b - t.val := by
      change |t.val - dist a b| = dist a b - t.val
      rw [abs_of_nonpos (sub_nonpos.mpr t.property.2)]
      ring

end RayBundle

-- Source: RayBundle.Def_Cayley_MetricSegment_append
namespace RayBundle

/-- Concatenate geodesics when their lengths add to the endpoint distance. -/
noncomputable def MetricSegment.append {X : Type*} [MetricSpace X] {a b c : X}
    (ab : MetricSegment a b) (bc : MetricSegment b c)
    (hadd : dist a b + dist b c = dist a c) : MetricSegment a c := by
  let f : Set.Icc (0 : ℝ) (dist a c) → X := fun u =>
    if h : u.val ≤ dist a b then ab.map ⟨u.val, ⟨u.property.1, h⟩⟩
    else bc.map ⟨u.val - dist a b, by constructor <;> linarith [u.property.2]⟩
  apply MetricSegment.of_short_map f
  · intro u v
    have ordered (u v : Set.Icc (0 : ℝ) (dist a c)) (huv : u.val ≤ v.val) :
        dist (f u) (f v) ≤ dist u v := by
      have hd : dist u v = v.val - u.val := by
        change |u.val - v.val| = _
        rw [abs_of_nonpos (sub_nonpos.mpr huv)]
        ring
      rw [hd]
      by_cases hu : u.val ≤ dist a b
      · by_cases hv : v.val ≤ dist a b
        · simp only [f, dif_pos hu, dif_pos hv]
          rw [ab.isometry.dist_eq]
          change |u.val - v.val| ≤ _
          rw [abs_of_nonpos (sub_nonpos.mpr huv)]
          linarith
        · simp only [f, dif_pos hu, dif_neg hv]
          have h := dist_triangle (ab.map ⟨u.val, ⟨u.property.1, hu⟩⟩) b
            (bc.map ⟨v.val - dist a b, by constructor <;> linarith [v.property.2]⟩)
          rw [ab.dist_finish, bc.dist_start] at h
          linarith
      · have hv : ¬ v.val ≤ dist a b := by linarith
        simp only [f, dif_neg hu, dif_neg hv]
        rw [bc.isometry.dist_eq]
        change |(u.val - dist a b) - (v.val - dist a b)| ≤ _
        rw [show (u.val - dist a b) - (v.val - dist a b) = u.val - v.val by ring,
          abs_of_nonpos (sub_nonpos.mpr huv)]
        linarith
    rcases le_total u.val v.val with h | h
    · exact ordered u v h
    · simpa only [dist_comm] using ordered v u h
  · simpa only [f, dif_pos dist_nonneg] using ab.start
  · by_cases h : dist a c ≤ dist a b
    · have hbc : b = c := dist_eq_zero.mp (by linarith [dist_nonneg (x := b) (y := c)])
      have hac : dist a c = dist a b := by simp [← hbc]
      simpa only [f, dif_pos h, hac, dif_pos le_rfl] using ab.finish.trans hbc
    · simp only [f, dif_neg h]
      have he : (⟨dist a c - dist a b, by constructor <;> linarith⟩ :
          Set.Icc (0 : ℝ) (dist b c)) = ⟨dist b c, ⟨dist_nonneg, le_rfl⟩⟩ :=
        Subtype.ext (by linarith)
      exact (congrArg bc.map he).trans bc.finish

end RayBundle

-- Source: RayBundle.Def_Cayley_MetricSegment_constant
namespace RayBundle

/-- The zero-length segment at a point. -/
def MetricSegment.constant {X : Type*} [MetricSpace X] (a : X) : MetricSegment a a where
  map := fun _ => a
  isometry := Isometry.of_dist_eq fun u v => by
    have hu : u.val = 0 := (by simpa using u.property.2 : u.val ≤ 0).antisymm u.property.1
    have hv : v.val = 0 := (by simpa using v.property.2 : v.val ≤ 0).antisymm v.property.1
    change dist a a = |u.val - v.val|
    simp [hu, hv]
  start := rfl
  finish := rfl

end RayBundle

-- Source: RayBundle.Def_Cayley_MetricSegment_of_interval_isometry
namespace RayBundle

/-- Any two points of an isometric real interval are joined by its subinterval. -/
noncomputable def MetricSegment.of_interval_isometry {X : Type*} [MetricSpace X]
    {L : ℝ} (f : Set.Icc (0 : ℝ) L → X) (hf : Isometry f)
    (s t : Set.Icc (0 : ℝ) L) : MetricSegment (f s) (f t) := by
  have hd : dist (f s) (f t) = |s.val - t.val| := hf.dist_eq s t
  let g : Set.Icc (0 : ℝ) (dist (f s) (f t)) → Set.Icc (0 : ℝ) L :=
    fun u => if h : s.val ≤ t.val then
      ⟨s.val + u.val, by
        constructor
        · linarith [s.property.1, u.property.1]
        · have hu := u.property.2
          simp only [hd, abs_of_nonpos (sub_nonpos.mpr h)] at hu
          linarith [t.property.2]⟩
    else
      ⟨s.val - u.val, by
        constructor
        · have hu := u.property.2
          simp only [hd, abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge h))] at hu
          linarith [t.property.1]
        · linarith [s.property.2, u.property.1]⟩
  have hg : Isometry g := by
    apply Isometry.of_dist_eq
    intro u v
    by_cases h : s.val ≤ t.val
    · change |(g u).val - (g v).val| = |u.val - v.val|
      simp only [g, dif_pos h]
      congr 1
      ring
    · change |(g u).val - (g v).val| = |u.val - v.val|
      simp only [g, dif_neg h]
      rw [show s.val - u.val - (s.val - v.val) = -(u.val - v.val) by ring, abs_neg]
  refine ⟨f ∘ g, hf.comp hg, ?_, ?_⟩
  · apply congrArg f
    apply Subtype.ext
    by_cases h : s.val ≤ t.val <;> simp [g, h]
  · apply congrArg f
    apply Subtype.ext
    by_cases h : s.val ≤ t.val
    · simp [g, h, hd, abs_of_nonpos (sub_nonpos.mpr h)]
    · simp [g, h, hd, abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge h))]

end RayBundle

-- Source: RayBundle.Def_Cayley_MetricSegment_reverse
namespace RayBundle

/-- Traverse a geodesic segment in the opposite direction. -/
noncomputable def MetricSegment.reverse {X : Type*} [MetricSpace X] {a b : X}
    (c : MetricSegment a b) : MetricSegment b a := by
  have s := MetricSegment.of_interval_isometry c.map c.isometry
    ⟨dist a b, ⟨dist_nonneg, le_rfl⟩⟩ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩
  simpa only [c.finish, c.start] using s

end RayBundle

-- Source: RayBundle.Def_Cayley_MetricSegment_toPath
namespace RayBundle

/-- Normalize an arc-length segment to a continuous path on the unit interval. -/
noncomputable def MetricSegment.toPath {X : Type*} [MetricSpace X] {a b : X}
    (c : MetricSegment a b) : _root_.Path a b := by
  let f : unitInterval → Set.Icc (0 : ℝ) (dist a b) := fun u =>
    ⟨dist a b * u.val, by
      constructor
      · exact mul_nonneg dist_nonneg u.property.1
      · nlinarith [u.property.2, dist_nonneg (x := a) (y := b)]⟩
  have hf : Continuous f := by dsimp [f]; fun_prop
  refine
    { toFun := c.map ∘ f
      continuous_toFun := c.isometry.continuous.comp hf
      source' := ?_
      target' := ?_ }
  · have h : f 0 = ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ := Subtype.ext (by simp [f])
    exact (congrArg c.map h).trans c.start
  · have h : f 1 = ⟨dist a b, ⟨dist_nonneg, le_rfl⟩⟩ := Subtype.ext (by simp [f])
    exact (congrArg c.map h).trans c.finish

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

-- Source: RayBundle.Thm_Cayley_UnitEdgeRealization_stage_range_mono
namespace RayBundle

universe u

theorem UnitEdgeRealization.stage_range_mono {V : Type u} [MetricSpace V]
    (a b : ℕ → V) (hab : ∀ n, dist (a n) (b n) = 1) :
    Monotone (fun n => Set.range
      (Metric.toInductiveLimit (UnitEdgeStage.sequenceStep_isometry a b hab) n)) := by
  apply monotone_nat_of_le_succ
  intro n p hp
  obtain ⟨x, rfl⟩ := hp
  exact ⟨UnitEdgeStage.sequenceStep a b hab n x,
    congrFun (Metric.toInductiveLimit_commute (UnitEdgeStage.sequenceStep_isometry a b hab) n) x⟩

end RayBundle

-- Source: RayBundle.Thm_Cayley_UnitEdgeRealization_edge_dist_of_lt
namespace RayBundle

/-- Distinct edges communicate through an endpoint of the later attachment. -/
theorem UnitEdgeRealization.edge_dist_of_lt {V : Type*} [MetricSpace V]
    (a b : ℕ → V) (hab : ∀ n, dist (a n) (b n) = 1) {n m : ℕ} (hnm : n < m)
    (s t : Set.Icc (0 : ℝ) 1) :
    dist (edge a b hab m t) (edge a b hab n s) =
      min (t.val + dist (vertex a b hab (a m)) (edge a b hab n s))
        (1 - t.val + dist (vertex a b hab (b m)) (edge a b hab n s)) := by
  let En := (UnitEdgeStage.sequence a b hab n).attach (a n) (b n) (hab n)
  have hn : edge a b hab n s ∈ Set.range
      (Metric.toInductiveLimit (UnitEdgeStage.sequenceStep_isometry a b hab) (n + 1)) :=
    ⟨En.edge s, rfl⟩
  obtain ⟨x, hx⟩ := stage_range_mono a b hab (Nat.succ_le_of_lt hnm) hn
  let A := UnitEdgeStage.sequence a b hab m
  let E := A.attach (a m) (b m) (hab m)
  have hi := Metric.toInductiveLimit_isometry (UnitEdgeStage.sequenceStep_isometry a b hab) (m + 1)
  have hv : Metric.toInductiveLimit (UnitEdgeStage.sequenceStep_isometry a b hab) (m + 1)
      (E.old x) = edge a b hab n s :=
    (congrFun (Metric.toInductiveLimit_commute
      (UnitEdgeStage.sequenceStep_isometry a b hab) m) x).trans hx
  have hvertex (v : V) : dist (A.vertex v) x =
      dist (vertex a b hab v) (edge a b hab n s) := by
    rw [← vertex_at_stage a b hab m v, ← hx]
    exact (Metric.toInductiveLimit_isometry
      (UnitEdgeStage.sequenceStep_isometry a b hab) m).dist_eq _ _ |>.symm
  calc
    _ = dist (E.edge t) (E.old x) := by rw [← hv]; exact hi.dist_eq _ _
    _ = min (t.val + dist (A.vertex (a m)) x) (1 - t.val + dist (A.vertex (b m)) x) :=
      A.attach_edge_old_dist (a m) (b m) (hab m) t x
    _ = _ := by rw [hvertex, hvertex]

end RayBundle

-- Source: RayBundle.Thm_Cayley_GraphRealization_edge_dist_of_lt
namespace RayBundle

theorem GraphRealization.edge_dist_of_lt {V : Type*} (T : SimpleGraph V)
    (hT : T.Connected) (e : ℕ ≃ T.edgeSet) {n m : ℕ} (hnm : n < m)
    (s t : Set.Icc (0 : ℝ) 1) :
    dist (edge T hT e m t) (edge T hT e n s) =
      min (t.val + dist (vertex T hT e (graphEdgePair T e m).1) (edge T hT e n s))
        (1 - t.val + dist (vertex T hT e (graphEdgePair T e m).2) (edge T hT e n s)) := by
  let := connectedGraphMetric T hT
  exact UnitEdgeRealization.edge_dist_of_lt _ _ _ hnm s t

end RayBundle

-- Source: RayBundle.Thm_Cayley_MetricSegment_exists_of_endpoint_formula
namespace RayBundle

/-- Join an interval point through whichever endpoint attains the distance. -/
theorem MetricSegment.exists_of_endpoint_formula {X : Type*} [MetricSpace X]
    (f : Set.Icc (0 : ℝ) 1 → X) (hf : Isometry f) (t : Set.Icc (0 : ℝ) 1) (x : X)
    (hzero : Nonempty (MetricSegment (f ⟨0, by simp⟩) x))
    (hone : Nonempty (MetricSegment (f ⟨1, by simp⟩) x))
    (hd : dist (f t) x =
      min (t.val + dist (f ⟨0, by simp⟩) x) (1 - t.val + dist (f ⟨1, by simp⟩) x)) :
    Nonempty (MetricSegment (f t) x) := by
  have h0 : dist (f t) (f ⟨0, by simp⟩) = t.val := by
    rw [hf.dist_eq]
    change |t.val - 0| = _
    simp [abs_of_nonneg t.property.1]
  have h1 : dist (f t) (f ⟨1, by simp⟩) = 1 - t.val := by
    rw [hf.dist_eq]
    change |t.val - 1| = _
    rw [abs_of_nonpos (sub_nonpos.mpr t.property.2)]
    ring
  rcases le_total (t.val + dist (f ⟨0, by simp⟩) x)
      (1 - t.val + dist (f ⟨1, by simp⟩) x) with h | h
  · obtain ⟨c⟩ := hzero
    refine ⟨(MetricSegment.of_interval_isometry f hf t ⟨0, by simp⟩).append c ?_⟩
    rw [h0, hd, min_eq_left h]
  · obtain ⟨c⟩ := hone
    refine ⟨(MetricSegment.of_interval_isometry f hf t ⟨1, by simp⟩).append c ?_⟩
    rw [h1, hd, min_eq_right h]

end RayBundle

-- Source: RayBundle.Thm_Cayley_GraphRealization_vertex_dist
namespace RayBundle

universe u

theorem GraphRealization.vertex_dist {V : Type u} (T : SimpleGraph V)
    (hT : T.Connected) (e : ℕ ≃ T.edgeSet) (v w : V) :
    dist (vertex T hT e v) (vertex T hT e w) = (T.dist v w : ℝ) := by
  let := connectedGraphMetric T hT
  exact (UnitEdgeRealization.vertex_isometry _ _ _).dist_eq v w

end RayBundle

-- Source: RayBundle.Thm_Cayley_GraphRealization_vertex_segment
namespace RayBundle

/-- Interpolate a shortest graph walk to join any two realized vertices. -/
theorem GraphRealization.vertex_segment {V : Type*} (T : SimpleGraph V)
    (hT : T.Connected) (e : ℕ ≃ T.edgeSet) (a b : V) :
    Nonempty (MetricSegment (vertex T hT e a) (vertex T hT e b)) := by
  obtain ⟨w, hw⟩ := hT.exists_walk_length_eq_dist a b
  induction w with
  | nil => exact ⟨MetricSegment.constant _⟩
  | @cons a v b hadj w ih =>
    have hw' := SimpleGraph.length_eq_dist_of_subwalk hw (w.isSubwalk_cons hadj)
    obtain ⟨vb⟩ := ih hw'
    let E := orientedEdge T hT e a v hadj
    have av : MetricSegment (vertex T hT e a) (vertex T hT e v) := by
      simpa only [E.zero, E.one] using
        MetricSegment.of_interval_isometry E.map E.isometry ⟨0, by simp⟩ ⟨1, by simp⟩
    refine ⟨av.append vb ?_⟩
    rw [vertex_dist, vertex_dist, vertex_dist, T.dist_eq_one_iff_adj.mpr hadj]
    have hlen : 1 + T.dist v b = T.dist a b := by
      simpa [SimpleGraph.Walk.length_cons, hw', Nat.add_comm] using hw
    exact_mod_cast hlen

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

-- Source: RayBundle.Thm_Cayley_GraphRealization_edge_vertex_segment
namespace RayBundle

/-- An edge point and an arbitrary graph vertex admit a geodesic. -/
theorem GraphRealization.edge_vertex_segment {V : Type*} (T : SimpleGraph V)
    (hT : T.Connected) (e : ℕ ≃ T.edgeSet) (n : ℕ)
    (t : Set.Icc (0 : ℝ) 1) (v : V) :
    Nonempty (MetricSegment (edge T hT e n t) (vertex T hT e v)) := by
  apply MetricSegment.exists_of_endpoint_formula (edge T hT e n)
    (edge_isometry T hT e n) t (vertex T hT e v)
  · rw [edge_zero]
    exact vertex_segment T hT e _ v
  · rw [edge_one]
    exact vertex_segment T hT e _ v
  · rw [edge_zero, edge_one, vertex_dist, vertex_dist]
    exact edge_vertex_dist T hT e n t v

end RayBundle

-- Source: RayBundle.Thm_Cayley_GraphRealization_edge_segment_of_lt
namespace RayBundle

/-- Two distinct edge points are joined through an endpoint of the later edge. -/
theorem GraphRealization.edge_segment_of_lt {V : Type*} (T : SimpleGraph V)
    (hT : T.Connected) (e : ℕ ≃ T.edgeSet) {n m : ℕ} (hnm : n < m)
    (s t : Set.Icc (0 : ℝ) 1) :
    Nonempty (MetricSegment (edge T hT e m t) (edge T hT e n s)) := by
  apply MetricSegment.exists_of_endpoint_formula (edge T hT e m)
    (edge_isometry T hT e m) t (edge T hT e n s)
  · rw [edge_zero]
    obtain ⟨c⟩ := edge_vertex_segment T hT e n s (graphEdgePair T e m).1
    exact ⟨c.reverse⟩
  · rw [edge_one]
    obtain ⟨c⟩ := edge_vertex_segment T hT e n s (graphEdgePair T e m).2
    exact ⟨c.reverse⟩
  · rw [edge_zero, edge_one]
    exact edge_dist_of_lt T hT e hnm s t

end RayBundle

-- Source: RayBundle.Thm_Cayley_GraphRealization_exists_segment
namespace RayBundle

/-- Every pair of points of the connected unit-edge realization admits a geodesic. -/
theorem GraphRealization.exists_segment {V : Type*} (T : SimpleGraph V)
    (hT : T.Connected) (e : ℕ ≃ T.edgeSet) (p q : GraphRealization T hT e) :
    Nonempty (MetricSegment p q) := by
  rcases covered T hT e p with ⟨v, rfl⟩ | ⟨n, s, rfl⟩
  · rcases covered T hT e q with ⟨w, rfl⟩ | ⟨m, t, rfl⟩
    · exact vertex_segment T hT e v w
    · obtain ⟨c⟩ := edge_vertex_segment T hT e m t v
      exact ⟨c.reverse⟩
  · rcases covered T hT e q with ⟨w, rfl⟩ | ⟨m, t, rfl⟩
    · exact edge_vertex_segment T hT e n s w
    · rcases lt_trichotomy n m with h | h | h
      · obtain ⟨c⟩ := edge_segment_of_lt T hT e h s t
        exact ⟨c.reverse⟩
      · subst m
        exact ⟨MetricSegment.of_interval_isometry (edge T hT e n)
          (edge_isometry T hT e n) s t⟩
      · exact edge_segment_of_lt T hT e h t s

end RayBundle

-- Source: RayBundle.Thm_Cayley_edist_le_metricPathLength
namespace RayBundle

/-- Every continuous path has length at least the distance between its endpoints. -/
theorem edist_le_metricPathLength {X : Type*} [PseudoEMetricSpace X] {a b : X}
    (γ : _root_.Path a b) : edist a b ≤ metricPathLength γ := by
  simpa only [metricPathLength, γ.source, γ.target] using
    eVariationOn.edist_le γ (Set.mem_univ (0 : unitInterval))
      (Set.mem_univ (1 : unitInterval))

end RayBundle

-- Source: RayBundle.Thm_Cayley_edist_le_intrinsicEDist
namespace RayBundle

theorem edist_le_intrinsicEDist {X : Type*} [PseudoEMetricSpace X] (a b : X) :
    edist a b ≤ intrinsicEDist a b :=
  le_iInf fun γ => edist_le_metricPathLength γ

end RayBundle

-- Source: RayBundle.Thm_Cayley_MetricSegment_toPath_dist
namespace RayBundle

theorem MetricSegment.toPath_dist {X : Type*} [MetricSpace X] {a b : X}
    (c : MetricSegment a b) (s t : unitInterval) :
    dist (c.toPath s) (c.toPath t) = dist a b * dist s t := by
  change dist (c.map _) (c.map _) = _
  rw [c.isometry.dist_eq]
  change |dist a b * s.val - dist a b * t.val| = dist a b * |s.val - t.val|
  rw [← mul_sub, abs_mul, abs_of_nonneg dist_nonneg]

end RayBundle

-- Source: RayBundle.Thm_Cayley_eVariationOn_eq_of_edist_eq
namespace RayBundle

/-- Variation depends only on pairwise distances on the parameter set. -/
theorem eVariationOn_eq_of_edist_eq {α E F : Type*} [LinearOrder α]
    [PseudoEMetricSpace E] [PseudoEMetricSpace F] (f : α → E) (g : α → F) (s : Set α)
    (h : ∀ x ∈ s, ∀ y ∈ s, edist (f x) (f y) = edist (g x) (g y)) :
    eVariationOn f s = eVariationOn g s := by
  unfold eVariationOn
  apply iSup_congr
  intro p
  apply Finset.sum_congr rfl
  intro i _
  exact h _ (p.2.property.2 _) _ (p.2.property.2 _)

end RayBundle

-- Source: RayBundle.Thm_Cayley_MetricSegment_toPath_length
namespace RayBundle

/-- The normalized path attains the endpoint distance, also for a zero-length segment. -/
theorem MetricSegment.toPath_length {X : Type*} [MetricSpace X] {a b : X}
    (c : MetricSegment a b) : metricPathLength c.toPath = edist a b := by
  let f : unitInterval → ℝ := fun u => dist a b * u.val
  have hp (s t : unitInterval) : edist (c.toPath s) (c.toPath t) = edist (f s) (f t) := by
    rw [edist_dist, edist_dist, c.toPath_dist]
    congr 1
    change dist a b * |s.val - t.val| = |dist a b * s.val - dist a b * t.val|
    rw [← mul_sub, abs_mul, abs_of_nonneg dist_nonneg]
  change eVariationOn c.toPath Set.univ = _
  rw [eVariationOn_eq_of_edist_eq c.toPath f Set.univ (fun s _ t _ => hp s t)]
  have hm : MonotoneOn f Set.univ := fun s _ t _ h =>
    mul_le_mul_of_nonneg_left h dist_nonneg
  have hv := hm.eVariationOn_eq (a := (0 : unitInterval)) (b := (1 : unitInterval))
    (Set.mem_univ _) (Set.mem_univ _)
  simpa [f, ← unitInterval.univ_eq_Icc, edist_dist] using hv

end RayBundle

-- Source: RayBundle.Thm_Cayley_intrinsicEDist_eq_of_segment
namespace RayBundle

/-- A geodesic makes the metric distance equal to the intrinsic path distance. -/
theorem intrinsicEDist_eq_of_segment {X : Type*} [MetricSpace X] {a b : X}
    (c : MetricSegment a b) : intrinsicEDist a b = edist a b := by
  apply le_antisymm _ (edist_le_intrinsicEDist a b)
  exact (iInf_le (fun γ : _root_.Path a b => metricPathLength γ) c.toPath).trans_eq
    c.toPath_length

end RayBundle

-- Source: RayBundle.Thm_Cayley_GraphRealization_intrinsicEDist_eq
namespace RayBundle

end RayBundle

open RayBundle
universe u
/-- The glued metric equals the intrinsic metric from all continuous paths. -/
theorem solution {V : Type*} (T : SimpleGraph V)
    (hT : T.Connected) (e : ℕ ≃ T.edgeSet) (p q : RayBundle.GraphRealization T hT e) :
    RayBundle.intrinsicEDist p q = edist p q := by
  obtain ⟨c⟩ := RayBundle.GraphRealization.exists_segment T hT e p q
  exact RayBundle.intrinsicEDist_eq_of_segment c

namespace RayBundle


end RayBundle
