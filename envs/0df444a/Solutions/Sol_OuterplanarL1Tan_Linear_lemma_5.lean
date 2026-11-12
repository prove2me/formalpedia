-- Prove2me | solution 1 for OuterplanarL1Tan.Linear.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:58:03.198016+00:00
-- url     : https://prove2.me/submissions/1c9e13ed-8fd5-4197-a61a-96198f89a2c5

import Mathlib
import Definitions.Def_OuterplanarL1Tan_Linear_BoundaryPattern
import Theorems.Thm_OuterplanarL1Tan_Linear_lemma_2

section
set_option autoImplicit false

namespace OuterplanarL1Tan.Dev.Dist

open OuterplanarL1Tan.Linear

theorem walkLength_append {V : Type} {G : SimpleGraph V} (length : V → V → ℝ)
    {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    OAI.PlanarL1.walkLength length (p.append q) =
      OAI.PlanarL1.walkLength length p + OAI.PlanarL1.walkLength length q := by
  induction p with
  | nil => simp [OAI.PlanarL1.walkLength]
  | cons h p ih =>
    simp only [SimpleGraph.Walk.cons_append, OAI.PlanarL1.walkLength, ih]
    ring

theorem walkLength_nonneg {V : Type} (W : WeightedGraph V) {u v : V}
    (p : W.graph.Walk u v) : 0 ≤ OAI.PlanarL1.walkLength W.length p := by
  induction p with
  | nil => simp [OAI.PlanarL1.walkLength]
  | cons h p ih =>
    simp only [OAI.PlanarL1.walkLength]
    exact add_nonneg (W.nonnegative _ _ h) ih

theorem walkLength_reverse {V : Type} (W : WeightedGraph V) {u v : V}
    (p : W.graph.Walk u v) :
    OAI.PlanarL1.walkLength W.length p.reverse = OAI.PlanarL1.walkLength W.length p := by
  induction p with
  | nil => simp [OAI.PlanarL1.walkLength]
  | cons h p ih =>
    rename_i a b c
    rw [SimpleGraph.Walk.reverse_cons, walkLength_append]
    simp only [OAI.PlanarL1.walkLength, ih]
    rw [W.symmetric b a]
    ring

theorem dist_nonneg {V : Type} (W : WeightedGraph V) (u v : V) : 0 ≤ W.distance u v := by
  unfold WeightedGraph.distance OAI.PlanarL1.graphDistance
  apply Real.sInf_nonneg
  rintro _ ⟨p, rfl⟩
  exact walkLength_nonneg W p

theorem dist_le_walk {V : Type} (W : WeightedGraph V) {u v : V} (p : W.graph.Walk u v) :
    W.distance u v ≤ OAI.PlanarL1.walkLength W.length p := by
  unfold WeightedGraph.distance OAI.PlanarL1.graphDistance
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨q, rfl⟩
    exact walkLength_nonneg W q
  · exact ⟨p, rfl⟩

theorem dist_comm {V : Type} (W : WeightedGraph V) (u v : V) :
    W.distance u v = W.distance v u := by
  have h : ∀ a b : V, W.distance a b ≤ W.distance b a := by
    intro a b
    by_cases hne : Nonempty (W.graph.Walk a b)
    · obtain ⟨q⟩ := hne
      unfold WeightedGraph.distance OAI.PlanarL1.graphDistance
      have hne2 : (Set.range fun p : W.graph.Walk b a => OAI.PlanarL1.walkLength W.length p).Nonempty := ⟨_, Set.mem_range_self q.reverse⟩
      apply le_csInf hne2
      rintro _ ⟨p, rfl⟩
      have := dist_le_walk W p.reverse
      rw [walkLength_reverse] at this
      exact this
    · have : IsEmpty (W.graph.Walk a b) := not_nonempty_iff.mp hne
      have h0 : W.distance a b = 0 := by
        unfold WeightedGraph.distance OAI.PlanarL1.graphDistance
        rw [Set.range_eq_empty]; exact Real.sInf_empty
      rw [h0]; exact dist_nonneg W b a
  exact le_antisymm (h u v) (h v u)

theorem dist_triangle {V : Type} (W : WeightedGraph V) (hr : W.FiniteDistances)
    (u v w : V) : W.distance u w ≤ W.distance u v + W.distance v w := by
  obtain ⟨p0⟩ := hr u v
  obtain ⟨q0⟩ := hr v w
  haveI : Nonempty (W.graph.Walk u v) := ⟨p0⟩
  haveI : Nonempty (W.graph.Walk v w) := ⟨q0⟩
  have key : ∀ p : W.graph.Walk u v, ∀ q : W.graph.Walk v w,
      W.distance u w ≤ OAI.PlanarL1.walkLength W.length p +
        OAI.PlanarL1.walkLength W.length q := by
    intro p q
    have := dist_le_walk W (p.append q)
    rwa [walkLength_append] at this
  have h1 : ∀ p : W.graph.Walk u v, W.distance u w - OAI.PlanarL1.walkLength W.length p
      ≤ W.distance v w := by
    intro p
    unfold WeightedGraph.distance OAI.PlanarL1.graphDistance
    apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨q, rfl⟩
    have := key p q
    unfold WeightedGraph.distance OAI.PlanarL1.graphDistance at this
    linarith
  have h2 : W.distance u w - W.distance v w ≤ W.distance u v := by
    unfold WeightedGraph.distance OAI.PlanarL1.graphDistance
    apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨p, rfl⟩
    have := h1 p
    unfold WeightedGraph.distance OAI.PlanarL1.graphDistance at this
    linarith
  linarith

end OuterplanarL1Tan.Dev.Dist
end

section
set_option autoImplicit false

namespace OuterplanarL1Tan.Dev.L5

open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.Dist

theorem l1norm {ι : Type} [Fintype ι] (f g : ι → ℝ) :
    ‖WithLp.toLp 1 f - WithLp.toLp 1 g‖ = ∑ i, |f i - g i| := by
  rw [← WithLp.toLp_sub, PiLp.norm_eq_of_nat 1 (by norm_num)]
  simp

theorem pat_norm {V : Type} [Fintype V] (W : WeightedGraph V) (D : PlaneDrawing W.graph)
    (B : OuterFacialWalk D) (x y : V) :
    ‖pattern W D B x - pattern W D B y‖ = ∑ j, |(W.distance x (B.vertex j) -
      W.distance x (B.vertex (cyclicNext B.positive j))) -
      (W.distance y (B.vertex j) - W.distance y (B.vertex (cyclicNext B.positive j)))| := by
  unfold pattern
  rw [l1norm]

theorem aug_norm {V : Type} [Fintype V] (W : WeightedGraph V) (D : PlaneDrawing W.graph)
    (B : OuterFacialWalk D) (x y : V) :
    ‖augmented W D B x - augmented W D B y‖ =
      (1 / 4) * ‖pattern W D B x - pattern W D B y‖ +
        2 * |boundaryDistance W D x - boundaryDistance W D y| := by
  unfold augmented
  rw [l1norm, Fintype.sum_sum_type, pat_norm]
  simp only [Sum.elim_inl, Sum.elim_inr, Finset.univ_unique, Finset.sum_singleton]
  rw [Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    rw [← mul_sub, abs_mul]
    norm_num
    rfl
  · rw [← mul_sub, abs_mul]; norm_num

theorem bd_attained {V : Type} [Fintype V] (W : WeightedGraph V) (D : PlaneDrawing W.graph)
    (B : OuterFacialWalk D) (z : V) :
    ∃ a ∈ D.boundary Set.univ, W.distance z a = boundaryDistance W D z ∧
      ∀ b ∈ D.boundary Set.univ, boundaryDistance W D z ≤ W.distance z b := by
  have hS : {r : ℝ | ∃ b ∈ D.boundary Set.univ, r = W.distance z b} =
      (fun b => W.distance z b) '' D.boundary Set.univ := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, rfl⟩
    · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, rfl⟩
  have hne : (D.boundary Set.univ).Nonempty := by
    refine ⟨B.vertex ⟨0, B.positive⟩, ?_⟩
    rw [← B.covers_boundary]
    exact Set.mem_range_self _
  have hfin : ((fun b => W.distance z b) '' D.boundary Set.univ).Finite :=
    Set.Finite.image _ (Set.toFinite _)
  have hne' : ((fun b => W.distance z b) '' D.boundary Set.univ).Nonempty := hne.image _
  unfold boundaryDistance
  rw [hS]
  obtain ⟨a, ha, hab⟩ := hne'.csInf_mem hfin
  refine ⟨a, ha, hab, ?_⟩
  intro b hb
  exact csInf_le hfin.bddBelow ⟨b, hb, rfl⟩

theorem half {V : Type} [Fintype V] (W : WeightedGraph V) (reachable : W.FiniteDistances)
    (D : PlaneDrawing W.graph) (B : OuterFacialWalk D) (x y : V)
    (hxy : boundaryDistance W D x ≤ boundaryDistance W D y) :
    W.distance x y - 4 * boundaryDistance W D x ≤
      ‖augmented W D B x - augmented W D B y‖ := by
  obtain ⟨a, ha, hxa, -⟩ := bd_attained W D B x
  obtain ⟨b, hb, hyb, -⟩ := bd_attained W D B y
  obtain ⟨h1, h2⟩ := lemma_2 W reachable D B
  have e1 := h1 x a
  have e2 := h1 y b
  have e3 := h2 a b ha hb
  have tri : ‖pattern W D B a - pattern W D B b‖ ≤ ‖pattern W D B a - pattern W D B x‖ +
      ‖pattern W D B x - pattern W D B y‖ + ‖pattern W D B y - pattern W D B b‖ := by
    have : pattern W D B a - pattern W D B b =
        (pattern W D B a - pattern W D B x) + (pattern W D B x - pattern W D B y) +
          (pattern W D B y - pattern W D B b) := by abel
    rw [this]
    exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
  rw [norm_sub_rev (pattern W D B a) (pattern W D B x)] at tri
  have t1 := dist_triangle W reachable x a y
  have t2 := dist_triangle W reachable a b y
  have c1 := dist_comm W a y
  have c2 := dist_comm W b y
  rw [aug_norm]
  have hab' : |boundaryDistance W D x - boundaryDistance W D y| =
      boundaryDistance W D y - boundaryDistance W D x := by
    rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
  rw [hab']
  rw [hxa] at e1
  rw [hyb] at e2
  rw [dist_comm W y b] at hyb
  linarith [dist_comm W b y, dist_comm W a b]

end OuterplanarL1Tan.Dev.L5

namespace OuterplanarL1Tan.Linear

theorem chk_lemma_5 {V : Type} [Fintype V] (W : WeightedGraph V)
    (reachable : W.FiniteDistances) (D : PlaneDrawing W.graph)
    (B : OuterFacialWalk D) (x y : V) :
    W.distance x y - 4 * min (boundaryDistance W D x) (boundaryDistance W D y) ≤
      ‖augmented W D B x - augmented W D B y‖ := by
  rcases le_total (boundaryDistance W D x) (boundaryDistance W D y) with h | h
  · rw [min_eq_left h]
    exact OuterplanarL1Tan.Dev.L5.half W reachable D B x y h
  · rw [min_eq_right h, OuterplanarL1Tan.Dev.Dist.dist_comm W x y, norm_sub_rev]
    exact OuterplanarL1Tan.Dev.L5.half W reachable D B y x h

end OuterplanarL1Tan.Linear
end

theorem solution : type_of% @OuterplanarL1Tan.Linear.chk_lemma_5 := @OuterplanarL1Tan.Linear.chk_lemma_5
