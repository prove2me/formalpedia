-- Prove2me | solution 1 for OuterplanarL1Tan.Linear.claim_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T20:43:54.555007+00:00
-- url     : https://prove2.me/submissions/678f5899-2761-4043-84db-8a237d3d30bd

import Mathlib
import Definitions.Def_OuterplanarL1Tan_Linear_BoundaryPattern
import Theorems.Thm_JordanCurve_jordan_curve_theorem
import Theorems.Thm_JordanCurve_euclidean_unit_circle_loop
import Theorems.Thm_Plasticity_Topology_isOpen_image_of_injOn_of_finrank_eq
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
namespace OuterplanarL1Tan.Dev.C3.PartA
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.Dist
/-! ## Combinatorics: four alternating visits -/
theorem alt_finish {n : ℕ} (b : Fin n → Prop) (p5 p6 i1 i2 : Fin n)
    (h6 : p5.val < p6.val ∨ p6.val = 0) (d3 : ¬ (b p5 ↔ b p6))
    (hi12 : i1.val < i2.val) (hi2 : i2.val < p5.val)
    (hb1 : b i1 ↔ b p5) (hb2 : ¬ (b i1 ↔ b i2)) :
    ∃ j1 j2 j3 j4 : Fin n, j1 < j2 ∧ j2 < j3 ∧ (j4 < j1 ∨ j3 < j4) ∧
      (b j1 ↔ b j3) ∧ (b j2 ↔ b j4) ∧ ¬ (b j1 ↔ b j2) := by
  refine ⟨i1, i2, p5, p6, Fin.lt_def.mpr hi12, Fin.lt_def.mpr hi2, ?_, hb1, by tauto, hb2⟩
  rcases h6 with h6 | h6
  · exact Or.inr (Fin.lt_def.mpr h6)
  · left
    have hne : i1.val ≠ 0 := by
      intro h0
      have e : i1 = p6 := Fin.ext (by omega)
      rw [e] at hb1
      exact d3 hb1.symm
    exact Fin.lt_def.mpr (by omega)

theorem alt_key {n : ℕ} (b : Fin n → Prop) (p1 p2 p3 p4 p5 p6 : Fin n)
    (h12 : p1.val < p2.val) (h23 : p2.val ≤ p3.val) (h34 : p3.val < p4.val)
    (h45 : p4.val ≤ p5.val) (h6 : p5.val < p6.val ∨ p6.val = 0)
    (d1 : ¬ (b p1 ↔ b p2)) (d2 : ¬ (b p3 ↔ b p4)) (d3 : ¬ (b p5 ↔ b p6)) :
    ∃ j1 j2 j3 j4 : Fin n, j1 < j2 ∧ j2 < j3 ∧ (j4 < j1 ∨ j3 < j4) ∧
      (b j1 ↔ b j3) ∧ (b j2 ↔ b j4) ∧ ¬ (b j1 ↔ b j2) := by
  by_cases c1 : (b p1 ↔ b p5)
  · exact alt_finish b p5 p6 p1 p2 h6 d3 h12 (by omega) c1 d1
  · have c1' : b p2 ↔ b p5 := by tauto
    by_cases c2 : p2.val = p3.val
    · have e : p2 = p3 := Fin.ext c2
      rw [← e] at d2
      have hne : p4.val ≠ p5.val := by
        intro he
        have e' : p4 = p5 := Fin.ext he
        rw [e'] at d2
        exact d2 c1'
      exact alt_finish b p5 p6 p2 p4 h6 d3 (by omega) (by omega) c1' d2
    · by_cases c3 : (b p3 ↔ b p5)
      · have hne : p4.val ≠ p5.val := by
          intro he
          have e' : p4 = p5 := Fin.ext he
          rw [e'] at d2
          exact d2 c3
        exact alt_finish b p5 p6 p2 p4 h6 d3 (by omega) (by omega) c1' (by tauto)
      · exact alt_finish b p5 p6 p2 p3 h6 d3 (by omega) (by omega) c1' (by tauto)

theorem cyclicNext_val_of_lt {m : ℕ} (hm : 0 < m) (j : Fin m) (h : j.val + 1 < m) :
    (cyclicNext hm j).val = j.val + 1 := by
  simp [cyclicNext, Nat.mod_eq_of_lt h]

theorem cyclicNext_val_cases {m : ℕ} (hm : 0 < m) (j : Fin m) :
    (cyclicNext hm j).val = j.val + 1 ∨ (cyclicNext hm j).val = 0 := by
  by_cases h : j.val + 1 < m
  · exact Or.inl (cyclicNext_val_of_lt hm j h)
  · right
    have : j.val + 1 = m := by omega
    simp [cyclicNext, this]

theorem alt_ordered {n : ℕ} (hn : 0 < n) (b : Fin n → Prop) (j1 j2 j3 : Fin n)
    (h12 : j1 < j2) (h23 : j2 < j3)
    (t1 : ¬ (b j1 ↔ b (cyclicNext hn j1))) (t2 : ¬ (b j2 ↔ b (cyclicNext hn j2)))
    (t3 : ¬ (b j3 ↔ b (cyclicNext hn j3))) :
    ∃ i1 i2 i3 i4 : Fin n, i1 < i2 ∧ i2 < i3 ∧ (i4 < i1 ∨ i3 < i4) ∧
      (b i1 ↔ b i3) ∧ (b i2 ↔ b i4) ∧ ¬ (b i1 ↔ b i2) := by
  rw [Fin.lt_def] at h12 h23
  have e1 := cyclicNext_val_of_lt hn j1 (by omega)
  have e2 := cyclicNext_val_of_lt hn j2 (by omega)
  have e3 := cyclicNext_val_cases hn j3
  exact alt_key b j1 (cyclicNext hn j1) j2 (cyclicNext hn j2) j3 (cyclicNext hn j3)
    (by omega) (by omega) (by omega) (by omega) (by omega) t1 t2 t3

theorem four_alternating {V : Type} {G : SimpleGraph V} (D : PlaneDrawing G)
    (B : OuterFacialWalk D) (A : Set V) (h : 3 ≤ transitionCount D B A) :
    ∃ i1 i2 i3 i4 : Fin B.size, i1 < i2 ∧ i2 < i3 ∧ (i4 < i1 ∨ i3 < i4) ∧
      (B.vertex i1 ∈ A ↔ B.vertex i3 ∈ A) ∧ (B.vertex i2 ∈ A ↔ B.vertex i4 ∈ A) ∧
      ¬ (B.vertex i1 ∈ A ↔ B.vertex i2 ∈ A) := by
  classical
  unfold transitionCount at h
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp (lt_of_lt_of_le (by norm_num) h)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hc
  have go := alt_ordered B.positive (fun j => B.vertex j ∈ A)
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hac with h2 | h2 <;>
    rcases lt_or_gt_of_ne hbc with h3 | h3
  · exact go a b c h1 h3 ha hb hc
  · exact go a c b h2 h3 ha hc hb
  · exact absurd (h1.trans h3) (not_lt.mpr h2.le)
  · exact go c a b h2 h1 hc ha hb
  · exact go b a c h1 h2 hb ha hc
  · exact absurd (h3.trans h1) (not_lt.mpr h2.le)
  · exact go b c a h3 h2 hb hc ha
  · exact go c b a h3 h1 hc hb ha

end OuterplanarL1Tan.Dev.C3.PartA
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.C3
open OuterplanarL1Tan.Linear
/-! ## Combinatorics -/
alias four_alternating := OuterplanarL1Tan.Dev.C3.PartA.four_alternating

end OuterplanarL1Tan.Dev.C3
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.C3.PartA
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.Dist
/-! ## Shortest walks and sublevel sets -/
theorem walkLength_bypass_le {V : Type} [DecidableEq V] (W : WeightedGraph V) {u v : V}
    (p : W.graph.Walk u v) :
    OAI.PlanarL1.walkLength W.length p.bypass ≤ OAI.PlanarL1.walkLength W.length p := by
  induction p with
  | nil => simp [SimpleGraph.Walk.bypass]
  | cons h p ih =>
    rename_i a b c
    have hl := W.nonnegative _ _ h
    simp only [SimpleGraph.Walk.bypass]
    split_ifs with hs
    · have e := congrArg (OAI.PlanarL1.walkLength W.length) (p.bypass.take_spec hs)
      rw [walkLength_append] at e
      have := walkLength_nonneg W (p.bypass.takeUntil a hs)
      simp only [OAI.PlanarL1.walkLength]
      linarith
    · simp only [OAI.PlanarL1.walkLength]
      linarith

theorem exists_min_walk {V : Type} [Fintype V] (W : WeightedGraph V)
    (hr : W.FiniteDistances) (u v : V) :
    ∃ p : W.graph.Walk u v, OAI.PlanarL1.walkLength W.length p = W.distance u v := by
  classical
  obtain ⟨q⟩ := hr u v
  obtain ⟨p0, -, hp0⟩ := Finset.exists_min_image Finset.univ
    (fun p : W.graph.Path u v => OAI.PlanarL1.walkLength W.length (p : W.graph.Walk u v))
    ⟨q.toPath, Finset.mem_univ _⟩
  refine ⟨p0, le_antisymm ?_ (dist_le_walk W _)⟩
  unfold WeightedGraph.distance OAI.PlanarL1.graphDistance
  apply le_csInf ⟨_, Set.mem_range_self q⟩
  rintro _ ⟨r, rfl⟩
  exact (hp0 r.toPath (Finset.mem_univ _)).trans (walkLength_bypass_le W r)

theorem split_le {V : Type} (W : WeightedGraph V) {z x : V} (p : W.graph.Walk z x)
    (hp : OAI.PlanarL1.walkLength W.length p = W.distance z x) (z' : V)
    (hz' : z' ∈ p.support) :
    W.distance z z' + W.distance z' x ≤ W.distance z x := by
  classical
  have e := congrArg (OAI.PlanarL1.walkLength W.length) (p.take_spec hz')
  rw [walkLength_append] at e
  have := dist_le_walk W (p.takeUntil z' hz')
  have := dist_le_walk W (p.dropUntil z' hz')
  linarith

theorem side_in {V : Type} [Fintype V] (W : WeightedGraph V)
    (hr : W.FiniteDistances) (x y : V) (t : ℝ) (z : V) (hz : z ∈ sublevel W x y t) :
    ∃ p : W.graph.Walk z x, ∀ z' ∈ p.support, z' ∈ sublevel W x y t := by
  obtain ⟨p, hp⟩ := exists_min_walk W hr z x
  refine ⟨p, fun z' hz' => ?_⟩
  have hs := split_le W p hp z' hz'
  have t1 := dist_triangle W hr y z' z
  have c1 := dist_comm W x z'
  have c2 := dist_comm W x z
  have c3 := dist_comm W z' z
  simp only [sublevel, Set.mem_ofPred_eq, differencePotential] at hz ⊢
  linarith

theorem side_out {V : Type} [Fintype V] (W : WeightedGraph V)
    (hr : W.FiniteDistances) (x y : V) (t : ℝ) (z : V) (hz : z ∉ sublevel W x y t) :
    ∃ p : W.graph.Walk z y, ∀ z' ∈ p.support, z' ∉ sublevel W x y t := by
  obtain ⟨p, hp⟩ := exists_min_walk W hr z y
  refine ⟨p, fun z' hz' => ?_⟩
  have hs := split_le W p hp z' hz'
  have t1 := dist_triangle W hr x z' z
  have c1 := dist_comm W y z'
  have c2 := dist_comm W y z
  have c3 := dist_comm W z' z
  simp only [sublevel, Set.mem_ofPred_eq, differencePotential, not_le] at hz ⊢
  linarith

theorem join_walks {V : Type} {G : SimpleGraph V} (P : V → Prop) {u w r : V}
    (p1 : G.Walk u r) (p2 : G.Walk w r) (h1 : ∀ z ∈ p1.support, P z)
    (h2 : ∀ z ∈ p2.support, P z) :
    ∃ p : G.Walk u w, p.IsPath ∧ ∀ z ∈ p.support, P z := by
  classical
  refine ⟨(p1.append p2.reverse).bypass, SimpleGraph.Walk.bypass_isPath _, fun z hz => ?_⟩
  have hz' := SimpleGraph.Walk.support_bypass_subset_support _ hz
  rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
    List.mem_reverse] at hz'
  rcases hz' with hz' | hz'
  · exact h1 z hz'
  · exact h2 z hz'

theorem same_class_path {V : Type} [Fintype V] (W : WeightedGraph V)
    (hr : W.FiniteDistances) (x y : V) (t : ℝ) (u w : V)
    (huw : u ∈ sublevel W x y t ↔ w ∈ sublevel W x y t) :
    ∃ p : W.graph.Walk u w, p.IsPath ∧
      ∀ z ∈ p.support, (z ∈ sublevel W x y t ↔ u ∈ sublevel W x y t) := by
  by_cases hu : u ∈ sublevel W x y t
  · obtain ⟨p1, h1⟩ := side_in W hr x y t u hu
    obtain ⟨p2, h2⟩ := side_in W hr x y t w (huw.mp hu)
    obtain ⟨p, hp, hs⟩ := join_walks (fun z => z ∈ sublevel W x y t) p1 p2 h1 h2
    exact ⟨p, hp, fun z hz => iff_of_true (hs z hz) hu⟩
  · obtain ⟨p1, h1⟩ := side_out W hr x y t u hu
    obtain ⟨p2, h2⟩ := side_out W hr x y t w (fun hw => hu (huw.mpr hw))
    obtain ⟨p, hp, hs⟩ := join_walks (fun z => z ∉ sublevel W x y t) p1 p2 h1 h2
    exact ⟨p, hp, fun z hz => iff_of_false (hs z hz) hu⟩

end OuterplanarL1Tan.Dev.C3.PartA
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.C3
open OuterplanarL1Tan.Linear
alias same_class_path := OuterplanarL1Tan.Dev.C3.PartA.same_class_path

end OuterplanarL1Tan.Dev.C3
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.C3.PartA
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.Dist
/-! ## Plane topology -/
theorem path_trans_injective {X : Type} [TopologicalSpace X] {a b c : X}
    (γ : Path a b) (γ' : Path b c)
    (h1 : Function.Injective γ) (h2 : Function.Injective γ')
    (h : ∀ p, p ∈ Set.range γ → p ∈ Set.range γ' → p = b) :
    Function.Injective (γ.trans γ') := by
  -- mixed case: `s ≤ 1/2 < t` is impossible
  have mixed : ∀ s t : unitInterval, (s : ℝ) ≤ 1 / 2 → ¬ (t : ℝ) ≤ 1 / 2 →
      (γ.trans γ') s ≠ (γ.trans γ') t := by
    intro s t hs ht heq
    rw [Path.trans_apply, Path.trans_apply, dif_pos hs, dif_neg ht] at heq
    have hb := h _ ⟨_, rfl⟩ ⟨_, heq.symm⟩
    have e2 : γ' ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩ = γ' 0 := by rw [← heq, hb, γ'.source]
    have := congrArg Subtype.val (h2 e2)
    simp only [Set.Icc.coe_zero] at this
    exact ht (by linarith)
  intro s t hst
  by_cases hs : (s : ℝ) ≤ 1 / 2 <;> by_cases ht : (t : ℝ) ≤ 1 / 2
  · rw [Path.trans_apply, Path.trans_apply, dif_pos hs, dif_pos ht] at hst
    have := congrArg Subtype.val (h1 hst)
    simp only at this
    exact Subtype.ext (by linarith)
  · exact absurd hst (mixed s t hs ht)
  · exact absurd hst.symm (mixed t s ht hs)
  · rw [Path.trans_apply, Path.trans_apply, dif_neg hs, dif_neg ht] at hst
    have := congrArg Subtype.val (h2 hst)
    simp only at this
    exact Subtype.ext (by linarith)

end OuterplanarL1Tan.Dev.C3.PartA
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.C3
open OuterplanarL1Tan.Linear
/-! ## Plane topology -/
alias path_trans_injective := OuterplanarL1Tan.Dev.C3.PartA.path_trans_injective

end OuterplanarL1Tan.Dev.C3
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.C3.PartA
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.Dist
/-- Injectivity of the closed loop `γ1.trans γ2`, up to identifying its endpoints. -/
theorem loop_inj {a b : ℝ × ℝ} (γ1 : Path a b) (γ2 : Path b a)
    (h1 : Function.Injective γ1) (h2 : Function.Injective γ2)
    (h : ∀ p, p ∈ Set.range γ1 → p ∈ Set.range γ2 → p = a ∨ p = b) :
    ∀ s t : unitInterval, (γ1.trans γ2) s = (γ1.trans γ2) t →
      s = t ∨ ((s : ℝ) = 0 ∧ (t : ℝ) = 1) ∨ ((s : ℝ) = 1 ∧ (t : ℝ) = 0) := by
  have mixed : ∀ s t : unitInterval, (s : ℝ) ≤ 1 / 2 → ¬ (t : ℝ) ≤ 1 / 2 →
      (γ1.trans γ2) s = (γ1.trans γ2) t → (s : ℝ) = 0 ∧ (t : ℝ) = 1 := by
    intro s t hs ht heq
    rw [Path.trans_apply, Path.trans_apply, dif_pos hs, dif_neg ht] at heq
    rcases h _ ⟨_, rfl⟩ ⟨_, heq.symm⟩ with hp | hp
    · have e1 : γ1 ⟨2 * s, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩ = γ1 0 := by rw [hp, γ1.source]
      have e2 : γ2 ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩ = γ2 1 := by rw [← heq, hp, γ2.target]
      have a1 := congrArg Subtype.val (h1 e1)
      have a2 := congrArg Subtype.val (h2 e2)
      simp only [Set.Icc.coe_zero, Set.Icc.coe_one] at a1 a2
      constructor <;> linarith
    · have e2 : γ2 ⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩ = γ2 0 := by rw [← heq, hp, γ2.source]
      have a2 := congrArg Subtype.val (h2 e2)
      simp only [Set.Icc.coe_zero] at a2
      exact absurd (by linarith : (t : ℝ) ≤ 1 / 2) ht
  intro s t hst
  by_cases hs : (s : ℝ) ≤ 1 / 2 <;> by_cases ht : (t : ℝ) ≤ 1 / 2
  · rw [Path.trans_apply, Path.trans_apply, dif_pos hs, dif_pos ht] at hst
    have := congrArg Subtype.val (h1 hst)
    simp only at this
    exact Or.inl (Subtype.ext (by linarith))
  · exact Or.inr (Or.inl (mixed s t hs ht hst))
  · exact Or.inr (Or.inr (mixed t s ht hs hst.symm).symm)
  · rw [Path.trans_apply, Path.trans_apply, dif_neg hs, dif_neg ht] at hst
    have := congrArg Subtype.val (h2 hst)
    simp only at this
    exact Or.inl (Subtype.ext (by linarith))

/-- A homeomorphism between the plane `ℝ × ℝ` and Euclidean space. -/
noncomputable def planeHomeo : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ :=
  (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).trans
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).toHomeomorph

abbrev Circle2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1

/-- A closed loop that is injective up to its endpoints gives a continuous injective
map from the circle with the same range. -/
theorem circle_param {f : unitInterval → ℝ × ℝ} (hf : Continuous f)
    (hf01 : f 0 = f 1)
    (hinj : ∀ s t : unitInterval, f s = f t →
      s = t ∨ ((s : ℝ) = 0 ∧ (t : ℝ) = 1) ∨ ((s : ℝ) = 1 ∧ (t : ℝ) = 0)) :
    ∃ g : Circle2 → ℝ × ℝ, Continuous g ∧ Function.Injective g ∧
      Set.range g = Set.range f := by
  obtain ⟨e, hec, he01, heinj, hesurj⟩ := JordanCurve.euclidean_unit_circle_loop
  have hpre : ∀ p : Circle2, ∃ u, u ∈ Set.Icc (0 : ℝ) 1 ∧ e u = p := by
    intro p
    have : p ∈ e '' Set.Icc 0 1 := by rw [hesurj]; trivial
    exact this
  choose U hU heU using hpre
  let g : Circle2 → ℝ × ℝ := fun p => f ⟨U p, hU p⟩
  -- `e`-collisions on `[0,1]`
  have ecoll : ∀ u v : ℝ, (hu : u ∈ Set.Icc (0 : ℝ) 1) → (hv : v ∈ Set.Icc (0 : ℝ) 1) →
      e u = e v → f ⟨u, hu⟩ = f ⟨v, hv⟩ := by
    intro u v hu hv huv
    have h0 : f ⟨0, by simp⟩ = f ⟨1, by simp⟩ := hf01
    rcases lt_or_eq_of_le hu.2 with hu1 | hu1 <;> rcases lt_or_eq_of_le hv.2 with hv1 | hv1
    · have := heinj ⟨hu.1, hu1⟩ ⟨hv.1, hv1⟩ huv
      subst this; rfl
    · subst hv1
      have := heinj ⟨hu.1, hu1⟩ ⟨le_refl 0, zero_lt_one⟩ (huv.trans he01.symm)
      subst this; exact h0
    · subst hu1
      have := heinj ⟨hv.1, hv1⟩ ⟨le_refl 0, zero_lt_one⟩ (huv.symm.trans he01.symm)
      subst this; exact h0.symm
    · subst hu1; subst hv1; rfl
  have hge : ∀ u (hu : u ∈ Set.Icc (0 : ℝ) 1), g (e u) = f ⟨u, hu⟩ :=
    fun u hu => ecoll _ _ _ _ (heU (e u))
  refine ⟨g, ?_, ?_, ?_⟩
  · rw [continuous_iff_isClosed]
    intro F hF
    have hK : IsCompact (Set.Icc (0 : ℝ) 1 ∩
        (fun u => f (Set.projIcc (0 : ℝ) 1 zero_le_one u)) ⁻¹' F) :=
      isCompact_Icc.inter_right (hF.preimage (hf.comp continuous_projIcc))
    have hpre : g ⁻¹' F = e '' (Set.Icc (0 : ℝ) 1 ∩
        (fun u => f (Set.projIcc (0 : ℝ) 1 zero_le_one u)) ⁻¹' F) := by
      ext p
      constructor
      · intro hp
        refine ⟨U p, ⟨hU p, ?_⟩, heU p⟩
        simp only [Set.mem_preimage, Set.projIcc_of_mem _ (hU p)]
        exact hp
      · rintro ⟨u, ⟨hu, hF'⟩, rfl⟩
        show g (e u) ∈ F
        rw [hge u hu]
        simpa only [Set.mem_preimage, Set.projIcc_of_mem _ hu] using hF'
    rw [hpre]
    exact (hK.image_of_continuousOn (hec.mono Set.inter_subset_left)).isClosed
  · intro p q hpq
    rcases hinj _ _ hpq with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← heU p, ← heU q]
      exact congrArg e (congrArg Subtype.val h)
    · change U p = 0 at h1
      change U q = 1 at h2
      rw [← heU p, ← heU q, h1, h2, he01]
    · change U p = 1 at h1
      change U q = 0 at h2
      rw [← heU p, ← heU q, h1, h2, he01]
  · apply le_antisymm
    · rintro _ ⟨p, rfl⟩; exact ⟨_, rfl⟩
    · rintro _ ⟨s, rfl⟩
      exact ⟨e s, hge s s.2⟩

theorem jordan_of_two_arcs {a b : ℝ × ℝ} (hab : a ≠ b) (γ1 : Path a b) (γ2 : Path b a)
    (h1 : Function.Injective γ1) (h2 : Function.Injective γ2)
    (h : ∀ p, p ∈ Set.range γ1 → p ∈ Set.range γ2 → p = a ∨ p = b) :
    ∃ U O : Set (ℝ × ℝ), IsOpen U ∧ IsOpen O ∧ Disjoint U O ∧
      U ∪ O = (Set.range γ1 ∪ Set.range γ2)ᶜ ∧
      Set.range γ1 ∪ Set.range γ2 ⊆ closure U ∧
      Set.range γ1 ∪ Set.range γ2 ⊆ closure O := by
  clear hab
  obtain ⟨g, hgc, hgi, hgr⟩ := circle_param (γ1.trans γ2).continuous
    (by rw [Path.source, Path.target]) (loop_inj γ1 γ2 h1 h2 h)
  rw [Path.trans_range] at hgr
  rw [← hgr]
  let φ : ℝ × ℝ ≃ₜ EuclideanSpace ℝ (Fin 2) := planeHomeo.symm
  obtain ⟨I, O, hIo, hOo, -, -, -, -, hdisj, hun, hfI, hfO⟩ :=
    JordanCurve.jordan_curve_theorem (φ ∘ g) (φ.continuous.comp hgc)
      (φ.injective.comp hgi)
  have hrange : φ ⁻¹' Set.range (φ ∘ g) = Set.range g := by
    rw [Set.range_comp, Set.preimage_image_eq _ φ.injective]
  refine ⟨φ ⁻¹' I, φ ⁻¹' O, hIo.preimage φ.continuous, hOo.preimage φ.continuous,
    hdisj.preimage φ, ?_, ?_, ?_⟩
  · rw [← Set.preimage_union, hun, Set.preimage_compl, hrange]
  · intro x hx
    rw [← φ.preimage_closure]
    rw [← hrange, ← hfI] at hx
    exact frontier_subset_closure hx
  · intro x hx
    rw [← φ.preimage_closure]
    rw [← hrange, ← hfO] at hx
    exact frontier_subset_closure hx

end OuterplanarL1Tan.Dev.C3.PartA
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.C3
open OuterplanarL1Tan.Linear
alias jordan_of_two_arcs := OuterplanarL1Tan.Dev.C3.PartA.jordan_of_two_arcs

end OuterplanarL1Tan.Dev.C3
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.C3.PartD
open OuterplanarL1Tan.Linear
variable {V : Type} {G : SimpleGraph V} (D : PlaneDrawing G)
/-! ## Outer-face points avoid the drawing -/
theorem outer_ne_vertex {p : ℝ × ℝ} (hp : p ∈ D.outerFace Set.univ) (x : V) :
    p ≠ D.vertex x := by
  rintro rfl
  exact hp.1 (Or.inl ⟨⟨x, trivial⟩, rfl⟩)

theorem outer_ne_arc {p : ℝ × ℝ} (hp : p ∈ D.outerFace Set.univ) {a b : V}
    (h : G.Adj a b) (t : unitInterval) : p ≠ D.arc h t := by
  rintro rfl
  apply hp.1
  refine Or.inr ?_
  simp only [Set.mem_iUnion]
  exact ⟨⟨a, trivial⟩, ⟨b, trivial⟩, h, t, rfl⟩

/-! ## The drawing of a walk -/
/-- Vertex points and arcs of a walk. -/
def drawSet : {u w : V} → G.Walk u w → Set (ℝ × ℝ)
  | u, _, .nil => {D.vertex u}
  | _, _, .cons h p => Set.range (D.arc h) ∪ drawSet p

theorem mem_drawSet {u w : V} (p : G.Walk u w) {z : ℝ × ℝ} (hz : z ∈ drawSet D p) :
    (∃ x ∈ p.support, z = D.vertex x) ∨
      ∃ (a b : V) (h : G.Adj a b) (t : unitInterval),
        a ∈ p.support ∧ b ∈ p.support ∧ z = D.arc h t := by
  induction p with
  | nil =>
    left
    exact ⟨_, by simp, hz⟩
  | @cons u v w h p ih =>
    rcases hz with ⟨t, rfl⟩ | hz
    · right
      exact ⟨u, v, h, t, by simp, by simp [p.start_mem_support], rfl⟩
    · rcases ih hz with ⟨x, hx, rfl⟩ | ⟨a, b, k, t, ha, hb, rfl⟩
      · left; exact ⟨x, by simp [hx], rfl⟩
      · right; exact ⟨a, b, k, t, by simp [ha], by simp [hb], rfl⟩

theorem start_mem_drawSet {u w : V} (p : G.Walk u w) : D.vertex u ∈ drawSet D p := by
  cases p with
  | nil => exact rfl
  | cons h p => exact Or.inl ⟨0, (D.arc h).source⟩

theorem end_mem_drawSet {u w : V} (p : G.Walk u w) : D.vertex w ∈ drawSet D p := by
  induction p with
  | nil => exact rfl
  | cons h p ih => exact Or.inr ih

theorem isPreconnected_drawSet {u w : V} (p : G.Walk u w) :
    IsPreconnected (drawSet D p) := by
  induction p with
  | nil => exact isPreconnected_singleton
  | @cons u v w h p ih =>
    exact IsPreconnected.union (D.vertex v) ⟨1, (D.arc h).target⟩ (start_mem_drawSet D p)
      (isPreconnected_range (D.arc h).continuous) ih

theorem vertex_mem_drawSet {u w : V} (p : G.Walk u w) {x : V}
    (hx : D.vertex x ∈ drawSet D p) : x ∈ p.support := by
  rcases mem_drawSet D p hx with ⟨y, hy, he⟩ | ⟨a, b, h, t, ha, hb, he⟩
  · rwa [D.vertex_injective he]
  · rcases D.arc_avoids_vertices h t x he.symm with rfl | rfl
    · exact ha
    · exact hb

theorem outer_not_mem_drawSet {u w : V} (p : G.Walk u w) {z : ℝ × ℝ}
    (hz : z ∈ D.outerFace Set.univ) : z ∉ drawSet D p := by
  intro hm
  rcases mem_drawSet D p hm with ⟨x, -, rfl⟩ | ⟨a, b, h, t, -, -, rfl⟩
  · exact outer_ne_vertex D hz x rfl
  · exact outer_ne_arc D hz h t rfl

theorem common_of_mem_drawSet {u w u' w' : V} (p : G.Walk u w) (q : G.Walk u' w')
    {z : ℝ × ℝ} (hp : z ∈ drawSet D p) (hq : z ∈ drawSet D q) :
    ∃ x, x ∈ p.support ∧ x ∈ q.support := by
  rcases mem_drawSet D p hp with ⟨x, hx, rfl⟩ | ⟨a, b, h, t, ha, hb, rfl⟩
  · exact ⟨x, hx, vertex_mem_drawSet D q hq⟩
  · rcases mem_drawSet D q hq with ⟨y, hy, he⟩ | ⟨a', b', k, s, ha', hb', he⟩
    · rcases D.arc_avoids_vertices h t y he with rfl | rfl
      · exact ⟨_, ha, hy⟩
      · exact ⟨_, hb, hy⟩
    · rcases D.arcs_meet_only_at_endpoints h k t s he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨ht, -⟩
      · exact ⟨_, ha, ha'⟩
      · exact ⟨_, ha, hb'⟩
      · rcases ht with rfl | rfl
        · rw [(D.arc h).source] at he
          refine ⟨a, ha, ?_⟩
          rcases D.arc_avoids_vertices k s a he.symm with rfl | rfl
          · exact ha'
          · exact hb'
        · rw [(D.arc h).target] at he
          refine ⟨b, hb, ?_⟩
          rcases D.arc_avoids_vertices k s b he.symm with rfl | rfl
          · exact ha'
          · exact hb'

theorem drawSet_disjoint {u w u' w' : V} (p : G.Walk u w) (q : G.Walk u' w')
    (hpq : ∀ z ∈ p.support, z ∉ q.support) {z : ℝ × ℝ}
    (hp : z ∈ drawSet D p) (hq : z ∈ drawSet D q) : False := by
  obtain ⟨x, hx, hx'⟩ := common_of_mem_drawSet D p q hp hq
  exact hpq x hx hx'

/-! ## Drawing a path followed by a tail -/
/-- The arcs of a walk, followed by a tail path. -/
noncomputable def drawPathTrans {z : ℝ × ℝ} : {u w : V} → G.Walk u w → Path (D.vertex w) z →
    Path (D.vertex u) z
  | _, _, .nil, tail => tail
  | _, _, .cons h p, tail => (D.arc h).trans (drawPathTrans p tail)

theorem range_drawPathTrans {z : ℝ × ℝ} {u w : V} (p : G.Walk u w)
    (tail : Path (D.vertex w) z) :
    Set.range (drawPathTrans D p tail) ⊆ drawSet D p ∪ Set.range tail := by
  induction p with
  | nil => exact Set.subset_union_right
  | @cons u v w h p ih =>
    show Set.range ((D.arc h).trans (drawPathTrans D p tail)) ⊆ _
    rw [Path.trans_range]
    intro y hy
    rcases hy with hy | hy
    · exact Or.inl (Or.inl hy)
    · rcases ih tail hy with hy | hy
      · exact Or.inl (Or.inr hy)
      · exact Or.inr hy

theorem drawSet_cons_sub {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    drawSet D p ⊆ drawSet D (.cons h p) := Set.subset_union_right

theorem injective_drawPathTrans {z : ℝ × ℝ} {u w : V} (p : G.Walk u w) (hp : p.IsPath)
    (tail : Path (D.vertex w) z) (ht : Function.Injective tail)
    (hmeet : ∀ y ∈ Set.range tail, y ∈ drawSet D p → y = D.vertex w) :
    Function.Injective (drawPathTrans D p tail) := by
  induction p with
  | nil => exact ht
  | @cons u v w h p ih =>
    rw [SimpleGraph.Walk.cons_isPath_iff] at hp
    have hrest := ih hp.1 tail ht (fun y hy hy' => hmeet y hy (drawSet_cons_sub D h p hy'))
    apply path_trans_injective _ _ (D.arc_injective h) hrest
    rintro y ⟨t, rfl⟩ hy
    rcases range_drawPathTrans D p tail hy with hy | hy
    · rcases mem_drawSet D p hy with ⟨x, hx, he⟩ | ⟨a, b, k, s, ha, hb, he⟩
      · rcases D.arc_avoids_vertices h t x he with rfl | rfl
        · exact absurd hx hp.2
        · exact he
      · rcases D.arcs_meet_only_at_endpoints h k t s he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨ht', -⟩
        · exact absurd ha hp.2
        · exact absurd hb hp.2
        · rcases ht' with rfl | rfl
          · rw [(D.arc h).source] at he ⊢
            rcases D.arc_avoids_vertices k s u he.symm with rfl | rfl
            · exact absurd ha hp.2
            · exact absurd hb hp.2
          · exact (D.arc h).target
    · have hw := hmeet _ hy (Or.inl ⟨t, rfl⟩)
      rw [hw]
      rw [hw] at hy
      rcases D.arc_avoids_vertices h t w hw with rfl | rfl
      · exact absurd p.end_mem_support hp.2
      · rfl

end OuterplanarL1Tan.Dev.C3.PartD
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.C3.PartD
open OuterplanarL1Tan.Linear
variable {V : Type} {G : SimpleGraph V} (D : PlaneDrawing G) (B : OuterFacialWalk D)
/-! ## Collar facts -/
theorem collar_pos_inj {r s t u : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t < 1) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (h : B.collar r t = B.collar s u) : r = s ∧ t = u :=
  B.exterior.2.2.2.2.1 r ⟨hr0, hr1⟩ s ⟨hs0, hs1⟩ t ⟨ht0, ht1⟩ u ⟨hu0, hu1⟩ h

theorem collar_outer {r t : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    B.collar r t ∈ D.outerFace Set.univ :=
  B.exterior.2.2.2.1 r ⟨hr0, hr1⟩ t ⟨ht0, ht1⟩

theorem collar_ne_vertex {r t : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (x : V) : B.collar r t ≠ D.vertex x :=
  outer_ne_vertex D (collar_outer D B hr0 hr1 ht0 ht1) x

theorem collar_not_mem_drawSet {r t : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) {u w : V} (p : G.Walk u w) : B.collar r t ∉ drawSet D p :=
  outer_not_mem_drawSet D p (collar_outer D B hr0 hr1 ht0 ht1)

theorem collar_cont :
    ContinuousOn (Function.uncurry B.collar) (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
  rw [Set.Icc_prod_Icc]
  exact B.exterior.1

/-- The parameter of visit `j`. -/
noncomputable def tt (j : Fin B.size) : ℝ := (j.val : ℝ) / (B.size : ℝ)

theorem tt_nonneg (j : Fin B.size) : 0 ≤ tt D B j := by
  unfold tt; positivity

theorem tt_lt_one (j : Fin B.size) : tt D B j < 1 := by
  unfold tt
  have hn : (0 : ℝ) < B.size := by exact_mod_cast B.positive
  rw [div_lt_one hn]
  exact_mod_cast j.isLt

theorem tt_lt {i j : Fin B.size} (h : i < j) : tt D B i < tt D B j := by
  unfold tt
  have hn : (0 : ℝ) < B.size := by exact_mod_cast B.positive
  apply div_lt_div_of_pos_right _ hn
  exact_mod_cast h

theorem collar_zero {x y : V} (hxy : x ≠ y) (j : Fin B.size) :
    B.collar 0 (tt D B j) = D.vertex (B.vertex j) := by
  rcases B.steps j with h | h
  · have := B.traces_edges j h 0
    simp only [Set.Icc.coe_zero, add_zero] at this
    rw [tt, this, (D.arc h).source]
  · exact absurd ((h x).trans (h y).symm) hxy

/-! ## Spokes -/
/-- The spoke from the vertex of visit `j` out to the radius-1/2 collar curve. -/
noncomputable def spoke {x y : V} (hxy : x ≠ y) (j : Fin B.size) :
    Path (D.vertex (B.vertex j)) (B.collar (1 / 2) (tt D B j)) where
  toFun u := B.collar ((u : ℝ) / 2) (tt D B j)
  continuous_toFun := by
    have hf : Continuous (fun u : unitInterval => (((u : ℝ) / 2), tt D B j)) := by fun_prop
    refine (collar_cont D B).comp_continuous hf (fun u => ?_)
    have := u.2.1; have := u.2.2
    have := tt_nonneg D B j; have := tt_lt_one D B j
    exact ⟨⟨by positivity, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  source' := by
    simp only [Set.Icc.coe_zero, zero_div]
    exact collar_zero D B hxy j
  target' := by simp

theorem spoke_apply {x y : V} (hxy : x ≠ y) (j : Fin B.size) (u : unitInterval) :
    spoke D B hxy j u = B.collar ((u : ℝ) / 2) (tt D B j) := rfl

theorem mem_range_spoke {x y : V} (hxy : x ≠ y) (j : Fin B.size) {z : ℝ × ℝ}
    (hz : z ∈ Set.range (spoke D B hxy j)) :
    z = D.vertex (B.vertex j) ∨ ∃ s, 0 < s ∧ s ≤ 1 / 2 ∧ z = B.collar s (tt D B j) := by
  obtain ⟨u, rfl⟩ := hz
  rw [spoke_apply]
  rcases eq_or_lt_of_le u.2.1 with h0 | h0
  · left
    rw [← h0, zero_div]
    exact collar_zero D B hxy j
  · right
    exact ⟨(u : ℝ) / 2, by positivity, by linarith [u.2.2], rfl⟩

theorem spoke_injective {x y : V} (hxy : x ≠ y) (j : Fin B.size) :
    Function.Injective (spoke D B hxy j) := by
  have key : ∀ u v : unitInterval, (u : ℝ) = 0 → 0 < (v : ℝ) →
      spoke D B hxy j u ≠ spoke D B hxy j v := by
    intro u v hu hv he
    rw [spoke_apply, spoke_apply, hu, zero_div, collar_zero D B hxy j] at he
    exact collar_ne_vertex D B (by positivity) (by linarith [v.2.2]) (tt_nonneg D B j)
      (tt_lt_one D B j).le _ he.symm
  intro u v he
  rcases eq_or_lt_of_le u.2.1 with hu | hu <;> rcases eq_or_lt_of_le v.2.1 with hv | hv
  · exact Subtype.ext (hu.symm.trans hv)
  · exact absurd he (key u v hu.symm hv)
  · exact absurd he.symm (key v u hv.symm hu)
  · rw [spoke_apply, spoke_apply] at he
    have := (collar_pos_inj D B (by positivity) (by linarith [u.2.2]) (by positivity)
      (by linarith [v.2.2]) (tt_nonneg D B j) (tt_lt_one D B j) (tt_nonneg D B j)
      (tt_lt_one D B j) he).1
    exact Subtype.ext (by linarith)

/-! ## The arc on the radius-1/2 collar curve -/
/-- The radius-1/2 collar curve between parameters `a ≤ b`. -/
noncomputable def jarc {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Path (B.collar (1 / 2) a) (B.collar (1 / 2) b) where
  toFun u := B.collar (1 / 2) (a + (u : ℝ) * (b - a))
  continuous_toFun := by
    have hf : Continuous (fun u : unitInterval => ((1 / 2 : ℝ), a + (u : ℝ) * (b - a))) := by
      fun_prop
    refine (collar_cont D B).comp_continuous hf (fun u => ?_)
    have h1 := u.2.1; have h2 := u.2.2
    have h3 : 0 ≤ (u : ℝ) * (b - a) := mul_nonneg h1 (by linarith)
    have h4 : (u : ℝ) * (b - a) ≤ 1 * (b - a) := mul_le_mul_of_nonneg_right h2 (by linarith)
    exact ⟨⟨by norm_num, by norm_num⟩, ⟨by linarith, by linarith⟩⟩
  source' := by simp
  target' := by simp

theorem jarc_apply {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (u : unitInterval) :
    jarc D B ha hab hb u = B.collar (1 / 2) (a + (u : ℝ) * (b - a)) := rfl

theorem mem_range_jarc {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) {z : ℝ × ℝ}
    (hz : z ∈ Set.range (jarc D B ha hab hb)) :
    ∃ t, a ≤ t ∧ t ≤ b ∧ z = B.collar (1 / 2) t := by
  obtain ⟨u, rfl⟩ := hz
  have h1 := u.2.1; have h2 := u.2.2
  have h3 : 0 ≤ (u : ℝ) * (b - a) := mul_nonneg h1 (by linarith)
  have h4 : (u : ℝ) * (b - a) ≤ 1 * (b - a) := mul_le_mul_of_nonneg_right h2 (by linarith)
  exact ⟨_, by linarith, by linarith, rfl⟩

theorem collar_mem_range_jarc {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) {t : ℝ}
    (hat : a ≤ t) (htb : t ≤ b) : B.collar (1 / 2) t ∈ Set.range (jarc D B ha hab.le hb) := by
  have hba : 0 < b - a := by linarith
  refine ⟨⟨(t - a) / (b - a), div_nonneg (by linarith) hba.le,
    (div_le_one hba).2 (by linarith)⟩, ?_⟩
  rw [jarc_apply]
  congr 1
  simp only
  field_simp
  ring

theorem jarc_injective {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < 1) :
    Function.Injective (jarc D B ha hab.le hb.le) := by
  intro u v he
  rw [jarc_apply, jarc_apply] at he
  have hba : 0 < b - a := by linarith
  have hu1 := u.2.1; have hu2 := u.2.2; have hv1 := v.2.1; have hv2 := v.2.2
  have h3 : 0 ≤ (u : ℝ) * (b - a) := mul_nonneg hu1 hba.le
  have h4 : (u : ℝ) * (b - a) ≤ 1 * (b - a) := mul_le_mul_of_nonneg_right hu2 hba.le
  have h5 : 0 ≤ (v : ℝ) * (b - a) := mul_nonneg hv1 hba.le
  have h6 : (v : ℝ) * (b - a) ≤ 1 * (b - a) := mul_le_mul_of_nonneg_right hv2 hba.le
  have := (collar_pos_inj D B (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by linarith) (by linarith) (by linarith) (by linarith) he).2
  have h7 : ((u : ℝ) - v) * (b - a) = 0 := by linarith
  rcases mul_eq_zero.1 h7 with h | h
  · exact Subtype.ext (by linarith)
  · linarith

end OuterplanarL1Tan.Dev.C3.PartD
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.C3.PartD
open OuterplanarL1Tan.Linear
/-- No four alternating visits of an outer facial walk are joined, in pairs,
by vertex-disjoint walks (the first one a path). -/
theorem no_alternation {V : Type} {G : SimpleGraph V} (D : PlaneDrawing G)
    (B : OuterFacialWalk D) (i1 i2 i3 i4 : Fin B.size)
    (h12 : i1 < i2) (h23 : i2 < i3) (h4 : i4 < i1 ∨ i3 < i4)
    (P : G.Walk (B.vertex i3) (B.vertex i1)) (hP : P.IsPath)
    (Q : G.Walk (B.vertex i2) (B.vertex i4))
    (hPQ : ∀ z ∈ P.support, z ∉ Q.support) : False := by
  classical
  have hxy : B.vertex i3 ≠ B.vertex i2 := fun h =>
    hPQ _ P.start_mem_support (by rw [h]; exact Q.start_mem_support)
  -- parameters
  set c := B.collar with hc
  set t1 := tt D B i1 with ht1
  set t2 := tt D B i2 with ht2
  set t3 := tt D B i3 with ht3
  set t4 := tt D B i4 with ht4
  have h1_0 : 0 ≤ t1 := tt_nonneg D B i1
  have h4_0 : 0 ≤ t4 := tt_nonneg D B i4
  have h3_1 : t3 < 1 := tt_lt_one D B i3
  have h4_1 : t4 < 1 := tt_lt_one D B i4
  have h12' : t1 < t2 := tt_lt D B h12
  have h23' : t2 < t3 := tt_lt D B h23
  have h4' : t4 < t1 ∨ t3 < t4 := by
    rcases h4 with h | h
    · exact Or.inl (tt_lt D B h)
    · exact Or.inr (tt_lt D B h)
  have hv1 : c 0 t1 = D.vertex (B.vertex i1) := collar_zero D B hxy i1
  have hv2 : c 0 t2 = D.vertex (B.vertex i2) := collar_zero D B hxy i2
  have hv4 : c 0 t4 = D.vertex (B.vertex i4) := collar_zero D B hxy i4
  obtain ⟨ε, hε0, hε1, hε2, hε3⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < t2 - t1 ∧ ε < t3 - t2 ∧ ε < 1 / 4 := by
    refine ⟨min (min (t2 - t1) (t3 - t2)) (1 / 4) / 2, ?_, ?_, ?_, ?_⟩
    · have : 0 < min (min (t2 - t1) (t3 - t2)) (1 / 4) :=
        lt_min (lt_min (by linarith) (by linarith)) (by norm_num)
      linarith
    · have := min_le_left (min (t2 - t1) (t3 - t2)) (1 / 4)
      have := min_le_left (t2 - t1) (t3 - t2)
      have : 0 < min (min (t2 - t1) (t3 - t2)) (1 / 4) :=
        lt_min (lt_min (by linarith) (by linarith)) (by norm_num)
      linarith
    · have := min_le_left (min (t2 - t1) (t3 - t2)) (1 / 4)
      have := min_le_right (t2 - t1) (t3 - t2)
      have : 0 < min (min (t2 - t1) (t3 - t2)) (1 / 4) :=
        lt_min (lt_min (by linarith) (by linarith)) (by norm_num)
      linarith
    · have := min_le_right (min (t2 - t1) (t3 - t2)) (1 / 4)
      have : 0 < min (min (t2 - t1) (t3 - t2)) (1 / 4) :=
        lt_min (lt_min (by linarith) (by linarith)) (by norm_num)
      linarith
  -- the closed curve
  let σ1 := spoke D B hxy i1
  let σ3 := spoke D B hxy i3
  have h13 : t1 < t3 := h12'.trans h23'
  let γ1 : Path (c (1 / 2) t1) (c (1 / 2) t3) := jarc D B h1_0 h13.le h3_1.le
  let γ2 : Path (c (1 / 2) t3) (c (1 / 2) t1) := σ3.symm.trans (drawPathTrans D P σ1)
  have hσ1 : Function.Injective σ1 := spoke_injective D B hxy i1
  have hσ3 : Function.Injective σ3 := spoke_injective D B hxy i3
  have hγ1 : Function.Injective γ1 := jarc_injective D B h1_0 h13 h3_1
  -- points of the spokes
  have spoke_pts : ∀ k : Fin B.size, ∀ z ∈ Set.range (spoke D B hxy k),
      z = D.vertex (B.vertex k) ∨ ∃ s, 0 < s ∧ s ≤ 1 / 2 ∧ z = c s (tt D B k) :=
    fun k z hz => mem_range_spoke D B hxy k hz
  have hγ2 : Function.Injective γ2 := by
    apply path_trans_injective
    · intro u v he
      simp only [Path.symm_apply] at he
      have := hσ3 he
      simpa using congrArg unitInterval.symm this
    · apply injective_drawPathTrans D P hP σ1 hσ1
      intro y hy hyP
      rcases spoke_pts i1 y hy with h | ⟨s, hs0, hs1, rfl⟩
      · exact h
      · exact absurd hyP (collar_not_mem_drawSet D B hs0 (by linarith) h1_0
          (by linarith) P)
    · intro y hy hy'
      rw [Path.symm_range] at hy
      rcases spoke_pts i3 y hy with h | ⟨s, hs0, hs1, rfl⟩
      · exact h
      · exfalso
        rcases range_drawPathTrans D P σ1 hy' with hyP | hy1
        · exact collar_not_mem_drawSet D B hs0 (by linarith) (by linarith)
            (by linarith) P hyP
        · rcases spoke_pts i1 _ hy1 with h | ⟨s', hs0', hs1', he⟩
          · exact collar_ne_vertex D B hs0 (by linarith) (by linarith) (by linarith) _ h
          · have := (collar_pos_inj D B hs0 (by linarith) hs0' (by linarith) (by linarith)
              h3_1 h1_0 (by linarith) he).2
            linarith
  -- classification of the points of the closed curve
  have hγ2pts : ∀ y ∈ Set.range γ2,
      (∃ s, 0 < s ∧ s ≤ 1 / 2 ∧ (y = c s t1 ∨ y = c s t3)) ∨ y ∈ drawSet D P := by
    intro y hy
    rw [Path.trans_range, Path.symm_range] at hy
    rcases hy with hy | hy
    · rcases spoke_pts i3 y hy with h | ⟨s, hs0, hs1, rfl⟩
      · exact Or.inr (h ▸ start_mem_drawSet D P)
      · exact Or.inl ⟨s, hs0, hs1, Or.inr rfl⟩
    · rcases range_drawPathTrans D P σ1 hy with hyP | hy1
      · exact Or.inr hyP
      · rcases spoke_pts i1 y hy1 with h | ⟨s, hs0, hs1, rfl⟩
        · exact Or.inr (h ▸ end_mem_drawSet D P)
        · exact Or.inl ⟨s, hs0, hs1, Or.inl rfl⟩
  have hCpts : ∀ y ∈ Set.range γ1 ∪ Set.range γ2,
      (∃ s t, y = c s t ∧ 0 < s ∧ s ≤ 1 / 2 ∧
        ((s = 1 / 2 ∧ t1 ≤ t ∧ t ≤ t3) ∨ t = t1 ∨ t = t3)) ∨ y ∈ drawSet D P := by
    intro y hy
    rcases hy with hy | hy
    · obtain ⟨t, ht1', ht3', rfl⟩ := mem_range_jarc D B h1_0 h13.le h3_1.le hy
      exact Or.inl ⟨1 / 2, t, rfl, by norm_num, le_rfl, Or.inl ⟨rfl, ht1', ht3'⟩⟩
    · rcases hγ2pts y hy with ⟨s, hs0, hs1, rfl | rfl⟩ | h
      · exact Or.inl ⟨s, t1, rfl, hs0, hs1, Or.inr (Or.inl rfl)⟩
      · exact Or.inl ⟨s, t3, rfl, hs0, hs1, Or.inr (Or.inr rfl)⟩
      · exact Or.inr h
  have hmeet : ∀ p, p ∈ Set.range γ1 → p ∈ Set.range γ2 →
      p = c (1 / 2) t1 ∨ p = c (1 / 2) t3 := by
    intro p hp1 hp2
    obtain ⟨t, ht1', ht3', rfl⟩ := mem_range_jarc D B h1_0 h13.le h3_1.le hp1
    rcases hγ2pts _ hp2 with ⟨s, hs0, hs1, he | he⟩ | hP'
    · have := collar_pos_inj D B (by norm_num) (by norm_num) hs0 (by linarith)
        (by linarith) (by linarith) h1_0 (by linarith) he
      exact Or.inl (by rw [this.2])
    · have := collar_pos_inj D B (by norm_num) (by norm_num) hs0 (by linarith)
        (by linarith) (by linarith) (by linarith) h3_1 he
      exact Or.inr (by rw [this.2])
    · exact absurd hP' (collar_not_mem_drawSet D B (by norm_num) (by norm_num) (by linarith)
        (by linarith) P)
  have hab : c (1 / 2) t1 ≠ c (1 / 2) t3 := by
    intro he
    have := (collar_pos_inj D B (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      h1_0 (by linarith) (by linarith) h3_1 he).2
    linarith
  obtain ⟨U, O, hU, hO, hUO, hunion, hcU, hcO⟩ :=
    jordan_of_two_arcs hab γ1 γ2 hγ1 hγ2 hmeet
  -- the connected set `Z` crossing the curve at `c (1/2) t2`
  have hsq : ∀ s t : ℝ, 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 →
      ((s, t) : ℝ × ℝ) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 :=
    fun s t a b d e => ⟨⟨a, b⟩, ⟨d, e⟩⟩
  have hcont := collar_cont D B
  let Lower := Function.uncurry c '' (Set.Ioo (1 / 2 - ε) (1 / 2) ×ˢ Set.Ioo (t2 - ε) (t2 + ε))
  let S2 := Function.uncurry c '' (Set.Ico (0 : ℝ) (1 / 2) ×ˢ {t2})
  let S4 := Function.uncurry c '' (Set.Icc (0 : ℝ) 1 ×ˢ {t4})
  let Out := Function.uncurry c '' (Set.Ioc (1 / 2 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1)
  let Z := Lower ∪ S2 ∪ drawSet D Q ∪ S4 ∪ Out
  have hZpre : IsPreconnected Z := by
    have pLower : IsPreconnected Lower :=
      (isPreconnected_Ioo.prod isPreconnected_Ioo).image _ (hcont.mono (by
        rintro ⟨s, t⟩ ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
        exact hsq s t (by linarith) (by linarith) (by linarith) (by linarith)))
    have pS2 : IsPreconnected S2 :=
      (isPreconnected_Ico.prod isPreconnected_singleton).image _ (hcont.mono (by
        rintro ⟨s, t⟩ ⟨⟨h1, h2⟩, h3⟩
        rw [Set.mem_singleton_iff] at h3
        subst h3
        exact hsq s _ (by linarith) (by linarith) (by linarith) (by linarith)))
    have pS4 : IsPreconnected S4 :=
      (isPreconnected_Icc.prod isPreconnected_singleton).image _ (hcont.mono (by
        rintro ⟨s, t⟩ ⟨⟨h1, h2⟩, h3⟩
        rw [Set.mem_singleton_iff] at h3
        subst h3
        exact hsq s _ (by linarith) (by linarith) (by linarith) (by linarith)))
    have pOut : IsPreconnected Out :=
      (isPreconnected_Ioc.prod isPreconnected_Ico).image _ (hcont.mono (by
        rintro ⟨s, t⟩ ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
        exact hsq s t (by linarith) (by linarith) (by linarith) (by linarith)))
    refine IsPreconnected.union (c 1 t4)
      (Or.inr ⟨(1, t4), ⟨⟨by norm_num, le_rfl⟩, Set.mem_singleton _⟩, rfl⟩)
      ⟨(1, t4), ⟨⟨by norm_num, le_rfl⟩, ⟨h4_0, h4_1⟩⟩, rfl⟩ ?_ pOut
    refine IsPreconnected.union (D.vertex (B.vertex i4)) (Or.inr (end_mem_drawSet D Q))
      ⟨(0, t4), ⟨⟨le_rfl, by norm_num⟩, Set.mem_singleton _⟩, hv4⟩ ?_ pS4
    refine IsPreconnected.union (D.vertex (B.vertex i2))
      (Or.inr ⟨(0, t2), ⟨⟨le_rfl, by norm_num⟩, Set.mem_singleton _⟩, hv2⟩)
      (start_mem_drawSet D Q) ?_ (isPreconnected_drawSet D Q)
    exact IsPreconnected.union (c (1 / 2 - ε / 2) t2)
      ⟨(1 / 2 - ε / 2, t2), ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, rfl⟩
      ⟨(1 / 2 - ε / 2, t2), ⟨⟨by linarith, by linarith⟩, Set.mem_singleton _⟩, rfl⟩
      pLower pS2
  have hZpts : ∀ y ∈ Z, (∃ s t, y = c s t ∧ 0 < s ∧ s ≤ 1 ∧ 0 ≤ t ∧ t < 1 ∧
      ((1 / 2 - ε < s ∧ s < 1 / 2 ∧ t2 - ε < t ∧ t < t2 + ε) ∨ (s < 1 / 2 ∧ t = t2) ∨
        t = t4 ∨ 1 / 2 < s)) ∨ y ∈ drawSet D Q := by
    rintro y ((((⟨⟨s, t⟩, ⟨⟨hs1, hs2⟩, ⟨ht1', ht2'⟩⟩, rfl⟩ |
      ⟨⟨s, t⟩, ⟨⟨hs1, hs2⟩, ht⟩, rfl⟩) | hQ) | ⟨⟨s, t⟩, ⟨⟨hs1, hs2⟩, ht⟩, rfl⟩) |
      ⟨⟨s, t⟩, ⟨⟨hs1, hs2⟩, ⟨ht1', ht2'⟩⟩, rfl⟩)
    · exact Or.inl ⟨s, t, rfl, by linarith, by linarith, by linarith, by linarith,
        Or.inl ⟨hs1, hs2, ht1', ht2'⟩⟩
    · rw [Set.mem_singleton_iff] at ht
      subst ht
      rcases eq_or_lt_of_le hs1 with h | h
      · subst h
        right
        show c 0 t2 ∈ drawSet D Q
        rw [hv2]; exact start_mem_drawSet D Q
      · exact Or.inl ⟨s, t2, rfl, h, by linarith, by linarith, by linarith,
          Or.inr (Or.inl ⟨hs2, rfl⟩)⟩
    · exact Or.inr hQ
    · rw [Set.mem_singleton_iff] at ht
      subst ht
      rcases eq_or_lt_of_le hs1 with h | h
      · subst h
        right
        show c 0 t4 ∈ drawSet D Q
        rw [hv4]; exact end_mem_drawSet D Q
      · exact Or.inl ⟨s, t4, rfl, h, hs2, h4_0, h4_1, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact Or.inl ⟨s, t, rfl, by linarith, hs2, ht1', ht2', Or.inr (Or.inr (Or.inr hs1))⟩
  have hZC : ∀ y ∈ Z, y ∉ Set.range γ1 ∪ Set.range γ2 := by
    intro y hyZ hyC
    rcases hZpts y hyZ with ⟨s, t, rfl, hs0, hs1, ht0, ht1', hz⟩ | hQ <;>
      rcases hCpts _ hyC with ⟨s', t', he, hs0', hs1', hc⟩ | hPm
    · have ht' : 0 ≤ t' ∧ t' < 1 := by
        rcases hc with ⟨-, a, b⟩ | rfl | rfl <;> constructor <;> linarith
      obtain ⟨rfl, rfl⟩ := collar_pos_inj D B hs0 hs1 hs0' (by linarith) ht0 ht1' ht'.1 ht'.2 he
      rcases h4' with h | h <;> rcases hz with ⟨a, b, d, e⟩ | ⟨a, b⟩ | a | a <;>
        rcases hc with ⟨a', b', d'⟩ | a' | a' <;> linarith
    · exact collar_not_mem_drawSet D B hs0 hs1 ht0 ht1'.le P hPm
    · have ht' : 0 ≤ t' ∧ t' < 1 := by
        rcases hc with ⟨-, a, b⟩ | rfl | rfl <;> constructor <;> linarith
      rw [he] at hQ
      exact collar_not_mem_drawSet D B hs0' (by linarith) ht'.1 ht'.2.le Q hQ
    · exact drawSet_disjoint D P Q hPQ hPm hQ
  -- the open neighbourhood `N` of `c (1/2) t2`
  let N := Function.uncurry c '' (Set.Ioo (1 / 2 - ε) (1 / 2 + ε) ×ˢ Set.Ioo (t2 - ε) (t2 + ε))
  have hNopen : IsOpen N := by
    refine Plasticity.Topology.isOpen_image_of_injOn_of_finrank_eq (V := ℝ × ℝ) (W := ℝ × ℝ)
      rfl _ (isOpen_Ioo.prod isOpen_Ioo) _ (hcont.mono ?_) ?_
    · rintro ⟨s, t⟩ ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      exact hsq s t (by linarith) (by linarith) (by linarith) (by linarith)
    · rintro ⟨s, t⟩ ⟨⟨a, b⟩, ⟨d, e⟩⟩ ⟨s', t'⟩ ⟨⟨a', b'⟩, ⟨d', e'⟩⟩ he
      obtain ⟨h1, h2⟩ := collar_pos_inj D B (s := s') (u := t') (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) he
      exact Prod.ext h1 h2
  have hN0 : c (1 / 2) t2 ∈ N :=
    ⟨(1 / 2, t2), ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, rfl⟩
  have hC0 : c (1 / 2) t2 ∈ Set.range γ1 ∪ Set.range γ2 :=
    Or.inl (collar_mem_range_jarc D B h1_0 h13 h3_1.le h12'.le h23'.le)
  have hNZ : ∀ y ∈ N, y ∉ Set.range γ1 ∪ Set.range γ2 → y ∈ Z := by
    rintro y ⟨⟨s, t⟩, ⟨⟨a, b⟩, ⟨d, e⟩⟩, rfl⟩ hy
    rcases lt_trichotomy s (1 / 2) with h | rfl | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨(s, t), ⟨⟨a, h⟩, ⟨d, e⟩⟩, rfl⟩)))
    · exact absurd (Or.inl (collar_mem_range_jarc D B h1_0 h13 h3_1.le (t := t)
        (by linarith) (by linarith))) hy
    · exact Or.inr ⟨(s, t), ⟨⟨h, by linarith⟩, ⟨by linarith, by linarith⟩⟩, rfl⟩
  obtain ⟨p, hpN, hpU⟩ := _root_.mem_closure_iff.1 (hcU hC0) N hNopen hN0
  obtain ⟨q, hqN, hqO⟩ := _root_.mem_closure_iff.1 (hcO hC0) N hNopen hN0
  have hpZ : p ∈ Z := hNZ p hpN (by rw [← Set.mem_compl_iff, ← hunion]; exact Or.inl hpU)
  have hqZ : q ∈ Z := hNZ q hqN (by rw [← Set.mem_compl_iff, ← hunion]; exact Or.inr hqO)
  have hZsub : Z ⊆ U ∪ O := fun y hy => by rw [hunion]; exact hZC y hy
  obtain ⟨r, -, hrU, hrO⟩ := hZpre U O hU hO hZsub ⟨p, hpZ, hpU⟩ ⟨q, hqZ, hqO⟩
  exact Set.disjoint_left.1 hUO hrU hrO

end OuterplanarL1Tan.Dev.C3.PartD
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.C3
open OuterplanarL1Tan.Linear
/-! ## The drawing -/
alias no_alternation := OuterplanarL1Tan.Dev.C3.PartD.no_alternation

/-! ## Claim 3 -/
theorem claim_3_dev {V : Type} [Fintype V] (W : WeightedGraph V)
    (reachable : W.FiniteDistances) (D : PlaneDrawing W.graph)
    (B : OuterFacialWalk D) (x y : V) (t : ℝ) :
    transitionCount D B (sublevel W x y t) ≤ 2 := by
  by_contra hc
  push_neg at hc
  obtain ⟨i1, i2, i3, i4, h12, h23, h4, h13, h24, h12'⟩ :=
    four_alternating D B (sublevel W x y t) (by omega)
  obtain ⟨P, hP, hPs⟩ := same_class_path W reachable x y t (B.vertex i3) (B.vertex i1) h13.symm
  obtain ⟨Q, -, hQs⟩ := same_class_path W reachable x y t (B.vertex i2) (B.vertex i4) h24
  refine no_alternation D B i1 i2 i3 i4 h12 h23 h4 P hP Q ?_
  intro z hzP hzQ
  have a := hPs z hzP
  have b := hQs z hzQ
  exact h12' (h13.trans (a.symm.trans b))

end OuterplanarL1Tan.Dev.C3
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Linear
theorem chk_claim_3 {V : Type} [Fintype V] (W : WeightedGraph V)
    (reachable : W.FiniteDistances) (D : PlaneDrawing W.graph)
    (B : OuterFacialWalk D) (x y : V) (t : ℝ)
    (lower : -W.distance x y < t) (upper : t < W.distance x y) :
    transitionCount D B (sublevel W x y t) ≤ 2 :=
  OuterplanarL1Tan.Dev.C3.claim_3_dev W reachable D B x y t

end OuterplanarL1Tan.Linear
end

theorem solution : type_of% @OuterplanarL1Tan.Linear.chk_claim_3 := @OuterplanarL1Tan.Linear.chk_claim_3
