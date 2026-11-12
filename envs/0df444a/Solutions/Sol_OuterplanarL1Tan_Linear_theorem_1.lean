-- Prove2me | solution 1 for OuterplanarL1Tan.Linear.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T21:00:46.20033+00:00
-- url     : https://prove2.me/submissions/41b8ab45-3ae9-4cc9-960c-648240828418
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OuterplanarL1Tan_Linear_BoundaryPattern
import Definitions.Def_OuterplanarL1Tan_Linear_L1Distance
import Theorems.Thm_OuterplanarL1Tan_Linear_lemma_2
import Theorems.Thm_OuterplanarL1Tan_Linear_lemma_5
import Theorems.Thm_OuterplanarL1Tan_Linear_lemma_6
import Theorems.Thm_OuterplanarL1Tan_Linear_exists_outerFacialWalk_of_connected
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

theorem dist_self {V : Type} (W : WeightedGraph V) (u : V) : W.distance u u = 0 := by
  apply le_antisymm
  · have := dist_le_walk W (SimpleGraph.Walk.nil : W.graph.Walk u u)
    simpa [OAI.PlanarL1.walkLength] using this
  · exact dist_nonneg W u u

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

namespace OuterplanarL1Tan.Dev.C3

open OuterplanarL1Tan.Linear

/-! ## Combinatorics -/

/-! ## Plane topology -/

/-! ## The drawing -/

/-! ## Claim 3 -/

end OuterplanarL1Tan.Dev.C3

namespace OuterplanarL1Tan.Linear

end OuterplanarL1Tan.Linear
end

section
set_option autoImplicit false

namespace OuterplanarL1Tan.Dev.C3.PartA

open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.Dist

/-! ## Combinatorics: four alternating visits -/

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

/-! ## Plane topology -/

end OuterplanarL1Tan.Dev.C3.PartA
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.T1
open OuterplanarL1Tan.Linear
/-- The weighted graph induced on a vertex set. -/
def sub {V : Type} (W : WeightedGraph V) (S : Set V) : WeightedGraph S where
  graph := W.graph.induce S
  length := fun a b => W.length a b
  symmetric := fun a b => W.symmetric a b
  nonnegative := fun a b h => W.nonnegative a b h

/-- Vertices reachable from `x` by a walk of `G` staying in `R`. -/
def comp {V : Type} (G : SimpleGraph V) (R : Set V) (x : V) : Set V :=
  {z | ∃ p : G.Walk x z, ∀ w ∈ p.support, w ∈ R}

end OuterplanarL1Tan.Dev.T1
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.T1.PartX
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.T1 OuterplanarL1Tan.Dev.Dist
/-! ## ℓ₁ helpers -/
theorem l1n {ι : Type} [Fintype ι] (v : PiLp 1 (fun _ : ι => ℝ)) :
    ‖v‖ = ∑ i, |v i| := by
  rw [PiLp.norm_eq_of_L1]
  simp [Real.norm_eq_abs]

/-- Disjoint coordinate blocks in finite ℓ₁. -/
theorem block_sum {X β : Type} [Fintype β] (n : β → ℕ) (f : ∀ b, X → L1Vector (n b)) :
    ∃ N : ℕ, ∃ F : X → L1Vector N, ∀ x y, ‖F x - F y‖ = ∑ b, ‖f b x - f b y‖ := by
  let ι := Σ b, Fin (n b)
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun x => WithLp.toLp 1 (fun k => f (e.symm k).1 x (e.symm k).2), ?_⟩
  intro x y
  rw [l1n]
  simp only [PiLp.sub_apply]
  have h1 : ∀ k : Fin (Fintype.card ι),
      |(WithLp.toLp 1 (fun k => f (e.symm k).1 x (e.symm k).2) :
          PiLp 1 (fun _ : Fin (Fintype.card ι) => ℝ)) k -
        (WithLp.toLp 1 (fun k => f (e.symm k).1 y (e.symm k).2) :
          PiLp 1 (fun _ : Fin (Fintype.card ι) => ℝ)) k| =
      (fun s : ι => |f s.1 x s.2 - f s.1 y s.2|) (e.symm k) := fun k => rfl
  rw [Finset.sum_congr rfl (fun k _ => h1 k), Equiv.sum_comp e.symm
    (fun s : ι => |f s.1 x s.2 - f s.1 y s.2|), Fintype.sum_sigma]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [l1n]
  simp only [PiLp.sub_apply]

end OuterplanarL1Tan.Dev.T1.PartX
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.T1
open OuterplanarL1Tan.Linear
/-! ## Part X stubs -/
alias block_sum := OuterplanarL1Tan.Dev.T1.PartX.block_sum

end OuterplanarL1Tan.Dev.T1
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.T1.PartX
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.T1 OuterplanarL1Tan.Dev.Dist
/-! ## Induced walks -/
/-- A walk of `G` inside `S` lifts to the induced weighted graph with the same length. -/
theorem induce_walk {V : Type} (W : WeightedGraph V) (S : Set V) {a b : V}
    (p : W.graph.Walk a b) (hp : ∀ w ∈ p.support, w ∈ S) :
    ∃ q : (sub W S).graph.Walk ⟨a, hp a p.start_mem_support⟩ ⟨b, hp b p.end_mem_support⟩,
      OAI.PlanarL1.walkLength (sub W S).length q = OAI.PlanarL1.walkLength W.length p := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | @cons u v w hadj p ih =>
    have hv : v ∈ S := hp v (by simp)
    obtain ⟨q, hq⟩ := ih (fun x hx => hp x (by simp [hx]))
    refine ⟨SimpleGraph.Walk.cons
      (show (sub W S).graph.Adj ⟨u, hp u (by simp)⟩ ⟨v, hv⟩ from hadj) q, ?_⟩
    simp only [OAI.PlanarL1.walkLength, hq]
    rfl

end OuterplanarL1Tan.Dev.T1.PartX
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.T1
open OuterplanarL1Tan.Linear
alias induce_walk := OuterplanarL1Tan.Dev.T1.PartX.induce_walk

end OuterplanarL1Tan.Dev.T1
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.T1.PartX
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.T1 OuterplanarL1Tan.Dev.Dist
theorem map_len {V : Type} (W : WeightedGraph V) (S : Set V) {a b : S}
    (q : (sub W S).graph.Walk a b) :
    ∃ p : W.graph.Walk a.val b.val,
      OAI.PlanarL1.walkLength W.length p = OAI.PlanarL1.walkLength (sub W S).length q := by
  induction q with
  | nil => exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | @cons u v w h q ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨SimpleGraph.Walk.cons (show W.graph.Adj u.val v.val from h) p, ?_⟩
    show W.length u.val v.val + OAI.PlanarL1.walkLength W.length p =
      W.length u.val v.val + OAI.PlanarL1.walkLength (sub W S).length q
    rw [hp]

/-- Induced distances dominate ambient distances. -/
theorem dist_le_sub {V : Type} (W : WeightedGraph V) (S : Set V)
    (hS : (sub W S).FiniteDistances) (a b : S) :
    W.distance a.val b.val ≤ (sub W S).distance a b := by
  obtain ⟨q0⟩ := hS a b
  unfold WeightedGraph.distance OAI.PlanarL1.graphDistance
  apply le_csInf ⟨_, Set.mem_range_self q0⟩
  rintro _ ⟨q, rfl⟩
  obtain ⟨p, hp⟩ := map_len W S q
  have := dist_le_walk W p
  rw [hp] at this
  exact this

end OuterplanarL1Tan.Dev.T1.PartX
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.T1
open OuterplanarL1Tan.Linear
alias dist_le_sub := OuterplanarL1Tan.Dev.T1.PartX.dist_le_sub

end OuterplanarL1Tan.Dev.T1
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.T1.PartX
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.T1 OuterplanarL1Tan.Dev.Dist
/-! ## Boundary of an induced drawing -/
theorem outerFace_mono {V₁ V₂ : Type} {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    (D₁ : RobertsonSeymour1986.GM5.PlaneDrawing G₁)
    (D₂ : RobertsonSeymour1986.GM5.PlaneDrawing G₂)
    (h : TaitTobin.Outerplanar.drawingImage D₁ ⊆ TaitTobin.Outerplanar.drawingImage D₂) :
    TaitTobin.Outerplanar.outerFace D₂ ⊆ TaitTobin.Outerplanar.outerFace D₁ := by
  rintro p ⟨hp, hb⟩
  refine ⟨fun hp1 => hp (h hp1), fun hb1 => hb ?_⟩
  exact hb1.subset (connectedComponentIn_mono p (Set.compl_subset_compl.mpr h))

/-- A vertex of a peeling layer that lies in a vertex set `S` inside the residual set is on
the outer boundary of the drawing induced on `S`. -/
theorem layer_mem_boundary {V : Type} {G : SimpleGraph V} (D : PlaneDrawing G) (i : ℕ)
    (S : Set V) (hS : S ⊆ D.remaining i) (a : V) (haS : a ∈ S) (ha : a ∈ D.layer i) :
    (⟨a, haS⟩ : S) ∈ (D.induced S).boundary Set.univ := by
  refine ⟨Set.mem_univ _, ?_⟩
  have hcl : D.vertex a ∈ closure (D.outerFace (D.remaining i)) := ha.2
  refine closure_mono ?_ hcl
  apply outerFace_mono
  intro p hp
  rcases hp with ⟨v, rfl⟩ | hp
  · exact Or.inl ⟨⟨v.1.1, hS v.1.2⟩, rfl⟩
  · simp only [Set.mem_iUnion] at hp
    obtain ⟨v, w, hvw, t, rfl⟩ := hp
    refine Or.inr ?_
    simp only [Set.mem_iUnion]
    exact ⟨⟨v.1.1, hS v.1.2⟩, ⟨w.1.1, hS w.1.2⟩, hvw, t, rfl⟩

end OuterplanarL1Tan.Dev.T1.PartX
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.T1
open OuterplanarL1Tan.Linear
alias layer_mem_boundary := OuterplanarL1Tan.Dev.T1.PartX.layer_mem_boundary

end OuterplanarL1Tan.Dev.T1
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.T1.PartX
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.T1 OuterplanarL1Tan.Dev.Dist
/-! ## Finite ℓ₁ embeds in ℓ₁(ℕ) -/
theorem isL1_of_fin {X ι : Type} [Fintype ι] (g : X → PiLp 1 (fun _ : ι => ℝ)) :
    IsL1Distance (fun x y => ‖g x - g y‖) := by
  classical
  let m := Fintype.card ι
  let e := Fintype.equivFin ι
  let seq : PiLp 1 (fun _ : ι => ℝ) → ℕ → ℝ :=
    fun v n => if h : n < m then v (e.symm ⟨n, h⟩) else 0
  have hz : ∀ v, ∀ n ∉ Finset.range m, seq v n = 0 := by
    intro v n hn
    simp only [Finset.mem_range] at hn
    simp [seq, hn]
  have hmem : ∀ v, Memℓp (seq v) 1 := by
    intro v
    apply memℓp_gen
    refine summable_of_ne_finset_zero (s := Finset.range m) (fun n hn => ?_)
    simp [hz v n hn]
  have key : ∀ (u : lp (fun _ : ℕ => ℝ) 1) (v : PiLp 1 (fun _ : ι => ℝ)),
      (∀ n, u n = seq v n) → ‖u‖ = ‖v‖ := by
    intro u v hu
    have h1 := lp.hasSum_norm (p := 1) (E := fun _ : ℕ => ℝ) (by simp) u
    simp only [ENNReal.toReal_one, Real.rpow_one] at h1
    have h2 : HasSum (fun n => ‖u n‖) (∑ n ∈ Finset.range m, ‖u n‖) :=
      hasSum_sum_of_ne_finset_zero (fun n hn => by simp [hu n, hz v n hn])
    rw [h1.unique h2, l1n, Finset.sum_range]
    rw [← Equiv.sum_comp e.symm (fun i => |v i|)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hu k.val]
    simp [seq, k.isLt, Real.norm_eq_abs]
  refine ⟨fun x => ⟨seq (g x), hmem (g x)⟩, fun x y => ?_⟩
  symm
  apply key
  intro n
  rw [lp.coeFn_sub]
  simp only [Pi.sub_apply]
  show seq (g x) n - seq (g y) n = seq (g x - g y) n
  simp only [seq]
  split_ifs <;> simp

/-! ## The per-component map -/
theorem bd_le {V : Type} [Fintype V] (W : WeightedGraph V) (D : PlaneDrawing W.graph)
    (z b : V) (hb : b ∈ D.boundary Set.univ) :
    boundaryDistance W D z ≤ W.distance z b := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨b', -, rfl⟩
    exact dist_nonneg W z b'
  · exact ⟨b, hb, rfl⟩

theorem bd_lip {V : Type} [Fintype V] (W : WeightedGraph V) (hr : W.FiniteDistances)
    (D : PlaneDrawing W.graph) (hne : (D.boundary Set.univ).Nonempty) (x y : V) :
    boundaryDistance W D x ≤ W.distance x y + boundaryDistance W D y := by
  have : boundaryDistance W D x - W.distance x y ≤ boundaryDistance W D y := by
    apply le_csInf
    · obtain ⟨b, hb⟩ := hne
      exact ⟨_, b, hb, rfl⟩
    rintro _ ⟨b, hb, rfl⟩
    have h1 := bd_le W D x b hb
    have h2 := dist_triangle W hr x y b
    linarith
  linarith

/-- The per-component map of §3.3: Lemma 6 applied to `g_H` (Lemmas 2 and 5) with norms `h`. -/
theorem component_map {V : Type} [Fintype V] (W : WeightedGraph V) (D : PlaneDrawing W.graph)
    (S : Set V) [Fintype S] (hne : S.Nonempty) (hS : (sub W S).FiniteDistances)
    (h : S → ℝ) (hh : ∀ x, 0 ≤ h x) :
    ∃ N : ℕ, ∃ Ψ : S → L1Vector N,
      (∀ x, ‖Ψ x‖ = h x) ∧
      (∀ x y, ‖Ψ x - Ψ y‖ ≤ 3 * (sub W S).distance x y + 3 * |h x - h y|) ∧
      (∀ x y b : S, b ∈ (D.induced S).boundary Set.univ →
        (1 / 4 : ℝ) * min ((sub W S).distance x y - 4 * (sub W S).distance x b)
          (max (h x) (h y)) ≤ ‖Ψ x - Ψ y‖) := by
  have : Nonempty S := hne.to_subtype
  let H := sub W S
  let D' : PlaneDrawing H.graph := D.induced S
  have hconn : H.graph.Connected := { preconnected := fun u v => hS u v }
  obtain ⟨B⟩ := exists_outerFacialWalk_of_connected hconn D'
  let g := augmented H D' B
  let δ : S → S → ℝ := fun x y => ‖g x - g y‖
  have hL1 : IsL1Distance δ := isL1_of_fin g
  obtain ⟨N, Ψ, hn, hup, hlo⟩ := lemma_6 δ hL1 h hh
  have hbne : (D'.boundary Set.univ).Nonempty := by
    rw [← B.covers_boundary]
    exact ⟨_, Set.mem_range_self ⟨0, B.positive⟩⟩
  have hδ : ∀ x y, δ x y ≤ 3 * H.distance x y := by
    intro x y
    have hsplit : δ x y = (1 / 4) * ‖pattern H D' B x - pattern H D' B y‖ +
        2 * |boundaryDistance H D' x - boundaryDistance H D' y| := by
      simp only [δ, g, augmented]
      rw [l1n, l1n, Fintype.sum_sum_type, Finset.mul_sum]
      simp only [PiLp.sub_apply, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique,
        Finset.sum_singleton]
      congr 1
      · refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [← mul_sub, abs_mul]
        norm_num
      · rw [← mul_sub, abs_mul]
        norm_num
    have h2 := (lemma_2 H hS D' B).1 x y
    have l1 := bd_lip H hS D' hbne x y
    have l2 := bd_lip H hS D' hbne y x
    have hc := dist_comm H x y
    have habs : |boundaryDistance H D' x - boundaryDistance H D' y| ≤ H.distance x y := by
      rw [abs_le]; constructor <;> linarith
    rw [hsplit]
    linarith
  refine ⟨N, Ψ, hn, fun x y => ?_, fun x y b hb => ?_⟩
  · have := hup x y
    have := hδ x y
    linarith
  · have h5 := lemma_5 H hS D' B x y
    have hb' := bd_le H D' x b hb
    have hm := min_le_left (boundaryDistance H D' x) (boundaryDistance H D' y)
    have hle : H.distance x y - 4 * H.distance x b ≤ δ x y := by
      simp only [δ, g]
      linarith
    refine le_trans ?_ (hlo x y)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact min_le_min_right _ hle

end OuterplanarL1Tan.Dev.T1.PartX
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.T1
open OuterplanarL1Tan.Linear
alias component_map := OuterplanarL1Tan.Dev.T1.PartX.component_map

end OuterplanarL1Tan.Dev.T1
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.T1.PartY
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.T1 OuterplanarL1Tan.Dev.Dist
variable {V : Type} {G : SimpleGraph V} {R : Set V}
/-! ## Components inside a vertex set -/
theorem comp_subset {x : V} : comp G R x ⊆ R := by
  rintro z ⟨p, hp⟩
  exact hp z p.end_mem_support

theorem mem_comp_self {x : V} (hx : x ∈ R) : x ∈ comp G R x :=
  ⟨SimpleGraph.Walk.nil, by simpa using hx⟩

theorem comp_symm {x z : V} (h : z ∈ comp G R x) : x ∈ comp G R z := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.reverse, fun w hw => hp w (by simpa using hw)⟩

theorem comp_trans {x z w : V} (h1 : z ∈ comp G R x) (h2 : w ∈ comp G R z) :
    w ∈ comp G R x := by
  obtain ⟨p, hp⟩ := h1
  obtain ⟨q, hq⟩ := h2
  refine ⟨p.append q, fun u hu => ?_⟩
  rw [SimpleGraph.Walk.mem_support_append_iff] at hu
  rcases hu with hu | hu
  · exact hp u hu
  · exact hq u hu

theorem comp_eq {x z : V} (h : z ∈ comp G R x) : comp G R z = comp G R x := by
  ext w
  constructor
  · intro hw; exact comp_trans h hw
  · intro hw; exact comp_trans (comp_symm h) hw

theorem adj_mem_comp {x y : V} (hxy : G.Adj x y) (hx : x ∈ R) (hy : y ∈ R) :
    y ∈ comp G R x :=
  ⟨SimpleGraph.Walk.cons hxy SimpleGraph.Walk.nil, by
    intro w hw
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;> assumption⟩

theorem walk_support_comp {x z : V} (p : G.Walk x z) (hp : ∀ w ∈ p.support, w ∈ R) :
    ∀ w ∈ p.support, w ∈ comp G R x := by
  classical
  intro w hw
  exact ⟨p.takeUntil w hw, fun u hu => hp u (p.support_takeUntil_subset_support hw hu)⟩

end OuterplanarL1Tan.Dev.T1.PartY
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.T1.PartY
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.T1 OuterplanarL1Tan.Dev.Dist
variable {V : Type}
/-! ## Induced distances -/
theorem sub_dist_le_walk (W : WeightedGraph V) (S : Set V) {a b : V}
    (p : W.graph.Walk a b) (hp : ∀ w ∈ p.support, w ∈ S) :
    (sub W S).distance ⟨a, hp a p.start_mem_support⟩ ⟨b, hp b p.end_mem_support⟩ ≤
      OAI.PlanarL1.walkLength W.length p := by
  obtain ⟨q, hq⟩ := induce_walk W S p hp
  rw [← hq]
  exact dist_le_walk (sub W S) q

theorem sub_dist_le_edge (W : WeightedGraph V) (S : Set V) {a b : V}
    (h : W.graph.Adj a b) (ha : a ∈ S) (hb : b ∈ S) :
    (sub W S).distance ⟨a, ha⟩ ⟨b, hb⟩ ≤ W.length a b := by
  have hp : ∀ w ∈ (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil : W.graph.Walk a b).support,
      w ∈ S := by
    intro w hw
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;> assumption
  have := sub_dist_le_walk W S _ hp
  simpa [OAI.PlanarL1.walkLength] using this

theorem sub_comp_finite (W : WeightedGraph V) (R : Set V) (x : V) :
    (sub W (comp W.graph R x)).FiniteDistances := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨p, hp⟩ := ha
  obtain ⟨q, hq⟩ := hb
  have hr : ∀ w ∈ (p.reverse.append q).support, w ∈ R := by
    intro w hw
    rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
      List.mem_reverse] at hw
    rcases hw with hw | hw
    · exact hp w hw
    · exact hq w hw
  have hr' := walk_support_comp _ hr
  have hr'' : ∀ w ∈ (p.reverse.append q).support, w ∈ comp W.graph R x := by
    intro w hw
    rw [← comp_eq (G := W.graph) ⟨p, hp⟩]
    exact hr' w hw
  obtain ⟨s, -⟩ := induce_walk W (comp W.graph R x) _ hr''
  exact ⟨s⟩

end OuterplanarL1Tan.Dev.T1.PartY
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.T1.PartY
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.T1 OuterplanarL1Tan.Dev.Dist
variable {V : Type} {G : SimpleGraph V} (D : PlaneDrawing G)
/-! ## Peeling -/

theorem remaining_anti {m n : ℕ} (h : m ≤ n) : D.remaining n ⊆ D.remaining m := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact (Set.sdiff_subset).trans ih

theorem not_mem_remaining_iff (v : V) (i : ℕ) :
    v ∉ D.remaining i ↔ ∃ j < i, v ∈ D.layer j := by
  induction i with
  | zero => simp [PlaneDrawing.remaining]
  | succ i ih =>
    have e : D.remaining (i + 1) = D.remaining i \ D.boundary (D.remaining i) := rfl
    rw [e]
    constructor
    · intro hv
      by_cases h : v ∈ D.remaining i
      · have : v ∈ D.boundary (D.remaining i) := by
          by_contra h'
          exact hv ⟨h, h'⟩
        exact ⟨i, Nat.lt_succ_self i, this⟩
      · obtain ⟨j, hj, hj'⟩ := ih.mp h
        exact ⟨j, Nat.lt_succ_of_lt hj, hj'⟩
    · rintro ⟨j, hj, hj'⟩ ⟨h1, h2⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact ih.mpr ⟨j, hj, hj'⟩ h1
      · exact h2 hj'

theorem remaining_univ_of_one (h1 : D.remaining 1 = Set.univ) (n : ℕ) :
    D.remaining n = Set.univ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e : D.remaining (n + 1) = D.remaining n \ D.boundary (D.remaining n) := rfl
    have e1 : D.remaining 1 = D.remaining 0 \ D.boundary (D.remaining 0) := rfl
    rw [e, ih]
    rw [e1] at h1
    exact h1

end OuterplanarL1Tan.Dev.T1.PartY
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.T1.PartY
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.T1 OuterplanarL1Tan.Dev.Dist
variable {V : Type}
/-! ## Stage norms -/
/-- Infimum of distances to a set. -/
noncomputable def infD (W : WeightedGraph V) (E : Set V) (x : V) : ℝ :=
  sInf {r : ℝ | ∃ a ∈ E, r = W.distance x a}

theorem infD_nonneg (W : WeightedGraph V) (E : Set V) (x : V) : 0 ≤ infD W E x := by
  apply Real.sInf_nonneg
  rintro _ ⟨a, -, rfl⟩
  exact dist_nonneg W x a

theorem infD_le (W : WeightedGraph V) (E : Set V) (x : V) {a : V} (ha : a ∈ E) :
    infD W E x ≤ W.distance x a := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨b, -, rfl⟩
    exact dist_nonneg W x b
  · exact ⟨a, ha, rfl⟩

theorem le_infD (W : WeightedGraph V) (E : Set V) (x : V) (hE : E.Nonempty) (c : ℝ)
    (h : ∀ a ∈ E, c ≤ W.distance x a) : c ≤ infD W E x := by
  obtain ⟨a0, ha0⟩ := hE
  apply le_csInf (⟨W.distance x a0, a0, ha0, rfl⟩ : Set.Nonempty {r : ℝ | ∃ a ∈ E, r = W.distance x a})
  rintro _ ⟨a, ha, rfl⟩
  exact h a ha

theorem infD_lip (W : WeightedGraph V) (hr : W.FiniteDistances) (E : Set V) (x y : V) :
    infD W E x ≤ W.distance x y + infD W E y := by
  by_cases hE : E.Nonempty
  · have : infD W E x - W.distance x y ≤ infD W E y := by
      apply le_infD W E y hE
      intro a ha
      have h1 := infD_le W E x ha
      have h2 := dist_triangle W hr x y a
      linarith
    linarith
  · rw [Set.not_nonempty_iff_eq_empty] at hE
    subst hE
    have h0 : ∀ z, infD W ∅ z = 0 := by
      intro z
      simp [infD]
    rw [h0, h0]
    have := dist_nonneg W x y
    linarith

theorem stageNorm_eq_infD (W : WeightedGraph V) (D : PlaneDrawing W.graph) {n : ℕ}
    (hn : n ≠ 0) (x : V) : stageNorm W D n x = infD W (D.earlierLayers n) x := by
  simp [stageNorm, hn, infD]

theorem distSet_finite [Finite V] (W : WeightedGraph V) :
    Set.Finite {r : ℝ | ∃ x y : V, r = W.distance x y} :=
  (Set.finite_range (fun p : V × V => W.distance p.1 p.2)).subset
    (by rintro r ⟨x, y, rfl⟩; exact ⟨(x, y), rfl⟩)

theorem dist_le_graphDiameter [Finite V] (W : WeightedGraph V) (x y : V) :
    W.distance x y ≤ graphDiameter W := by
  apply le_csSup ((distSet_finite W).insert 0).bddAbove
  exact Set.mem_insert_of_mem _ ⟨x, y, rfl⟩

theorem graphDiameter_nonneg [Finite V] (W : WeightedGraph V) : 0 ≤ graphDiameter W :=
  le_csSup ((distSet_finite W).insert 0).bddAbove (Set.mem_insert 0 _)

theorem stageNorm_nonneg [Finite V] (W : WeightedGraph V) (D : PlaneDrawing W.graph)
    (n : ℕ) (x : V) : 0 ≤ stageNorm W D n x := by
  by_cases hn : n = 0
  · simp only [stageNorm, hn, if_true]
    exact graphDiameter_nonneg W
  · rw [stageNorm_eq_infD W D hn]
    exact infD_nonneg W _ x

theorem stageNorm_lip (W : WeightedGraph V) (hr : W.FiniteDistances)
    (D : PlaneDrawing W.graph) (n : ℕ) (x y : V) :
    |stageNorm W D n x - stageNorm W D n y| ≤ W.distance x y := by
  by_cases hn : n = 0
  · simp only [stageNorm, hn, if_true, sub_self, abs_zero]
    exact dist_nonneg W x y
  · rw [stageNorm_eq_infD W D hn, stageNorm_eq_infD W D hn, abs_sub_le_iff]
    have h1 := infD_lip W hr (D.earlierLayers n) x y
    have h2 := infD_lip W hr (D.earlierLayers n) y x
    rw [dist_comm W y x] at h2
    constructor <;> linarith

theorem dist_le_length (W : WeightedGraph V) {x y : V} (h : W.graph.Adj x y) :
    W.distance x y ≤ W.length x y := by
  have := dist_le_walk W (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil)
  simpa [OAI.PlanarL1.walkLength] using this

/-- Components of the `i`-th residual set. -/
abbrev Fib {G : SimpleGraph V} (D : PlaneDrawing G) (i : ℕ) :=
  {S : Set V // ∃ x ∈ D.remaining i, S = comp G (D.remaining i) x}

/-- All blocks of the construction. -/
abbrev Blk {G : SimpleGraph V} (D : PlaneDrawing G) (k : ℕ) :=
  Σ i : Fin k, Fib D (i : ℕ)

theorem ebz_mem {S : Set V} {n : ℕ} (f : S → L1Vector n) {x : V} (hx : x ∈ S) :
    extendByZero f x = f ⟨x, hx⟩ := by
  unfold extendByZero
  rw [dif_pos hx]

theorem ebz_not_mem {S : Set V} {n : ℕ} (f : S → L1Vector n) {x : V} (hx : x ∉ S) :
    extendByZero f x = 0 := by
  unfold extendByZero
  rw [dif_neg hx]

theorem fib_zero (W : WeightedGraph V) (D : PlaneDrawing W.graph) (i : ℕ)
    [Fintype (Fib D i)] (N : Fib D i → ℕ) (Ψ : ∀ S : Fib D i, S.1 → L1Vector (N S))
    {x y : V} (hx : x ∉ D.remaining i) (hy : y ∉ D.remaining i) :
    ∑ S, ‖extendByZero (Ψ S) x - extendByZero (Ψ S) y‖ = 0 := by
  apply Finset.sum_eq_zero
  rintro ⟨S, x', hx', rfl⟩ -
  rw [ebz_not_mem _ (fun h => hx (comp_subset h)), ebz_not_mem _ (fun h => hy (comp_subset h))]
  simp

theorem fib_edge_bound [Fintype V] (W : WeightedGraph V) (hr : W.FiniteDistances)
    (D : PlaneDrawing W.graph) (i : ℕ)
    [Fintype (Fib D i)] (N : Fib D i → ℕ) (Ψ : ∀ S : Fib D i, S.1 → L1Vector (N S))
    (h1 : ∀ S z, ‖Ψ S z‖ = stageNorm W D i z)
    (h2 : ∀ S z z', ‖Ψ S z - Ψ S z'‖ ≤
      3 * (sub W S.1).distance z z' + 3 * |stageNorm W D i z - stageNorm W D i z'|)
    {x y : V} (hxy : W.graph.Adj x y) (hx : x ∈ D.remaining i) :
    ∑ S, ‖extendByZero (Ψ S) x - extendByZero (Ψ S) y‖ ≤ 6 * W.length x y := by
  have hw := W.nonnegative x y hxy
  have hdl := dist_le_length W hxy
  let S0 : Fib D i := ⟨comp W.graph (D.remaining i) x, x, hx, rfl⟩
  have hxS : x ∈ S0.1 := mem_comp_self hx
  rw [Finset.sum_eq_single S0]
  · rw [ebz_mem _ hxS]
    by_cases hy : y ∈ D.remaining i
    · have hyS : y ∈ S0.1 := adj_mem_comp hxy hx hy
      rw [ebz_mem _ hyS]
      have a1 := h2 S0 ⟨x, hxS⟩ ⟨y, hyS⟩
      have a2 : (sub W S0.1).distance ⟨x, hxS⟩ ⟨y, hyS⟩ ≤ W.length x y :=
        sub_dist_le_edge W S0.1 hxy hxS hyS
      have a3 := stageNorm_lip W hr D i x y
      have a3' : |stageNorm W D i (⟨x, hxS⟩ : S0.1) - stageNorm W D i (⟨y, hyS⟩ : S0.1)| ≤
          W.distance x y := a3
      linarith
    · have hyS : y ∉ S0.1 := fun h => hy (comp_subset h)
      rw [ebz_not_mem _ hyS, sub_zero, h1]
      have hi : i ≠ 0 := by
        rintro rfl
        exact hy (Set.mem_univ y)
      have : stageNorm W D i x ≤ W.distance x y := by
        rw [stageNorm_eq_infD W D hi]
        exact infD_le W _ x hy
      show stageNorm W D i x ≤ 6 * W.length x y
      linarith
  · rintro ⟨S, x', hx', rfl⟩ - hne
    have hxS' : x ∉ comp W.graph (D.remaining i) x' := by
      intro h
      apply hne
      apply Subtype.ext
      exact (comp_eq h).symm
    rw [ebz_not_mem _ hxS']
    by_cases hy : y ∈ comp W.graph (D.remaining i) x'
    · exfalso
      have hyR : y ∈ D.remaining i := comp_subset hy
      exact hxS' (comp_trans hy (adj_mem_comp hxy.symm hyR hx))
    · rw [ebz_not_mem _ hy]
      simp
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem blk_edge_bound [Fintype V] (W : WeightedGraph V) (hr : W.FiniteDistances)
    (D : PlaneDrawing W.graph) (k : ℕ) [∀ i : Fin k, Fintype (Fib D (i : ℕ))]
    (N : Blk D k → ℕ) (Ψ : ∀ b : Blk D k, b.2.1 → L1Vector (N b))
    (h1 : ∀ b z, ‖Ψ b z‖ = stageNorm W D b.1 z)
    (h2 : ∀ b z z', ‖Ψ b z - Ψ b z'‖ ≤
      3 * (sub W b.2.1).distance z z' + 3 * |stageNorm W D b.1 z - stageNorm W D b.1 z'|)
    {x y : V} (hxy : W.graph.Adj x y) :
    ∑ b, ‖extendByZero (Ψ b) x - extendByZero (Ψ b) y‖ ≤ 6 * k * W.length x y := by
  rw [Fintype.sum_sigma]
  have hi : ∀ i : Fin k,
      ∑ S : Fib D (i : ℕ), ‖extendByZero (Ψ ⟨i, S⟩) x - extendByZero (Ψ ⟨i, S⟩) y‖ ≤
        6 * W.length x y := by
    intro i
    by_cases hx : x ∈ D.remaining i
    · exact fib_edge_bound W hr D i (fun S => N ⟨i, S⟩) (fun S => Ψ ⟨i, S⟩)
        (fun S => h1 ⟨i, S⟩) (fun S => h2 ⟨i, S⟩) hxy hx
    · by_cases hy : y ∈ D.remaining i
      · have := fib_edge_bound W hr D i (fun S => N ⟨i, S⟩) (fun S => Ψ ⟨i, S⟩)
          (fun S => h1 ⟨i, S⟩) (fun S => h2 ⟨i, S⟩) hxy.symm hy
        simp only [norm_sub_rev (extendByZero _ y)] at this
        rw [W.symmetric y x] at this
        exact this
      · rw [fib_zero W D i (fun S => N ⟨i, S⟩) (fun S => Ψ ⟨i, S⟩) hx hy]
        have := W.nonnegative x y hxy
        linarith
  calc _ ≤ ∑ _i : Fin k, 6 * W.length x y := Finset.sum_le_sum (fun i _ => hi i)
    _ = 6 * k * W.length x y := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem walk_bound {E : Type} [SeminormedAddCommGroup E] (W : WeightedGraph V)
    (F0 : V → E) (c : ℝ)
    (hedge : ∀ u v, W.graph.Adj u v → ‖F0 u - F0 v‖ ≤ c * W.length u v)
    {x y : V} (p : W.graph.Walk x y) :
    ‖F0 x - F0 y‖ ≤ c * OAI.PlanarL1.walkLength W.length p := by
  induction p with
  | nil => simp [OAI.PlanarL1.walkLength]
  | cons h p ih =>
    rename_i u v w
    simp only [OAI.PlanarL1.walkLength, mul_add]
    have := norm_sub_le_norm_sub_add_norm_sub (F0 u) (F0 v) (F0 w)
    have := hedge _ _ h
    linarith

theorem sep_bound [Fintype V] (W : WeightedGraph V) (hr : W.FiniteDistances)
    (D : PlaneDrawing W.graph) (k : ℕ) (hk : D.remaining k = ∅)
    [∀ i : Fin k, Fintype (Fib D (i : ℕ))]
    (N : Blk D k → ℕ) (Ψ : ∀ b : Blk D k, b.2.1 → L1Vector (N b))
    (h1 : ∀ b z, ‖Ψ b z‖ = stageNorm W D b.1 z)
    (h3 : ∀ b : Blk D k, ∀ z z' c : b.2.1, c ∈ (D.induced b.2.1).boundary Set.univ →
      (1 / 4 : ℝ) * min ((sub W b.2.1).distance z z' - 4 * (sub W b.2.1).distance z c)
        (max (stageNorm W D b.1 z) (stageNorm W D b.1 z')) ≤ ‖Ψ b z - Ψ b z'‖)
    (hfd : ∀ b : Blk D k, (sub W b.2.1).FiniteDistances)
    (x y : V) :
    W.distance x y / 32 ≤ ∑ b, ‖extendByZero (Ψ b) x - extendByZero (Ψ b) y‖ := by
  classical
  have hsum0 : 0 ≤ ∑ b, ‖extendByZero (Ψ b) x - extendByZero (Ψ b) y‖ :=
    Finset.sum_nonneg (fun b _ => norm_nonneg _)
  set D0 := W.distance x y with hD0
  by_cases hD : D0 ≤ 0
  · linarith
  push Not at hD
  have hxk : x ∉ D.remaining k := by rw [hk]; exact Set.notMem_empty x
  obtain ⟨j, hjk, hxj⟩ := (not_mem_remaining_iff D x k).mp hxk
  have hex : ∃ i, ∃ a ∈ D.layer i, W.distance x a ≤ D0 / 8 :=
    ⟨j, x, hxj, by rw [dist_self]; linarith⟩
  set i := Nat.find hex with hi_def
  have hij : i ≤ j := Nat.find_min' hex ⟨x, hxj, by rw [dist_self]; linarith⟩
  have hik : i < k := lt_of_le_of_lt hij hjk
  have key : ∀ z, W.distance x z ≤ D0 / 8 → z ∈ D.remaining i := by
    intro z hz
    by_contra hzR
    obtain ⟨j', hj', hzl⟩ := (not_mem_remaining_iff D z i).mp hzR
    exact Nat.find_min hex hj' ⟨z, hzl, hz⟩
  have hx : x ∈ D.remaining i := key x (by rw [dist_self]; linarith)
  obtain ⟨a, ha, hda⟩ := Nat.find_spec hex
  have hnorm : D0 / 8 ≤ stageNorm W D i x := by
    by_cases hi0 : i = 0
    · simp only [stageNorm, hi0, if_true]
      have := dist_le_graphDiameter W x y
      linarith
    · rw [stageNorm_eq_infD W D hi0]
      apply le_infD
      · by_contra hne
        rw [Set.not_nonempty_iff_eq_empty] at hne
        have hRi : D.remaining i = Set.univ := by
          ext v
          constructor
          · intro _; trivial
          · intro _
            by_contra hv
            have : v ∈ (∅ : Set V) := by rw [← hne]; exact hv
            exact this
        have h1u : D.remaining 1 = Set.univ := by
          apply Set.eq_univ_of_univ_subset
          rw [← hRi]
          exact remaining_anti D (Nat.one_le_iff_ne_zero.mpr hi0)
        have := remaining_univ_of_one D h1u k
        rw [hk] at this
        exact Set.notMem_empty x (this ▸ Set.mem_univ x)
      · intro a' ha'
        by_contra hlt
        push Not at hlt
        exact ha' (key a' hlt.le)
  obtain ⟨p, hp⟩ := OuterplanarL1Tan.Dev.C3.PartA.exists_min_walk W hr x a
  have hps : ∀ z ∈ p.support, z ∈ D.remaining i := by
    intro z hz
    apply key
    have := OuterplanarL1Tan.Dev.C3.PartA.split_le W p hp z hz
    have := dist_nonneg W z a
    linarith
  have hsupp := walk_support_comp p hps
  let S := comp W.graph (D.remaining i) x
  let b0 : Blk D k := ⟨⟨i, hik⟩, ⟨S, x, hx, rfl⟩⟩
  have hxS : x ∈ S := mem_comp_self hx
  have haS : a ∈ S := hsupp a p.end_mem_support
  have hdS : (sub W S).distance ⟨x, hxS⟩ ⟨a, haS⟩ ≤ D0 / 8 := by
    have h' : (sub W S).distance ⟨x, hxS⟩ ⟨a, haS⟩ ≤ OAI.PlanarL1.walkLength W.length p :=
      sub_dist_le_walk W S p hsupp
    rw [hp] at h'
    linarith
  have hab : (⟨a, haS⟩ : S) ∈ (D.induced S).boundary Set.univ :=
    layer_mem_boundary D i S comp_subset a haS ha
  have hterm : D0 / 32 ≤ ‖extendByZero (Ψ b0) x - extendByZero (Ψ b0) y‖ := by
    have e1 : extendByZero (Ψ b0) x = Ψ b0 ⟨x, hxS⟩ := ebz_mem _ hxS
    rw [e1]
    by_cases hyS : y ∈ S
    · have e2 : extendByZero (Ψ b0) y = Ψ b0 ⟨y, hyS⟩ := ebz_mem _ hyS
      rw [e2]
      have a3 : (1 / 4 : ℝ) * min ((sub W S).distance ⟨x, hxS⟩ ⟨y, hyS⟩ -
          4 * (sub W S).distance ⟨x, hxS⟩ ⟨a, haS⟩)
          (max (stageNorm W D i x) (stageNorm W D i y)) ≤
          ‖Ψ b0 ⟨x, hxS⟩ - Ψ b0 ⟨y, hyS⟩‖ :=
        h3 b0 ⟨x, hxS⟩ ⟨y, hyS⟩ ⟨a, haS⟩ hab
      have a4 : W.distance x y ≤ (sub W S).distance ⟨x, hxS⟩ ⟨y, hyS⟩ :=
        dist_le_sub W S (hfd b0) ⟨x, hxS⟩ ⟨y, hyS⟩
      have a5 : D0 / 8 ≤ min ((sub W S).distance ⟨x, hxS⟩ ⟨y, hyS⟩ -
          4 * (sub W S).distance ⟨x, hxS⟩ ⟨a, haS⟩)
          (max (stageNorm W D i x) (stageNorm W D i y)) := by
        apply le_min
        · linarith
        · exact hnorm.trans (le_max_left _ _)
      linarith
    · have e2 : extendByZero (Ψ b0) y = 0 := ebz_not_mem _ hyS
      rw [e2, sub_zero]
      have : ‖Ψ b0 ⟨x, hxS⟩‖ = stageNorm W D i x := h1 b0 ⟨x, hxS⟩
      linarith
  have := Finset.single_le_sum (f := fun b => ‖extendByZero (Ψ b) x - extendByZero (Ψ b) y‖)
    (fun b _ => norm_nonneg _) (Finset.mem_univ b0)
  linarith

end OuterplanarL1Tan.Dev.T1.PartY
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.T1.PartY
open OuterplanarL1Tan.Linear OuterplanarL1Tan.Dev.T1
theorem theorem_1_dev {V : Type} [Fintype V] (W : WeightedGraph V)
    (reachable : W.FiniteDistances) (k : ℕ) (outerplanar : IsKOuterplanar W.graph k) :
    ∃ N : ℕ, ∃ F : V → L1Vector N, ∀ x y : V,
      W.distance x y ≤ ‖F x - F y‖ ∧
      ‖F x - F y‖ ≤ (192 : ℝ) * (k : ℝ) * W.distance x y := by
  classical
  obtain ⟨D, hk⟩ := outerplanar
  haveI : ∀ i : Fin k, Fintype (Fib D (i : ℕ)) := fun i => Fintype.ofFinite _
  have hfd : ∀ b : Blk D k, (sub W b.2.1).FiniteDistances := by
    rintro ⟨i, S, x, hx, rfl⟩
    exact sub_comp_finite W _ x
  have hne : ∀ b : Blk D k, b.2.1.Nonempty := by
    rintro ⟨i, S, x, hx, rfl⟩
    exact ⟨x, mem_comp_self hx⟩
  have key : ∀ b : Blk D k, ∃ n : ℕ, ∃ Ψ : b.2.1 → L1Vector n,
      (∀ z, ‖Ψ z‖ = stageNorm W D b.1 z) ∧
      (∀ z z', ‖Ψ z - Ψ z'‖ ≤ 3 * (sub W b.2.1).distance z z' +
        3 * |stageNorm W D b.1 z - stageNorm W D b.1 z'|) ∧
      (∀ z z' c : b.2.1, c ∈ (D.induced b.2.1).boundary Set.univ →
        (1 / 4 : ℝ) * min ((sub W b.2.1).distance z z' - 4 * (sub W b.2.1).distance z c)
          (max (stageNorm W D b.1 z) (stageNorm W D b.1 z')) ≤ ‖Ψ z - Ψ z'‖) :=
    fun b => component_map W D b.2.1 (hne b) (hfd b) (fun z => stageNorm W D b.1 z)
      (fun z => stageNorm_nonneg W D _ _)
  choose N Ψ h1 h2 h3 using key
  obtain ⟨M, F0, hF0⟩ := block_sum N (fun b => extendByZero (Ψ b))
  refine ⟨M, fun x => (32 : ℝ) • F0 x, fun x y => ?_⟩
  have hs : ‖(32 : ℝ) • F0 x - (32 : ℝ) • F0 y‖ = 32 * ‖F0 x - F0 y‖ := by
    rw [← smul_sub, norm_smul]
    norm_num
  show W.distance x y ≤ ‖(32 : ℝ) • F0 x - (32 : ℝ) • F0 y‖ ∧
    ‖(32 : ℝ) • F0 x - (32 : ℝ) • F0 y‖ ≤ (192 : ℝ) * (k : ℝ) * W.distance x y
  rw [hs]
  constructor
  · have := sep_bound W reachable D k hk N Ψ h1 h3 hfd x y
    rw [← hF0] at this
    linarith
  · have hedge : ∀ u v, W.graph.Adj u v → ‖F0 u - F0 v‖ ≤ (6 * k) * W.length u v := by
      intro u v huv
      rw [hF0]
      exact blk_edge_bound W reachable D k N Ψ h1 h2 huv
    obtain ⟨p, hp⟩ := OuterplanarL1Tan.Dev.C3.PartA.exists_min_walk W reachable x y
    have := walk_bound W F0 (6 * k) hedge p
    rw [hp] at this
    linarith

end OuterplanarL1Tan.Dev.T1.PartY
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Dev.T1
open OuterplanarL1Tan.Linear
/-! ## Part Y stub -/
alias theorem_1_dev := OuterplanarL1Tan.Dev.T1.PartY.theorem_1_dev

end OuterplanarL1Tan.Dev.T1
end

section
set_option autoImplicit false
namespace OuterplanarL1Tan.Linear
theorem chk_theorem_1 {V : Type} [Fintype V] (W : WeightedGraph V)
    (reachable : W.FiniteDistances) (k : ℕ) (outerplanar : IsKOuterplanar W.graph k) :
    ∃ N : ℕ, ∃ F : V → L1Vector N, ∀ x y : V,
      W.distance x y ≤ ‖F x - F y‖ ∧
      ‖F x - F y‖ ≤ (192 : ℝ) * (k : ℝ) * W.distance x y :=
  OuterplanarL1Tan.Dev.T1.theorem_1_dev W reachable k outerplanar

end OuterplanarL1Tan.Linear
end

theorem solution : type_of% @OuterplanarL1Tan.Linear.chk_theorem_1 := @OuterplanarL1Tan.Linear.chk_theorem_1
