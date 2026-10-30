-- Prove2me | solution 1 for WilliamsonShmoys.graph_reachable_of_carrier_component__p2m_188e1412_5b81_4b4f_8125_7b7ad68311d3_a1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T00:09:51.909734+00:00
-- url     : https://prove2.me/submissions/8ebbee5d-a039-4584-a620-6fae62af5836

import Definitions.Def_WilliamsonShmoys_DrawingCarrier__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Connected.Basic

open Set SimpleGraph

noncomputable def drawingPiece {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (S : Set V) : Set (ℝ × ℝ) :=
  (⋃ w ∈ S, {p w}) ∪
  (⋃ u : V, ⋃ v : V, ⋃ (_ : u < v ∧ G.Adj u v ∧ u ∈ S), arc u v '' Set.Icc 0 1)

lemma drawingPiece_compact {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ) (S : Set V)
    (ha : ∀ u v, u < v → G.Adj u v → ContinuousOn (arc u v) (Set.Icc 0 1)) :
    IsCompact (drawingPiece G p arc S) := by
  classical
  unfold drawingPiece
  apply IsCompact.union
  · apply isCompact_iUnion
    intro w
    apply isCompact_iUnion
    intro hw
    exact isCompact_singleton
  · apply isCompact_iUnion
    intro u
    apply isCompact_iUnion
    intro v
    apply isCompact_iUnion
    intro huv
    exact isCompact_Icc.image_of_continuousOn (ha u v huv.1 huv.2.1)


abbrev drawingCarrier {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ) : Set (ℝ × ℝ) :=
  WilliamsonShmoys_DrawingCarrier__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12 G p arc

lemma drawingPiece_cover {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ) (S : Set V) :
    drawingCarrier G p arc = drawingPiece G p arc S ∪ drawingPiece G p arc Sᶜ := by
  classical
  ext z
  simp only [drawingCarrier, drawingPiece, mem_setOf_eq, mem_union, mem_iUnion,
    mem_singleton_iff, mem_image, mem_compl_iff]
  constructor
  · rintro (⟨w, rfl⟩ | ⟨u, v, huv, hadj, t, ht, rfl⟩)
    · by_cases hw : w ∈ S
      · exact Or.inl (Or.inl ⟨w, hw, rfl⟩)
      · exact Or.inr (Or.inl ⟨w, hw, rfl⟩)
    · by_cases hu : u ∈ S
      · exact Or.inl (Or.inr ⟨u, v, ⟨huv, hadj, hu⟩, t, ht, rfl⟩)
      · exact Or.inr (Or.inr ⟨u, v, ⟨huv, hadj, hu⟩, t, ht, rfl⟩)
  · rintro ((⟨w, _, rfl⟩ | ⟨u, v, ⟨huv, hadj, _⟩, t, ht, rfl⟩) |
      (⟨w, _, rfl⟩ | ⟨u, v, ⟨huv, hadj, _⟩, t, ht, rfl⟩))
    · exact Or.inl ⟨w, rfl⟩
    · exact Or.inr ⟨u, v, huv, hadj, t, ht, rfl⟩
    · exact Or.inl ⟨w, rfl⟩
    · exact Or.inr ⟨u, v, huv, hadj, t, ht, rfl⟩


lemma arc_meeting_reachable {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (ha : ∀ u v, u < v → G.Adj u v → arc u v 0 = p u ∧ arc u v 1 = p v)
    (hi : ∀ u v x y, u < v → x < y → G.Adj u v → G.Adj x y →
      (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
      arc u v t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (u v x y : V) (huv : u < v) (hxy : x < y) (hGuv : G.Adj u v) (hGxy : G.Adj x y)
    (t s : ℝ) (ht : t ∈ Set.Icc 0 1) (hs : s ∈ Set.Icc 0 1)
    (he : arc u v t = arc x y s) : G.Reachable u x := by
  by_cases hpairs : (u, v) = (x, y)
  · have hux : u = x := congrArg Prod.fst hpairs
    subst x
    exact SimpleGraph.Reachable.refl u
  · obtain ⟨ht0 | ht1, hs0 | hs1⟩ := hi u v x y huv hxy hGuv hGxy hpairs t ht s hs he
    · have hux : u = x := hp (by simpa [ht0, hs0, (ha u v huv hGuv).1,
          (ha x y hxy hGxy).1] using he)
      subst x
      exact SimpleGraph.Reachable.refl u
    · have huy : u = y := hp (by simpa [ht0, hs1, (ha u v huv hGuv).1,
          (ha x y hxy hGxy).2] using he)
      subst y
      exact hGxy.reachable.symm
    · have hvx : v = x := hp (by simpa [ht1, hs0, (ha u v huv hGuv).2,
          (ha x y hxy hGxy).1] using he)
      subst x
      exact hGuv.reachable
    · have hvy : v = y := hp (by simpa [ht1, hs1, (ha u v huv hGuv).2,
          (ha x y hxy hGxy).2] using he)
      subst y
      exact hGuv.reachable.trans hGxy.reachable.symm


lemma vertex_on_arc_is_endpoint {V X : Type} (p : V → X) (a : ℝ → X) (u v w : V)
    (hp : Function.Injective p) (h0 : a 0 = p u) (h1 : a 1 = p v)
    (hinterior : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, a t ≠ p w)
    (t : ℝ) (ht : t ∈ Set.Icc 0 1) (h : a t = p w) : w = u ∨ w = v := by
  rcases lt_or_eq_of_le ht.1 with hpos | hzero
  · rcases lt_or_eq_of_le ht.2 with hlt | hone
    · exact False.elim (hinterior t ⟨hpos, hlt⟩ w h)
    · subst t
      exact Or.inr (hp (h.symm.trans h1))
  · subst t
    exact Or.inl (hp (h.symm.trans h0))

lemma drawingPiece_disjoint {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ) (base : V)
    (hp : Function.Injective p)
    (ha : ∀ u v, u < v → G.Adj u v →
      arc u v 0 = p u ∧ arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w)
    (hi : ∀ u v x y, u < v → x < y → G.Adj u v → G.Adj x y →
      (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
      arc u v t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) :
    Disjoint (drawingPiece G p arc {w | G.Reachable base w})
      (drawingPiece G p arc {w | G.Reachable base w}ᶜ) := by
  classical
  apply Set.disjoint_left.mpr
  intro z hzA hzB
  simp only [drawingPiece, mem_union, mem_iUnion, mem_singleton_iff, mem_image,
    mem_compl_iff, mem_setOf_eq] at hzA hzB
  rcases hzA with ⟨w, hw, hzw⟩ | ⟨u, v, ⟨huv, hguv, hu⟩, t, ht, htz⟩
  · rcases hzB with ⟨w', hw', hzw'⟩ | ⟨x, y, ⟨hxy, hgxy, hx⟩, s, hs, hsz⟩
    · have hww : w = w' := hp (hzw.symm.trans hzw')
      exact hw' (hww ▸ hw)
    · have hwxy : w = x ∨ w = y := vertex_on_arc_is_endpoint p (arc x y) x y w hp
        (ha x y hxy hgxy).1 (ha x y hxy hgxy).2.1 (ha x y hxy hgxy).2.2
        s hs (hsz.trans hzw)
      rcases hwxy with h | h
      · exact hx (h ▸ hw)
      · exact hx ((h ▸ hw).trans hgxy.reachable.symm)
  · rcases hzB with ⟨w, hw, hzw⟩ | ⟨x, y, ⟨hxy, hgxy, hx⟩, s, hs, hsz⟩
    · have hwuv : w = u ∨ w = v := vertex_on_arc_is_endpoint p (arc u v) u v w hp
        (ha u v huv hguv).1 (ha u v huv hguv).2.1 (ha u v huv hguv).2.2
        t ht (htz.trans hzw)
      rcases hwuv with h | h
      · exact hw (h ▸ hu)
      · exact hw (h ▸ hu.trans hguv.reachable)
    · have hux := arc_meeting_reachable G p arc hp
        (fun u v huv hguv ↦ ⟨(ha u v huv hguv).1, (ha u v huv hguv).2.1⟩)
        hi u v x y huv hxy hguv hgxy t s ht hs (htz.trans hsz.symm)
      exact hx (hu.trans hux)


lemma connected_inside_left {X : Type} [TopologicalSpace X] (F A B : Set X) (x : X)
    (hA : IsClosed A) (hB : IsClosed B) (hdis : Disjoint A B)
    (hcover : F ⊆ A ∪ B) (hx : x ∈ A) :
    connectedComponentIn F x ⊆ A := by
  classical
  by_cases hxF : x ∈ F
  · intro y hy
    by_contra hyA
    have hyB : y ∈ B := (hcover (connectedComponentIn_subset F x hy)).resolve_left hyA
    have hconnected := isPreconnected_closed_iff.mp (isPreconnected_connectedComponentIn
      (F := F) (x := x)) A B hA hB
      ((connectedComponentIn_subset F x).trans hcover)
      ⟨x, mem_connectedComponentIn hxF, hx⟩ ⟨y, hy, hyB⟩
    obtain ⟨z, _, hzA, hzB⟩ := hconnected
    exact Set.disjoint_left.mp hdis hzA hzB
  · rw [connectedComponentIn_eq_empty hxF]
    exact Set.empty_subset A



theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (ha : ∀ u v, u < v → G.Adj u v →
      ContinuousOn (arc u v) (Set.Icc 0 1) ∧
      Set.InjOn (arc u v) (Set.Icc 0 1) ∧
      arc u v 0 = p u ∧ arc u v 1 = p v ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc u v t ≠ p w)
    (hi : ∀ u v x y, u < v → x < y → G.Adj u v → G.Adj x y →
      (u, v) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc 0 1,
        arc u v t = arc x y s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (u v : V) :
    p v ∈ connectedComponentIn
        (WilliamsonShmoys_DrawingCarrier__p2m_e9afcc95_ed4a_4c92_9086_c25618dbb046_a12 G p arc) (p u) →
      G.Reachable u v := by
  classical
  let S : Set V := {w | G.Reachable u w}
  have haCompact : ∀ a b, a < b → G.Adj a b → ContinuousOn (arc a b) (Set.Icc 0 1) :=
    fun a b hab hG ↦ (ha a b hab hG).1
  have haEnds : ∀ a b, a < b → G.Adj a b →
      arc a b 0 = p a ∧ arc a b 1 = p b ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w :=
    fun a b hab hG ↦ (ha a b hab hG).2.2
  have hclosedA : IsClosed (drawingPiece G p arc S) :=
    (drawingPiece_compact G p arc S haCompact).isClosed
  have hclosedB : IsClosed (drawingPiece G p arc Sᶜ) :=
    (drawingPiece_compact G p arc Sᶜ haCompact).isClosed
  have hdis : Disjoint (drawingPiece G p arc S) (drawingPiece G p arc Sᶜ) :=
    drawingPiece_disjoint G p arc u hp haEnds hi
  have hbase : p u ∈ drawingPiece G p arc S := by
    simp only [drawingPiece, Set.mem_union, Set.mem_iUnion, Set.mem_singleton_iff]
    exact Or.inl ⟨u, SimpleGraph.Reachable.refl u, rfl⟩
  have hcover : drawingCarrier G p arc ⊆ drawingPiece G p arc S ∪ drawingPiece G p arc Sᶜ :=
    (drawingPiece_cover G p arc S).subset
  intro hcomponent
  have hvA : p v ∈ drawingPiece G p arc S :=
    connected_inside_left (drawingCarrier G p arc) (drawingPiece G p arc S)
      (drawingPiece G p arc Sᶜ) (p u) hclosedA hclosedB hdis hcover hbase hcomponent
  by_contra hn
  have hvB : p v ∈ drawingPiece G p arc Sᶜ := by
    simp only [drawingPiece, Set.mem_union, Set.mem_iUnion, Set.mem_singleton_iff,
      Set.mem_compl_iff, Set.mem_setOf_eq]
    exact Or.inl ⟨v, hn, rfl⟩
  exact Set.disjoint_left.mp hdis hvA hvB

#print axioms solution
