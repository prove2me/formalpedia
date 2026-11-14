-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_local_edge_extension__p2m_3b9c1b25_36f2_49fb_9760_e5ee7be0caf4_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-13T16:28:55.542208+00:00
-- url     : https://prove2.me/submissions/4354e0b4-b9a6-4ba2-a4d2-2d9a7f9ea433
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_rooted_drawing_empty_strip__p2m_7e85fb9b_7eae_4d06_bade_329c1839a3ae_a54
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open WilliamsonShmoys

/-!
Partial work, not a proof of the assigned theorem. No `solution` declaration
is claimed. The remaining geometric normalization is described at the end.
The lemmas below have not been checked by a compiler in this invocation.
-/

/-- The no-walk assumption provides a nontrivial cut respected by every old edge. -/
private theorem separated_cut__p2m_7e85fb9b_7eae_4d06_bade_329c1839a3ae_a50
    {V : Type} (G : SimpleGraph V) (u v : V)
    (hsep : ¬ Nonempty (G.Walk u v)) :
    u ≠ v ∧ ¬ G.Adj u v ∧
      ∃ A : Set V, u ∈ A ∧ v ∉ A ∧
        ∀ a b, G.Adj a b → (a ∈ A ↔ b ∈ A) := by
  have hne : u ≠ v := by
    intro h
    subst v
    exact hsep ⟨SimpleGraph.Walk.nil⟩
  refine ⟨hne, fun h => hsep ⟨h.toWalk⟩, ?_⟩
  refine ⟨{w | G.Reachable u w}, SimpleGraph.Reachable.refl u, hsep, ?_⟩
  intro a b hab
  exact ⟨fun h => h.trans hab.reachable,
    fun h => h.trans hab.symm.reachable⟩

/-- Insert a supplied simple arc, retaining every old edge and drawing condition.
Only the ordered pair representing the new undirected edge is changed. -/
private theorem insert_ordered_arc__p2m_7e85fb9b_7eae_4d06_bade_329c1839a3ae_a50
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hEdge : ∀ a b, a < b → G.Adj a b →
      ContinuousOn (arc a b) (Set.Icc 0 1) ∧
      Set.InjOn (arc a b) (Set.Icc 0 1) ∧
      arc a b 0 = p a ∧ arc a b 1 = p b ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w)
    (hCross : ∀ a b x y, a < b → x < y → G.Adj a b → G.Adj x y →
      (a, b) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ s ∈ Set.Icc (0 : ℝ) 1, arc a b t = arc x y s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (u v : V) (huv : u < v) (gamma : ℝ → ℝ × ℝ)
    (hcont : ContinuousOn gamma (Set.Icc 0 1))
    (hinj : Set.InjOn gamma (Set.Icc 0 1))
    (hzero : gamma 0 = p u) (hone : gamma 1 = p v)
    (hvertex : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w)
    (hbridge : ∀ a b, a < b → G.Adj a b →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        gamma t = arc a b s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    ∃ H : SimpleGraph V,
      HasPlanarDrawingOn H ∧ G.edgeFinset ⊆ H.edgeFinset ∧ H.Adj u v := by
  classical
  letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
    fun K => Classical.decRel K.Adj
  let H : SimpleGraph V :=
    { Adj := fun a b => G.Adj a b ∨ (a = u ∧ b = v) ∨ (a = v ∧ b = u)
      symm := ⟨by
        intro a b h
        rcases h with h | h | h
        · exact Or.inl h.symm
        · exact Or.inr (Or.inr ⟨h.2, h.1⟩)
        · exact Or.inr (Or.inl ⟨h.2, h.1⟩)⟩
      loopless := ⟨by
        intro a h
        rcases h with h | h | h
        · exact G.irrefl h
        · exact (ne_of_lt huv) (h.1.symm.trans h.2)
        · exact (ne_of_lt huv) (h.2.symm.trans h.1)⟩ }
  have hGH : G ≤ H := fun _ _ h => Or.inl h
  have hcases : ∀ a b, a < b → H.Adj a b →
      (a = u ∧ b = v) ∨ G.Adj a b := by
    intro a b hab h
    rcases h with h | h | h
    · exact Or.inr h
    · exact Or.inl h
    · have hrev : v < u := by simpa only [h.1, h.2] using hab
      exact (not_lt_of_ge (le_of_lt huv) hrev).elim
  let q : V → V → ℝ → ℝ × ℝ :=
    fun a b => if a = u ∧ b = v then gamma else arc a b
  have hDraw : HasPlanarDrawingOn H := by
    refine ⟨p, q, hp, ?_, ?_⟩
    · intro a b hab hH
      by_cases hnew : a = u ∧ b = v
      · rcases hnew with ⟨hau, hbv⟩
        subst a
        subst b
        simpa [q] using
          (show ContinuousOn gamma (Set.Icc 0 1) ∧
            Set.InjOn gamma (Set.Icc 0 1) ∧
            gamma 0 = p u ∧ gamma 1 = p v ∧
            ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w from
              ⟨hcont, hinj, hzero, hone, hvertex⟩)
      · have hold : G.Adj a b := (hcases a b hab hH).resolve_left hnew
        simpa only [q, if_neg hnew] using hEdge a b hab hold
    · intro a b x y hab hxy hHab hHxy hne t ht s hs heq
      by_cases hnab : a = u ∧ b = v
      · by_cases hnxy : x = u ∧ y = v
        · exact (hne (Prod.ext (hnab.1.trans hnxy.1.symm)
            (hnab.2.trans hnxy.2.symm))).elim
        · have hold : G.Adj x y := (hcases x y hxy hHxy).resolve_left hnxy
          have heq' : gamma t = arc x y s := by
            simpa only [q, if_pos hnab, if_neg hnxy] using heq
          exact hbridge x y hxy hold t ht s hs heq'
      · have holdab : G.Adj a b := (hcases a b hab hHab).resolve_left hnab
        by_cases hnxy : x = u ∧ y = v
        · have heq' : gamma s = arc a b t := by
            simpa only [q, if_neg hnab, if_pos hnxy] using heq.symm
          have h := hbridge a b hab holdab s hs t ht heq'
          exact ⟨h.2, h.1⟩
        · have holdxy : G.Adj x y := (hcases x y hxy hHxy).resolve_left hnxy
          have heq' : arc a b t = arc x y s := by
            simpa only [q, if_neg hnab, if_neg hnxy] using heq
          exact hCross a b x y hab hxy holdab holdxy hne t ht s hs heq'
  exact ⟨H, hDraw, SimpleGraph.edgeFinset_mono hGH,
    Or.inr (Or.inl ⟨rfl, rfl⟩)⟩

/-- Reverse a supplied arc when the vertex order is opposite to its orientation. -/
private theorem insert_arc__p2m_7e85fb9b_7eae_4d06_bade_329c1839a3ae_a50
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hp : Function.Injective p)
    (hEdge : ∀ a b, a < b → G.Adj a b →
      ContinuousOn (arc a b) (Set.Icc 0 1) ∧
      Set.InjOn (arc a b) (Set.Icc 0 1) ∧
      arc a b 0 = p a ∧ arc a b 1 = p b ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w)
    (hCross : ∀ a b x y, a < b → x < y → G.Adj a b → G.Adj x y →
      (a, b) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ s ∈ Set.Icc (0 : ℝ) 1, arc a b t = arc x y s →
          (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1))
    (u v : V) (huv : u ≠ v) (gamma : ℝ → ℝ × ℝ)
    (hcont : ContinuousOn gamma (Set.Icc 0 1))
    (hinj : Set.InjOn gamma (Set.Icc 0 1))
    (hzero : gamma 0 = p u) (hone : gamma 1 = p v)
    (hvertex : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w)
    (hbridge : ∀ a b, a < b → G.Adj a b →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        gamma t = arc a b s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    ∃ H : SimpleGraph V,
      HasPlanarDrawingOn H ∧ G.edgeFinset ⊆ H.edgeFinset ∧ H.Adj u v := by
  classical
  rcases lt_or_gt_of_ne huv with hlt | hlt
  · exact insert_ordered_arc__p2m_7e85fb9b_7eae_4d06_bade_329c1839a3ae_a50
      G p arc hp hEdge hCross u v hlt gamma hcont hinj hzero hone hvertex hbridge
  · have hmaps : Set.MapsTo (fun t : ℝ => 1 - t) (Set.Icc 0 1) (Set.Icc 0 1) := by
      intro t ht
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hrcont : ContinuousOn (fun t => gamma (1 - t)) (Set.Icc 0 1) :=
      hcont.comp (continuous_const.sub continuous_id).continuousOn hmaps
    have hrinj : Set.InjOn (fun t => gamma (1 - t)) (Set.Icc 0 1) := by
      intro t ht s hs heq
      have h := hinj (hmaps ht) (hmaps hs) heq
      linarith
    have hrzero : gamma (1 - 0) = p v := by simpa only [sub_zero] using hone
    have hrone : gamma (1 - 1) = p u := by simpa only [sub_self] using hzero
    have hrvertex : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma (1 - t) ≠ p w := by
      intro t ht w
      exact hvertex (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ w
    have hrbridge : ∀ a b, a < b → G.Adj a b →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          gamma (1 - t) = arc a b s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1) := by
      intro a b hab hG t ht s hs heq
      have h := hbridge a b hab hG (1 - t) (hmaps ht) s hs heq
      refine ⟨?_, h.2⟩
      rcases h.1 with h | h
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
    obtain ⟨H, hH, hsub, hvu⟩ :=
      insert_ordered_arc__p2m_7e85fb9b_7eae_4d06_bade_329c1839a3ae_a50
        G p arc hp hEdge hCross v u hlt (fun t => gamma (1 - t))
        hrcont hrinj hrzero hrone hrvertex hrbridge
    exact ⟨H, hH, hsub, hvu.symm⟩

/-- Once the drawing avoids an open vertical strip with the prescribed roots
at its two boundary points, the horizontal segment is a safe joining arc.
Boundary intersections with old arcs are handled using vertex avoidance;
strict half-plane inequalities at old edge endpoints are not required. -/
private theorem extension_of_empty_strip__p2m_7e85fb9b_7eae_4d06_bade_329c1839a3ae_a50
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (u v : V) (huv : u ≠ v)
    (hstrip : ∃ (p : V → ℝ × ℝ) (arc : V → V → ℝ → ℝ × ℝ),
      Function.Injective p ∧
      (∀ a b, a < b → G.Adj a b →
        ContinuousOn (arc a b) (Set.Icc 0 1) ∧
        Set.InjOn (arc a b) (Set.Icc 0 1) ∧
        arc a b 0 = p a ∧ arc a b 1 = p b ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc a b t ≠ p w) ∧
      (∀ a b x y, a < b → x < y → G.Adj a b → G.Adj x y →
        (a, b) ≠ (x, y) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ∀ s ∈ Set.Icc (0 : ℝ) 1, arc a b t = arc x y s →
            (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1)) ∧
      p u = (0, 0) ∧ p v = (1, 0) ∧
      (∀ w, (p w).1 ≤ 0 ∨ 1 ≤ (p w).1) ∧
      (∀ a b, a < b → G.Adj a b → ∀ s ∈ Set.Icc (0 : ℝ) 1,
        (arc a b s).1 ≤ 0 ∨ 1 ≤ (arc a b s).1)) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    ∃ H : SimpleGraph V,
      HasPlanarDrawingOn H ∧ G.edgeFinset ⊆ H.edgeFinset ∧ H.Adj u v := by
  classical
  rcases hstrip with ⟨p, arc, hp, hEdge, hCross, hu, hv, hpStrip, haStrip⟩
  let gamma : ℝ → ℝ × ℝ := fun t => (t, 0)
  have hcont : ContinuousOn gamma (Set.Icc 0 1) :=
    (continuous_id.prodMk continuous_const).continuousOn
  have hinj : Set.InjOn gamma (Set.Icc 0 1) := by
    intro t ht s hs h
    exact congrArg Prod.fst h
  have hzero : gamma 0 = p u := hu.symm
  have hone : gamma 1 = p v := hv.symm
  have hvertex : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ w, gamma t ≠ p w := by
    intro t ht w heq
    have hx : t = (p w).1 := congrArg Prod.fst heq
    rcases hpStrip w with hw | hw
    · linarith [ht.1]
    · linarith [ht.2]
  have hbridge : ∀ a b, a < b → G.Adj a b →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        gamma t = arc a b s → (t = 0 ∨ t = 1) ∧ (s = 0 ∨ s = 1) := by
    intro a b hab hG t ht s hs heq
    have hx : t = (arc a b s).1 := congrArg Prod.fst heq
    have htEnd : t = 0 ∨ t = 1 := by
      rcases haStrip a b hab hG s hs with h | h
      · exact Or.inl (by linarith [ht.1])
      · exact Or.inr (by linarith [ht.2])
    refine ⟨htEnd, ?_⟩
    by_cases hs0 : s = 0
    · exact Or.inl hs0
    by_cases hs1 : s = 1
    · exact Or.inr hs1
    have hsInt : s ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), lt_of_le_of_ne hs.2 hs1⟩
    have havoid := (hEdge a b hab hG).2.2.2.2 s hsInt
    rcases htEnd with ht0 | ht1
    · have htroot : gamma t = p u := by simpa only [ht0] using hzero
      exact (havoid u (heq.symm.trans htroot)).elim
    · have htroot : gamma t = p v := by simpa only [ht1] using hone
      exact (havoid v (heq.symm.trans htroot)).elim
  exact insert_arc__p2m_7e85fb9b_7eae_4d06_bade_329c1839a3ae_a50
    G p arc hp hEdge hCross u v huv gamma hcont hinj hzero hone hvertex hbridge

/-
UNPROVED NORMALIZATION:
For the component cut A from `separated_cut`, construct a new drawing of G
whose A vertices and edges are in x ≤ 0, whose complementary vertices and
edges are in x ≥ 1, and whose selected roots are (0,0) and (1,0).

The supplied drawing cannot merely be translated componentwise: a prescribed
root may be enclosed by a cycle in its own component. One first needs a rooted
plane redrawing/exposure theorem, with continuity, injectivity, avoidance of
vertices, and all endpoint intersection conditions. Neither the arbitrary-
endpoint component-bridge theorem nor connected-supergraph existence supplies
this normalization. Global affine transformations do not expose an enclosed
root. No assertion that the assigned target follows without this step is made.
-/

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hJ : HasPlanarDrawingOn J)
    (u v : V) (hsep : ¬ Nonempty (J.Walk u v)) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    ∃ H : SimpleGraph V,
      HasPlanarDrawingOn H ∧
      J.edgeFinset ⊆ H.edgeFinset ∧
      H.Adj u v := by
  classical
  have huv : u ≠ v := by
    intro heq
    subst v
    exact hsep ⟨SimpleGraph.Walk.nil⟩
  exact extension_of_empty_strip__p2m_7e85fb9b_7eae_4d06_bade_329c1839a3ae_a50 J u v huv
    (WilliamsonShmoys.rooted_drawing_empty_strip__p2m_7e85fb9b_7eae_4d06_bade_329c1839a3ae_a54
      J hJ u v hsep)