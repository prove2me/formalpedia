-- Prove2me | solution 1 for PlanarQueue.Planar.planar_of_treewidth_three_no_K33_minor
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T16:03:11.746398+00:00
-- url     : https://prove2.me/submissions/1b651a4e-a83d-4ceb-ad09-7fcb0421d76e

import Mathlib
import Definitions.Def_PlanarQueue_Planar_Setting
import Definitions.Def_RobertsonSeymour1986_GM5_IsMinor

set_option autoImplicit false
set_option linter.all false
set_option linter.deprecated false

/-! PQL5 / KV-comb lemma YD: a Y-Delta exchange (delete a vertex `v` adjacent to `a, b, c`, add edges
among `a, b, c`) cannot create a minor of a triangle-free graph without isolated vertices (e.g. K₃,₃).
Used in the 3-connected step of the combinatorial Kratochvil-Vaner completion. -/

namespace PQL5

open RobertsonSeymour1986.GM5

/-- `x` is one of `a, b, c`. -/
def In3 {V : Type} (a b c x : V) : Prop := x = a ∨ x = b ∨ x = c

theorem four_of_three {V : Type} {a b c p q r s : V} (hp : In3 a b c p)
    (hq : In3 a b c q) (hr : In3 a b c r) (hs : In3 a b c s)
    (h1 : p ≠ q) (h2 : p ≠ r) (h3 : p ≠ s) (h4 : q ≠ r) (h5 : q ≠ s) (h6 : r ≠ s) : False := by
  unfold In3 at hp hq hr hs
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    rcases hr with rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl <;> simp_all

/-- A property holding at one vertex of a connected induced set and closed under induced adjacency
holds on the whole set. -/
theorem induce_closed {V : Type} {G : SimpleGraph V} {s : Set V} (hc : (G.induce s).Connected)
    (P : V → Prop) {x0 : V} (hx0 : x0 ∈ s) (h0 : P x0)
    (hstep : ∀ x y, x ∈ s → y ∈ s → G.Adj x y → P x → P y) : ∀ y ∈ s, P y := by
  intro y hy
  have hr := hc.preconnected ⟨x0, hx0⟩ ⟨y, hy⟩
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  have key : ∀ u : s, Relation.ReflTransGen (G.induce s).Adj ⟨x0, hx0⟩ u → P u.1 := by
    intro u hu
    induction hu with
    | refl => exact h0
    | @tail b c _ hbc ih =>
      exact hstep b.1 c.1 b.2 c.2 (by simpa using hbc) ih
  exact key ⟨y, hy⟩ hr

/-- Adding a vertex `v` to a set connected in `G''`, where every `G''`-edge of the set is a `G`-edge
or joins two `G`-neighbours of `v`, gives a set connected in `G`. -/
theorem induce_insert_connected {V : Type} {G G'' : SimpleGraph V} {s : Set V} {v : V}
    (hc : (G''.induce s).Connected)
    (hstep : ∀ x y, x ∈ s → y ∈ s → G''.Adj x y → G.Adj x y ∨ (G.Adj v x ∧ G.Adj v y))
    {x0 : V} (hx0 : x0 ∈ s) (hv0 : G.Adj v x0) :
    (G.induce (insert v s)).Connected := by
  have hv : v ∈ insert v s := Set.mem_insert v s
  have hall : ∀ y ∈ s, ∃ hy : y ∈ insert v s,
      (G.induce (insert v s)).Reachable ⟨v, hv⟩ ⟨y, hy⟩ := by
    refine induce_closed hc (fun y => ∃ hy : y ∈ insert v s,
      (G.induce (insert v s)).Reachable ⟨v, hv⟩ ⟨y, hy⟩) hx0 ?_ ?_
    · refine ⟨Set.mem_insert_of_mem v hx0, SimpleGraph.Adj.reachable ?_⟩
      simpa using hv0
    · rintro x y _ hy hxy ⟨_, hr⟩
      refine ⟨Set.mem_insert_of_mem v hy, ?_⟩
      rcases hstep x y ‹_› hy hxy with h | ⟨_, h⟩
      · exact hr.trans (SimpleGraph.Adj.reachable (by simpa using h))
      · exact SimpleGraph.Adj.reachable (by simpa using h)
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨v, hv⟩, ?_⟩
  rintro ⟨y, hy⟩
  rcases Set.mem_insert_iff.1 hy with h | h
  · subst h
    exact SimpleGraph.Reachable.refl _
  · obtain ⟨_, h'⟩ := hall y h
    exact h'

/-- **Lemma YD.** Let `v` be adjacent in `G` to `a, b, c`, and let `G''` have no edge at `v` and only
edges of `G` or edges among `a, b, c`. Then every minor of `G''` that is triangle-free and has no
isolated vertex is a minor of `G`. -/
theorem minor_YDelta {W V : Type} (K : SimpleGraph W)
    (hKtri : ∀ x y z, K.Adj x y → K.Adj y z → ¬ K.Adj x z)
    (hKiso : ∀ w, ∃ w', K.Adj w w')
    (G G'' : SimpleGraph V) (v a b c : V)
    (hva : G.Adj v a) (hvb : G.Adj v b) (hvc : G.Adj v c)
    (hG'' : ∀ x y, G''.Adj x y → x ≠ v ∧ (G.Adj x y ∨ (In3 a b c x ∧ In3 a b c y)))
    (hm : IsMinor K G'') : IsMinor K G := by
  classical
  obtain ⟨β, hβ, hpw, hadj⟩ := hm
  have hvA : ∀ x, In3 a b c x → G.Adj v x := by
    rintro x (rfl | rfl | rfl) <;> assumption
  have hvβ : ∀ w, v ∉ β w := by
    intro w hvw
    obtain ⟨w', hww'⟩ := hKiso w
    obtain ⟨x, hx, y, _, hxy⟩ := hadj w w' hww'
    have hall : ∀ y ∈ β w, y = v :=
      induce_closed (hβ w).2 (fun y => y = v) hvw rfl
        (fun x y _ _ hxy hx => absurd hx (hG'' x y hxy).1)
    exact (hG'' x y hxy).1 (hall x hx)
  have hdis : ∀ p q x, x ∈ β p → x ∈ β q → p = q := by
    intro p q x hp hq
    by_contra hne
    exact Set.disjoint_left.1 (hpw hne) hp hq
  -- the set `D` of branch sets that receive `v` (at most one)
  obtain ⟨D, hD, hDA, hle, hbad⟩ : ∃ D : Set W, D.Subsingleton ∧
      (∀ w ∈ D, ∃ x ∈ β w, In3 a b c x) ∧
      (∀ w ∉ D, ∀ x ∈ β w, ∀ y ∈ β w, In3 a b c x → In3 a b c y → x = y) ∧
      (∀ p q, K.Adj p q → ∀ x ∈ β p, ∀ y ∈ β q, In3 a b c x → In3 a b c y → x ≠ y →
        p ∈ D ∨ q ∈ D) := by
    by_cases h1 : ∃ w, ∃ x ∈ β w, ∃ y ∈ β w, In3 a b c x ∧ In3 a b c y ∧ x ≠ y
    · obtain ⟨w0, x, hx, y, hy, hAx, hAy, hxy⟩ := h1
      refine ⟨{w0}, Set.subsingleton_singleton, ?_, ?_, ?_⟩
      · intro w hw
        rw [Set.mem_singleton_iff] at hw
        subst hw
        exact ⟨x, hx, hAx⟩
      · intro w hw x' hx' y' hy' hAx' hAy'
        rw [Set.mem_singleton_iff] at hw
        by_contra hne
        have n1 : x ≠ x' := fun e => hw (hdis _ _ _ hx' (e ▸ hx))
        have n2 : x ≠ y' := fun e => hw (hdis _ _ _ hy' (e ▸ hx))
        have n3 : y ≠ x' := fun e => hw (hdis _ _ _ hx' (e ▸ hy))
        have n4 : y ≠ y' := fun e => hw (hdis _ _ _ hy' (e ▸ hy))
        exact four_of_three hAx hAy hAx' hAy' hxy n1 n2 n3 n4 hne
      · intro p q _ x' hx' y' hy' hAx' hAy' hne
        by_contra hcon
        simp only [Set.mem_singleton_iff, not_or] at hcon
        obtain ⟨hp, hq⟩ := hcon
        have n1 : x ≠ x' := fun e => hp (hdis _ _ _ hx' (e ▸ hx))
        have n2 : x ≠ y' := fun e => hq (hdis _ _ _ hy' (e ▸ hx))
        have n3 : y ≠ x' := fun e => hp (hdis _ _ _ hx' (e ▸ hy))
        have n4 : y ≠ y' := fun e => hq (hdis _ _ _ hy' (e ▸ hy))
        exact four_of_three hAx hAy hAx' hAy' hxy n1 n2 n3 n4 hne
    · push Not at h1
      by_cases h2 : ∃ p q, K.Adj p q ∧ ∃ x ∈ β p, ∃ y ∈ β q,
          In3 a b c x ∧ In3 a b c y ∧ x ≠ y
      · obtain ⟨p0, q0, hpq0, x0, hx0, y0, hy0, hA0, hB0, hne0⟩ := h2
        have through : ∀ (u0 : W) (s0 t0 : V), s0 ∈ β u0 → In3 a b c s0 → In3 a b c t0 →
            s0 ≠ t0 → ∀ (t0w : W), t0 ∈ β t0w →
            ∀ p q, K.Adj p q → ∀ x ∈ β p, ∀ y ∈ β q, In3 a b c x → In3 a b c y → x ≠ y →
              p ≠ u0 → q ≠ u0 → ∃ r, K.Adj t0w r ∧ ∃ z ∈ β r, In3 a b c z ∧ z ≠ s0 ∧ z ≠ t0 := by
          intro u0 s0 t0 hs0 hs0A ht0A hst t0w ht0 p q hpq x hx y hy hAx hAy hne hp hq
          have n1 : x ≠ s0 := fun e => hp (hdis _ _ _ hx (e ▸ hs0))
          have n2 : y ≠ s0 := fun e => hq (hdis _ _ _ hy (e ▸ hs0))
          by_cases e1 : x = t0
          · have hpt : p = t0w := hdis _ _ _ hx (e1 ▸ ht0)
            subst hpt
            exact ⟨q, hpq, y, hy, hAy, n2, fun e => hne (e1.trans e.symm)⟩
          · by_cases e2 : y = t0
            · have hqt : q = t0w := hdis _ _ _ hy (e2 ▸ ht0)
              subst hqt
              exact ⟨p, hpq.symm, x, hx, hAx, n1, e1⟩
            · exact (four_of_three hAx hAy hs0A ht0A hne n1 e1 n2 e2 hst).elim
        by_cases hP : ∀ p q, K.Adj p q → ∀ x ∈ β p, ∀ y ∈ β q, In3 a b c x → In3 a b c y →
            x ≠ y → p = p0 ∨ q = p0
        · refine ⟨{p0}, Set.subsingleton_singleton, ?_, fun w _ => h1 w, ?_⟩
          · intro w hw
            rw [Set.mem_singleton_iff] at hw
            subst hw
            exact ⟨x0, hx0, hA0⟩
          · intro p q hpq x hx y hy hAx hAy hne
            simpa using hP p q hpq x hx y hy hAx hAy hne
        · refine ⟨{q0}, Set.subsingleton_singleton, ?_, fun w _ => h1 w, ?_⟩
          · intro w hw
            rw [Set.mem_singleton_iff] at hw
            subst hw
            exact ⟨y0, hy0, hB0⟩
          · intro p q hpq x hx y hy hAx hAy hne
            by_contra hcon
            simp only [Set.mem_singleton_iff, not_or] at hcon
            obtain ⟨hp, hq⟩ := hcon
            push Not at hP
            obtain ⟨p1, q1, hpq1, x1, hx1, y1, hy1, hAx1, hAy1, hne1, hp1, hq1⟩ := hP
            obtain ⟨r, hr, z, hz, hAz, hz1, hz2⟩ := through p0 x0 y0 hx0 hA0 hB0 hne0 q0 hy0
              p1 q1 hpq1 x1 hx1 y1 hy1 hAx1 hAy1 hne1 hp1 hq1
            obtain ⟨r', hr', z', hz', hAz', hz1', hz2'⟩ := through q0 y0 x0 hy0 hB0 hA0
              hne0.symm p0 hx0 p q hpq x hx y hy hAx hAy hne hp hq
            have hzz : z = z' := by
              by_contra hzz
              exact four_of_three hA0 hB0 hAz hAz' hne0 hz1.symm hz2'.symm hz2.symm
                hz1'.symm hzz
            subst hzz
            have hrr : r = r' := hdis _ _ _ hz hz'
            subst hrr
            exact hKtri p0 q0 r hpq0 hr hr'
      · push Not at h2
        refine ⟨∅, Set.subsingleton_empty, by simp, fun w _ => h1 w, ?_⟩
        intro p q hpq x hx y hy hAx hAy hne
        exact absurd (h2 p q hpq x hx y hy hAx hAy) hne
  -- the new branch sets
  obtain ⟨β', hβ'⟩ : ∃ β' : W → Set V, ∀ w, β' w = if w ∈ D then insert v (β w) else β w :=
    ⟨_, fun w => rfl⟩
  have sub : ∀ w, β w ⊆ β' w := by
    intro w z hz
    rw [hβ' w]
    split_ifs
    · exact Set.mem_insert_of_mem _ hz
    · exact hz
  have memv : ∀ w, w ∈ D → v ∈ β' w := by
    intro w hw
    rw [hβ' w, if_pos hw]
    exact Set.mem_insert _ _
  have mem' : ∀ w x, x ∈ β' w → (x = v ∧ w ∈ D) ∨ x ∈ β w := by
    intro w x hx
    rw [hβ' w] at hx
    split_ifs at hx with hw
    · rcases hx with h | h
      · exact Or.inl ⟨h, hw⟩
      · exact Or.inr h
    · exact Or.inr hx
  refine ⟨β', ?_, ?_, ?_⟩
  · intro w
    by_cases hw : w ∈ D
    · rw [hβ' w, if_pos hw]
      refine ⟨Set.insert_nonempty _ _, ?_⟩
      obtain ⟨x0, hx0, hAx0⟩ := hDA w hw
      refine induce_insert_connected (hβ w).2 (fun x y _ _ hxy => ?_) hx0 (hvA x0 hAx0)
      rcases (hG'' x y hxy).2 with h | ⟨hx, hy⟩
      · exact Or.inl h
      · exact Or.inr ⟨hvA x hx, hvA y hy⟩
    · rw [hβ' w, if_neg hw]
      refine ⟨(hβ w).1, SimpleGraph.Connected.mono ?_ (hβ w).2⟩
      intro x y hxy
      change G''.Adj x.1 y.1 at hxy
      change G.Adj x.1 y.1
      rcases (hG'' _ _ hxy).2 with h | ⟨hx, hy⟩
      · exact h
      · exact absurd (hle w hw x.1 x.2 y.1 y.2 hx hy) (G''.ne_of_adj hxy)
  · intro p q hpq
    rw [Set.disjoint_left]
    intro x hxp hxq
    rcases mem' p x hxp with ⟨hxv, hp⟩ | hp <;> rcases mem' q x hxq with ⟨hxv', hq⟩ | hq
    · exact hpq (hD hp hq)
    · exact hvβ q (hxv ▸ hq)
    · exact hvβ p (hxv' ▸ hp)
    · exact Set.disjoint_left.1 (hpw hpq) hp hq
  · intro p q hpq
    obtain ⟨x, hx, y, hy, hxy⟩ := hadj p q hpq
    rcases (hG'' x y hxy).2 with h | ⟨hAx, hAy⟩
    · exact ⟨x, sub p hx, y, sub q hy, h⟩
    · rcases hbad p q hpq x hx y hy hAx hAy (G''.ne_of_adj hxy) with hp | hq
      · exact ⟨v, memv p hp, y, sub q hy, hvA y hAy⟩
      · exact ⟨x, sub p hx, v, memv q hq, (hvA x hAx).symm⟩

/-- `K₃,₃` is triangle-free. -/
theorem K33_triangle_free : ∀ x y z : Fin 3 ⊕ Fin 3,
    (completeBipartiteGraph (Fin 3) (Fin 3)).Adj x y →
    (completeBipartiteGraph (Fin 3) (Fin 3)).Adj y z →
    ¬ (completeBipartiteGraph (Fin 3) (Fin 3)).Adj x z := by
  intro x y z
  rcases x with x | x <;> rcases y with y | y <;> rcases z with z | z <;> simp

/-- `K₃,₃` has no isolated vertex. -/
theorem K33_no_isolated : ∀ w : Fin 3 ⊕ Fin 3,
    ∃ w', (completeBipartiteGraph (Fin 3) (Fin 3)).Adj w w' := by
  intro w
  rcases w with w | w
  · exact ⟨Sum.inr 0, by simp⟩
  · exact ⟨Sum.inl 0, by simp⟩

end PQL5

namespace PQL5

/-- the triangle on `x, y, z` -/
def tri {V : Type} (x y z : V) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {s(x, y), s(y, z), s(x, z)}

/-- the star joining `v` to `x, y, z` -/
def star3 {V : Type} (v x y z : V) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {s(v, x), s(v, y), s(v, z)}

/-- `H` is a 3-tree on the vertex set `S`, grown from the base triangle `x y z` by stacking
vertices onto triangles (Proskurowski; DJMMUW Sect. 2). -/
inductive TTb {V : Type} [DecidableEq V] : SimpleGraph V → Finset V → V → V → V → Prop
  | base (x y z : V) : x ≠ y → y ≠ z → x ≠ z → TTb (tri x y z) {x, y, z} x y z
  | stack {H : SimpleGraph V} {S : Finset V} {x y z : V} (v p q r : V) : TTb H S x y z → v ∉ S →
      p ∈ S → q ∈ S → r ∈ S → H.Adj p q → H.Adj q r → H.Adj p r →
      TTb (H ⊔ star3 v p q r) (insert v S) x y z

/-- `H` is a 3-tree on `S`. -/
def TT {V : Type} [DecidableEq V] (H : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ x y z, TTb H S x y z

section TTlemmas

variable {V : Type} [DecidableEq V]

theorem tri_adj {x y z u w : V} : (tri x y z).Adj u w ↔ u ≠ w ∧
    ((u = x ∧ w = y) ∨ (u = y ∧ w = x) ∨ (u = y ∧ w = z) ∨ (u = z ∧ w = y) ∨
      (u = x ∧ w = z) ∨ (u = z ∧ w = x)) := by
  unfold tri
  rw [SimpleGraph.fromEdgeSet_adj]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq_iff]
  tauto

theorem star3_adj {v x y z u w : V} : (star3 v x y z).Adj u w ↔ u ≠ w ∧
    ((u = v ∧ w = x) ∨ (u = x ∧ w = v) ∨ (u = v ∧ w = y) ∨ (u = y ∧ w = v) ∨
      (u = v ∧ w = z) ∨ (u = z ∧ w = v)) := by
  unfold star3
  rw [SimpleGraph.fromEdgeSet_adj]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq_iff]
  tauto

omit [DecidableEq V] in
theorem tri_swap12 (x y z : V) : tri y x z = tri x y z := by
  unfold tri
  rw [show s(y, x) = s(x, y) from Sym2.eq_swap]
  congr 1
  ext e
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  try tauto

omit [DecidableEq V] in
theorem tri_swap23 (x y z : V) : tri x z y = tri x y z := by
  unfold tri
  rw [show s(z, y) = s(y, z) from Sym2.eq_swap]
  congr 1
  ext e
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  try tauto

theorem tri_star3_comm (v b c t : V) : tri b c t ⊔ star3 v b c t = tri v b c ⊔ star3 t v b c := by
  unfold tri star3
  rw [← SimpleGraph.fromEdgeSet_union, ← SimpleGraph.fromEdgeSet_union,
    show s(t, v) = s(v, t) from Sym2.eq_swap, show s(t, b) = s(b, t) from Sym2.eq_swap,
    show s(t, c) = s(c, t) from Sym2.eq_swap]
  congr 1
  ext e
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  try tauto

theorem TTb.supp {H : SimpleGraph V} {S : Finset V} {x y z : V} (h : TTb H S x y z) :
    ∀ u w, H.Adj u w → u ∈ S ∧ w ∈ S := by
  induction h with
  | base x y z _ _ _ =>
    intro u w huw
    rw [tri_adj] at huw
    obtain ⟨_, h⟩ := huw
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp
  | @stack H S x y z v p q r _ _ hp hq hr _ _ _ ih =>
    intro u w huw
    rw [SimpleGraph.sup_adj, star3_adj] at huw
    rcases huw with huw | ⟨_, h⟩
    · obtain ⟨h1, h2⟩ := ih u w huw
      exact ⟨Finset.mem_insert_of_mem h1, Finset.mem_insert_of_mem h2⟩
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [hp, hq, hr]

theorem TTb.base_mem {H : SimpleGraph V} {S : Finset V} {x y z : V} (h : TTb H S x y z) :
    x ∈ S ∧ y ∈ S ∧ z ∈ S ∧ H.Adj x y ∧ H.Adj y z ∧ H.Adj x z := by
  induction h with
  | base x y z hxy hyz hxz =>
    refine ⟨by simp, by simp, by simp, ?_, ?_, ?_⟩
    · rw [tri_adj]; exact ⟨hxy, Or.inl ⟨rfl, rfl⟩⟩
    · rw [tri_adj]; exact ⟨hyz, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · rw [tri_adj]; exact ⟨hxz, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩
  | @stack H S x y z v p q r _ _ _ _ _ _ _ _ ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih
    exact ⟨Finset.mem_insert_of_mem h1, Finset.mem_insert_of_mem h2, Finset.mem_insert_of_mem h3,
      (le_sup_left : H ≤ H ⊔ _) h4, (le_sup_left : H ≤ H ⊔ _) h5, (le_sup_left : H ≤ H ⊔ _) h6⟩

theorem TTb.swap12 {H : SimpleGraph V} {S : Finset V} {x y z : V} (h : TTb H S x y z) :
    TTb H S y x z := by
  induction h with
  | base x y z hxy hyz hxz =>
    have h := TTb.base y x z hxy.symm hxz hyz
    rwa [tri_swap12, Finset.insert_comm] at h
  | @stack H S x y z v p q r _ hv hp hq hr hpq hqr hpr ih =>
    exact TTb.stack v p q r ih hv hp hq hr hpq hqr hpr

theorem TTb.swap23 {H : SimpleGraph V} {S : Finset V} {x y z : V} (h : TTb H S x y z) :
    TTb H S x z y := by
  induction h with
  | base x y z hxy hyz hxz =>
    have h := TTb.base x z y hxz hyz.symm hxy
    rwa [tri_swap23, Finset.pair_comm] at h
  | @stack H S x y z v p q r _ hv hp hq hr hpq hqr hpr ih =>
    exact TTb.stack v p q r ih hv hp hq hr hpq hqr hpr

/-- A vertex stacked on the base triangle can become the first base vertex. -/
theorem TTb.push {H : SimpleGraph V} {S : Finset V} {b c t : V} (h : TTb H S b c t) :
    ∀ v, v ∉ S → TTb (H ⊔ star3 v b c t) (insert v S) v b c := by
  induction h with
  | base b c t hbc hct hbt =>
    intro v hv
    have hvb : v ≠ b := fun e => hv (by simp [e])
    have hvc : v ≠ c := fun e => hv (by simp [e])
    have htv : t ∉ ({v, b, c} : Finset V) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun e => hv (by simp [e]), hbt.symm, hct.symm⟩
    have h0 := TTb.stack t v b c (TTb.base v b c hvb hbc hvc) htv (by simp) (by simp) (by simp)
      (by rw [tri_adj]; exact ⟨hvb, Or.inl ⟨rfl, rfl⟩⟩)
      (by rw [tri_adj]; exact ⟨hbc, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩)
      (by rw [tri_adj]; exact ⟨hvc, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩)
    rw [← tri_star3_comm] at h0
    have hS : (insert v {b, c, t} : Finset V) = insert t {v, b, c} := by
      ext u; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [hS]
    exact h0
  | @stack H S b c t u p q r _ hu hp hq hr hpq hqr hpr ih =>
    intro v hv
    have hvS : v ∉ S := fun e => hv (Finset.mem_insert_of_mem e)
    have hvu : u ≠ v := fun e => hv (by rw [← e]; exact Finset.mem_insert_self u S)
    have h1 := TTb.stack u p q r (ih v hvS) (by simp [hvu, hu]) (Finset.mem_insert_of_mem hp)
      (Finset.mem_insert_of_mem hq) (Finset.mem_insert_of_mem hr)
      ((le_sup_left : H ≤ H ⊔ _) hpq) ((le_sup_left : H ≤ H ⊔ _) hqr)
      ((le_sup_left : H ≤ H ⊔ _) hpr)
    rw [sup_right_comm, Finset.insert_comm] at h1
    exact h1

/-- **M1 (re-rooting).** A 3-tree can be grown from any of its triangles (Proskurowski). -/
theorem TTb.reroot {H : SimpleGraph V} {S : Finset V} {x y z : V} (h : TTb H S x y z) :
    ∀ a b c, H.Adj a b → H.Adj b c → H.Adj a c → TTb H S a b c := by
  induction h with
  | base x y z hxy hyz hxz =>
    intro a b c hab hbc hac
    have hs := (TTb.base x y z hxy hyz hxz).supp
    have ha := (hs a b hab).1
    have hb := (hs a b hab).2
    have hc := (hs b c hbc).2
    have nab := hab.ne
    have nbc := hbc.ne
    have nac := hac.ne
    have h0 := TTb.base x y z hxy hyz hxz
    have h1 := h0.swap12
    have h2 := h0.swap23
    have h3 := h0.swap12.swap23
    have h4 := h0.swap23.swap12
    have h5 := h0.swap12.swap23.swap12
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      rcases hc with rfl | rfl | rfl <;>
      first | exact (nab rfl).elim | exact (nbc rfl).elim | exact (nac rfl).elim | assumption
  | @stack H S x y z v p q r h0 hv hp hq hr hpq hqr hpr ih =>
    have hsupp := h0.supp
    have adjH : ∀ a b, (H ⊔ star3 v p q r).Adj a b → a ≠ v → b ≠ v → H.Adj a b := by
      intro a b hab hav hbv
      rw [SimpleGraph.sup_adj, star3_adj] at hab
      rcases hab with h | ⟨_, h⟩
      · exact h
      · exfalso
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          first | exact hav h1 | exact hbv h2
    have nbrv : ∀ b, (H ⊔ star3 v p q r).Adj v b → b = p ∨ b = q ∨ b = r := by
      intro b hb
      rw [SimpleGraph.sup_adj, star3_adj] at hb
      rcases hb with h | ⟨hne, h⟩
      · exact absurd (hsupp v b h).1 hv
      · rcases h with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩
        · exact Or.inl h2
        · exact (hne h2.symm).elim
        · exact Or.inr (Or.inl h2)
        · exact (hne h2.symm).elim
        · exact Or.inr (Or.inr h2)
        · exact (hne h2.symm).elim
    have key : ∀ b c t, H.Adj b c → H.Adj c t → H.Adj b t → star3 v b c t = star3 v p q r →
        TTb (H ⊔ star3 v p q r) (insert v S) v b c := by
      intro b c t h1 h2 h3 he
      have := (ih b c t h1 h2 h3).push v hv
      rwa [he] at this
    have case_v : ∀ b c, (H ⊔ star3 v p q r).Adj v b → (H ⊔ star3 v p q r).Adj v c →
        (H ⊔ star3 v p q r).Adj b c → TTb (H ⊔ star3 v p q r) (insert v S) v b c := by
      intro b c hvb hvc hbc
      have nbc := hbc.ne
      rcases nbrv b hvb with rfl | rfl | rfl <;> rcases nbrv c hvc with rfl | rfl | rfl
      · exact (nbc rfl).elim
      · exact key _ _ _ hpq hqr hpr (by first | rfl | (unfold star3; congr 1; ext e; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; try tauto))
      · exact key _ _ _ hpr hqr.symm hpq (by first | rfl | (unfold star3; congr 1; ext e; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; try tauto))
      · exact key _ _ _ hpq.symm hpr hqr (by first | rfl | (unfold star3; congr 1; ext e; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; try tauto))
      · exact (nbc rfl).elim
      · exact key _ _ _ hqr hpr.symm hpq.symm (by first | rfl | (unfold star3; congr 1; ext e; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; try tauto))
      · exact key _ _ _ hpr.symm hpq hqr.symm (by first | rfl | (unfold star3; congr 1; ext e; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; try tauto))
      · exact key _ _ _ hqr.symm hpq.symm hpr.symm (by first | rfl | (unfold star3; congr 1; ext e; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; try tauto))
      · exact (nbc rfl).elim
    intro a b c hab hbc hac
    by_cases ha : a = v
    · subst ha
      exact case_v b c hab hac hbc
    · by_cases hb : b = v
      · subst hb
        exact (case_v a c hab.symm hbc hac).swap12
      · by_cases hc : c = v
        · subst hc
          exact (case_v a b hac.symm hbc.symm hab).swap12.swap23
        · exact TTb.stack v p q r (ih a b c (adjH a b hab ha hb) (adjH b c hbc hb hc)
            (adjH a c hac ha hc)) hv hp hq hr hpq hqr hpr

end TTlemmas

end PQL5

/-! M2: every edge of a 3-tree lies in a face (a triangle with at most one common neighbour). -/

namespace PQL5

section Faces

variable {V : Type} [DecidableEq V]

/-- `x y z` is a triangle of `H` with at most one common neighbour. -/
def Face (H : SimpleGraph V) (x y z : V) : Prop :=
  H.Adj x y ∧ H.Adj y z ∧ H.Adj x z ∧ ∀ p q, p ≠ q → H.Adj p x → H.Adj p y → H.Adj p z →
    H.Adj q x → H.Adj q y → H.Adj q z → False

omit [DecidableEq V] in
theorem Face.swap12 {H : SimpleGraph V} {x y z : V} (h : Face H x y z) : Face H y x z := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1.symm, h3, h2, fun p q hpq a b c d e f => h4 p q hpq b a c e d f⟩

theorem tri_adj_of_In3 {x y z u w : V} (hu : In3 x y z u) (hw : In3 x y z w) (huw : u ≠ w) :
    (tri x y z).Adj u w := by
  rw [tri_adj]
  refine ⟨huw, ?_⟩
  unfold In3 at hu hw
  rcases hu with h1 | h1 | h1 <;> rcases hw with h2 | h2 | h2 <;> simp_all

theorem tri_In3_of_adj {x y z u w : V} (h : (tri x y z).Adj u w) :
    In3 x y z u ∧ In3 x y z w := by
  rw [tri_adj] at h
  obtain ⟨_, h⟩ := h
  unfold In3
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

theorem face_tri {x y z u w t : V} (hu : In3 x y z u) (hw : In3 x y z w) (ht : In3 x y z t)
    (huw : u ≠ w) (hwt : w ≠ t) (hut : u ≠ t) : Face (tri x y z) u w t := by
  refine ⟨tri_adj_of_In3 hu hw huw, tri_adj_of_In3 hw ht hwt, tri_adj_of_In3 hu ht hut, ?_⟩
  intro p _ _ hpu hpw hpt _ _ _
  exact four_of_three hu hw ht (tri_In3_of_adj hpu).1 huw hut (Ne.symm hpu.ne) hwt
    (Ne.symm hpw.ne) (Ne.symm hpt.ne)

/-- **M2.** Every edge of a 3-tree lies in a face. -/
theorem TTb.edge_face {H : SimpleGraph V} {S : Finset V} {x y z : V} (h : TTb H S x y z) :
    ∀ u w, H.Adj u w → ∃ t, Face H u w t := by
  induction h with
  | base x y z hxy hyz hxz =>
    intro u w huw
    have hIn := tri_In3_of_adj huw
    have hne := huw.ne
    have hx : In3 x y z x := Or.inl rfl
    have hy : In3 x y z y := Or.inr (Or.inl rfl)
    have hz : In3 x y z z := Or.inr (Or.inr rfl)
    by_cases hux : u = x
    · by_cases hwy : w = y
      · exact ⟨z, face_tri hIn.1 hIn.2 hz hne (by rw [hwy]; exact hyz) (by rw [hux]; exact hxz)⟩
      · exact ⟨y, face_tri hIn.1 hIn.2 hy hne hwy (by rw [hux]; exact hxy)⟩
    · by_cases hwx : w = x
      · by_cases huy : u = y
        · exact ⟨z, face_tri hIn.1 hIn.2 hz hne (by rw [hwx]; exact hxz) (by rw [huy]; exact hyz)⟩
        · exact ⟨y, face_tri hIn.1 hIn.2 hy hne (by rw [hwx]; exact hxy) huy⟩
      · exact ⟨x, face_tri hIn.1 hIn.2 hx hne hwx hux⟩
  | @stack H S x y z v p q r h0 hv hp hq hr hpq hqr hpr ih =>
    have hsupp := h0.supp
    have hvS : ∀ a, a ∈ S → a ≠ v := fun a ha e => hv (by rw [← e]; exact ha)
    have adjH : ∀ a b, (H ⊔ star3 v p q r).Adj a b → a ≠ v → b ≠ v → H.Adj a b := by
      intro a b hab hav hbv
      rw [SimpleGraph.sup_adj, star3_adj] at hab
      rcases hab with h | ⟨_, h⟩
      · exact h
      · exfalso
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          first | exact hav h1 | exact hbv h2
    have nbrv : ∀ b, (H ⊔ star3 v p q r).Adj v b → In3 p q r b := by
      intro b hb
      rw [SimpleGraph.sup_adj, star3_adj] at hb
      rcases hb with h | ⟨hne, h⟩
      · exact absurd (hsupp v b h).1 hv
      · rcases h with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩
        · exact Or.inl h2
        · exact (hne h2.symm).elim
        · exact Or.inr (Or.inl h2)
        · exact (hne h2.symm).elim
        · exact Or.inr (Or.inr h2)
        · exact (hne h2.symm).elim
    have adjv : ∀ b, In3 p q r b → (H ⊔ star3 v p q r).Adj v b := by
      intro b hb
      rw [SimpleGraph.sup_adj, star3_adj]
      right
      rcases hb with h | h | h
      · rw [h]; exact ⟨fun e => hv (by rw [e]; exact hp), Or.inl ⟨rfl, rfl⟩⟩
      · rw [h]; exact ⟨fun e => hv (by rw [e]; exact hq), Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
      · rw [h]
        exact ⟨fun e => hv (by rw [e]; exact hr), Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩
    have adj0 : ∀ a b, In3 p q r a → In3 p q r b → a ≠ b → H.Adj a b := by
      intro a b ha hb hab
      rcases ha with h1 | h1 | h1 <;> rcases hb with h2 | h2 | h2 <;> rw [h1, h2] at hab ⊢ <;>
        first | exact (hab rfl).elim | exact hpq | exact hqr | exact hpr | exact hpq.symm |
          exact hqr.symm | exact hpr.symm
    have face_new : ∀ b c, In3 p q r b → In3 p q r c → b ≠ c → Face (H ⊔ star3 v p q r) v b c := by
      intro b c hb hc hbc
      refine ⟨adjv b hb, (le_sup_left : H ≤ H ⊔ _) (adj0 b c hb hc hbc), adjv c hc, ?_⟩
      intro s s' hss' hsv hsb hsc hs'v hs'b hs'c
      exact four_of_three hb hc (nbrv s hsv.symm) (nbrv s' hs'v.symm) hbc (Ne.symm hsb.ne)
        (Ne.symm hs'b.ne) (Ne.symm hsc.ne) (Ne.symm hs'c.ne) hss'
    have other : ∀ b, In3 p q r b → ∃ c, In3 p q r c ∧ b ≠ c := by
      intro b _
      by_cases hbp : b = p
      · exact ⟨q, Or.inr (Or.inl rfl), by rw [hbp]; exact hpq.ne⟩
      · exact ⟨p, Or.inl rfl, hbp⟩
    intro u w huw
    by_cases huv : u = v
    · rw [huv] at huw ⊢
      obtain ⟨c, hc, hwc⟩ := other w (nbrv w huw)
      exact ⟨c, face_new w c (nbrv w huw) hc hwc⟩
    by_cases hwv : w = v
    · rw [hwv] at huw ⊢
      have hu := nbrv u huw.symm
      obtain ⟨c, hc, huc⟩ := other u hu
      exact ⟨c, (face_new u c hu hc huc).swap12⟩
    have h0uw := adjH u w huw huv hwv
    obtain ⟨t, _, ht2, ht3, ht4⟩ := ih u w h0uw
    have htv : t ≠ v := hvS t (hsupp w t ht2).2
    by_cases hall : (H ⊔ star3 v p q r).Adj v u ∧ (H ⊔ star3 v p q r).Adj v w ∧
        (H ⊔ star3 v p q r).Adj v t
    · obtain ⟨a1, a2, _⟩ := hall
      have hu := nbrv u a1
      have hw := nbrv w a2
      refine ⟨v, huw, a2.symm, a1.symm, ?_⟩
      intro s s' hss' hsu hsw hsv hs'u hs'w hs'v
      exact four_of_three hu hw (nbrv s hsv.symm) (nbrv s' hs'v.symm) huw.ne (Ne.symm hsu.ne)
        (Ne.symm hs'u.ne) (Ne.symm hsw.ne) (Ne.symm hs'w.ne) hss'
    · refine ⟨t, huw, (le_sup_left : H ≤ H ⊔ _) ht2, (le_sup_left : H ≤ H ⊔ _) ht3, ?_⟩
      intro s s' hss' hsu hsw hst hs'u hs'w hs't
      have hsv : s ≠ v := fun e => hall (by subst e; exact ⟨hsu, hsw, hst⟩)
      have hs'v : s' ≠ v := fun e => hall (by subst e; exact ⟨hs'u, hs'w, hs't⟩)
      exact ht4 s s' hss' (adjH s u hsu hsv huv) (adjH s w hsw hsv hwv) (adjH s t hst hsv htv)
        (adjH s' u hs'u hs'v huv) (adjH s' w hs'w hs'v hwv) (adjH s' t hs't hs'v htv)

end Faces

end PQL5

/-! Combinatorial interface (session 2): 3-trees grown by stacking (`TT`), the Apollonian condition
`TriCond`, and the reduction of lemma_5 to C2 (combinatorial Kratochvil-Vaner) and C3 (combinatorial
Alam et al.). -/

namespace PQL5

open PlanarQueue.Planar

/-- No triangle of `H` has three distinct common neighbours (planar 3-trees = Apollonian
networks). -/
def TriCond {V : Type} (H : SimpleGraph V) : Prop :=
  ∀ a b c p q r : V, H.Adj a b → H.Adj b c → H.Adj a c → p ≠ q → q ≠ r → p ≠ r →
    H.Adj p a → H.Adj p b → H.Adj p c → H.Adj q a → H.Adj q b → H.Adj q c →
    H.Adj r a → H.Adj r b → H.Adj r c → False

/-- C2 (combinatorial Kratochvil-Vaner, arXiv 1210.8113 Thm 1): a treewidth-3 graph without a
`K₃,₃` minor, supported on `S` with `|S| ≥ 3`, is a spanning subgraph of an Apollonian 3-tree on `S`. -/
def ChildC2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) (G : SimpleGraph V),
    (∀ x y, G.Adj x y → x ∈ S ∧ y ∈ S) → 3 ≤ S.card →
    RobertsonSeymour1986.GM5.TreewidthLE G 3 →
    ¬ RobertsonSeymour1986.GM5.IsMinor (completeBipartiteGraph (Fin 3) (Fin 3)) G →
    ∃ H, G ≤ H ∧ TT H S ∧ TriCond H

/-- C3 (combinatorial Alam-Bekos-Gronemann-Kaufmann-Pupyrev, arXiv 1808.10841 Thm 1): an
Apollonian 3-tree has a 5-queue layout. -/
def ChildC3 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V), TT H Finset.univ → TriCond H →
    HasQueueLayout H 5

end PQL5

/-! C1: a graph of tree-width at most 3 on a support `S` with `|S| ≥ 3` is a spanning subgraph of
a 3-tree on `S` (Proskurowski; the chordal completion of a width-3 tree decomposition). -/

namespace PQL5

section C1

variable {V : Type} [DecidableEq V]

/-- the path (interpolation) property of a tree decomposition -/
def PathProp {T : Type} (t : SimpleGraph T) (X : T → Finset V) : Prop :=
  ∀ (s s' s'' : T) (p : t.Walk s s''), p.IsPath → s' ∈ p.support → X s ∩ X s'' ⊆ X s'

/-- `P` is a union of branches of `t` at `s`. -/
def BrClosed {T : Type} (t : SimpleGraph T) (s : T) (P : Finset T) : Prop :=
  s ∉ P ∧ ∀ u ∈ P, ∀ w, t.Adj u w → w ≠ s → w ∈ P

theorem brClosed_walk_hits {T : Type} {t : SimpleGraph T} {s : T} {P : Finset T}
    (hc : BrClosed t s P) : ∀ {u w : T} (p : t.Walk u w), u ∈ P → w ∉ P → s ∈ p.support := by
  intro u w p
  induction p with
  | nil => intro hu hw; exact absurd hu hw
  | @cons a b c h p ih =>
    intro ha hc'
    by_cases hb : b = s
    · subst hb
      simp
    · have hbP : b ∈ P := hc.2 a ha b h hb
      have := ih hbP hc'
      simp [this]

theorem brClosed_walk_adj {T : Type} {t : SimpleGraph T} {s : T} {P : Finset T}
    (hc : BrClosed t s P) : ∀ {u w : T} (p : t.Walk u w), u ∈ P → w = s → ∃ x ∈ P, t.Adj x s := by
  intro u w p
  induction p with
  | nil => intro hu hw; subst hw; exact absurd hu hc.1
  | @cons a b c h p ih =>
    intro ha hcs
    by_cases hb : b = s
    · subst hb
      exact ⟨a, ha, h⟩
    · exact ih (hc.2 a ha b h hb) hcs

/-- Every tree decomposition has a vertex `v` all of whose bags lie inside one bag containing `v`
(a simplicial vertex of the chordal completion). -/
theorem exists_simplicial {T : Type} [Fintype T] [DecidableEq T] (t : SimpleGraph T)
    (ht : t.Connected) (hac : t.IsAcyclic) (X : T → Finset V) (hp : PathProp t X)
    (hne : ∃ s, (X s).Nonempty) : ∃ v s0, v ∈ X s0 ∧ ∀ s, v ∈ X s → X s ⊆ X s0 := by
  classical
  have key : ∀ m : ℕ, ∀ (s : T) (P : Finset T), P.card = m → BrClosed t s P →
      (∃ w ∈ P, ¬ X w ⊆ X s) → ∃ v s0, v ∈ X s0 ∧ ∀ s, v ∈ X s → X s ⊆ X s0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro s P hPm hc hw
    obtain ⟨w0, hw0P, hw0⟩ := hw
    obtain ⟨p0⟩ := ht.preconnected w0 s
    obtain ⟨s', hs'P, hs's⟩ := brClosed_walk_adj hc p0 hw0P rfl
    have hss' : s ≠ s' := fun h => hc.1 (h ▸ hs'P)
    set P' := P.filter (fun u => u ≠ s' ∧ ∀ p : t.Walk u s, s' ∈ p.support) with hP'
    have hP'sub : P' ⊆ P := Finset.filter_subset _ _
    have hcP' : BrClosed t s' P' := by
      refine ⟨fun h => (Finset.mem_filter.mp h).2.1 rfl, ?_⟩
      intro u hu a hua has'
      rw [hP', Finset.mem_filter] at hu ⊢
      obtain ⟨huP, hus', hall⟩ := hu
      have has : a ≠ s := by
        rintro rfl
        have := hall (SimpleGraph.Walk.cons hua SimpleGraph.Walk.nil)
        simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false] at this
        rcases this with h | h
        · exact hus' h.symm
        · exact hss' h.symm
      refine ⟨hc.2 u huP a hua has, has', ?_⟩
      intro q
      have := hall (SimpleGraph.Walk.cons hua q)
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at this
      rcases this with h | h
      · exact absurd h.symm hus'
      · exact h
    have hcard' : P'.card < m := by
      rw [← hPm]
      refine Finset.card_lt_card ⟨hP'sub, fun h => ?_⟩
      exact (Finset.mem_filter.mp (h hs'P)).2.1 rfl
    by_cases hA : ∃ u ∈ P', ¬ X u ⊆ X s'
    · exact ih _ hcard' s' P' rfl hcP' hA
    push_neg at hA
    -- a node of `P` outside `P'` and not `s'` has a walk to `s` avoiding `s'`
    have hout : ∀ u ∈ P, u ≠ s' → u ∉ P' → ∃ q : t.Walk u s, q.IsPath ∧ s' ∉ q.support := by
      intro u huP hus' huP'
      have : ¬ ∀ p : t.Walk u s, s' ∈ p.support := by
        intro h
        exact huP' (Finset.mem_filter.mpr ⟨huP, hus', h⟩)
      push_neg at this
      obtain ⟨q, hq⟩ := this
      exact ⟨q.bypass, q.bypass_isPath,
        fun h => hq (SimpleGraph.Walk.support_bypass_subset_support q h)⟩
    by_cases hB : X s' ⊆ X s
    · -- recurse on the other branches
      have hw0s' : w0 ≠ s' := by rintro rfl; exact hw0 hB
      have hw0P' : w0 ∉ P' := fun h => hw0 ((hA w0 h).trans hB)
      set P2 := (P \ P').erase s' with hP2
      have hc2 : BrClosed t s P2 := by
        refine ⟨fun h => hc.1 (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase h)).1, ?_⟩
        intro u hu a hua has
        rw [hP2, Finset.mem_erase, Finset.mem_sdiff] at hu
        obtain ⟨hus', huP, huP'⟩ := hu
        obtain ⟨q, hqp, hqs'⟩ := hout u huP hus' huP'
        have haP : a ∈ P := hc.2 u huP a hua has
        have has' : a ≠ s' := by
          rintro rfl
          have hpath : (SimpleGraph.Walk.cons hua.symm q).IsPath := by
            rw [SimpleGraph.Walk.cons_isPath_iff]; exact ⟨hqp, hqs'⟩
          have hpath2 : (SimpleGraph.Walk.cons hs's SimpleGraph.Walk.nil : t.Walk a s).IsPath := by
            rw [SimpleGraph.Walk.cons_isPath_iff]
            refine ⟨SimpleGraph.Walk.IsPath.nil, ?_⟩
            simp only [SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false]
            exact fun h => hss' h.symm
          have heq := hac.path_unique ⟨_, hpath⟩ ⟨_, hpath2⟩
          have hsupp := congrArg (fun z : t.Path a s => z.1.support) heq
          simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
            List.cons.injEq, true_and] at hsupp
          have hu1 : q.support.head? = some u := by
            rw [SimpleGraph.Walk.support_eq_cons]; rfl
          rw [hsupp] at hu1
          simp only [List.head?_cons, Option.some.injEq] at hu1
          exact hc.1 (hu1 ▸ huP)
        have haP' : a ∉ P' := by
          intro h
          obtain ⟨_, _, hall⟩ := (Finset.mem_filter.mp h)
          have := hall (SimpleGraph.Walk.cons hua.symm q)
          rw [SimpleGraph.Walk.support_cons, List.mem_cons] at this
          rcases this with h' | h'
          · exact has' h'.symm
          · exact hqs' h'
        rw [hP2, Finset.mem_erase, Finset.mem_sdiff]
        exact ⟨has', haP, haP'⟩
      have hcard2 : P2.card < m := by
        rw [← hPm, hP2]
        exact lt_of_lt_of_le (Finset.card_erase_lt_of_mem
          (Finset.mem_sdiff.mpr ⟨hs'P, fun h => (Finset.mem_filter.mp h).2.1 rfl⟩))
          (Finset.card_le_card Finset.sdiff_subset)
      refine ih _ hcard2 s P2 rfl hc2 ⟨w0, ?_, hw0⟩
      rw [hP2, Finset.mem_erase, Finset.mem_sdiff]
      exact ⟨hw0s', hw0P, hw0P'⟩
    · -- `s'` is the simplicial bag
      rw [Finset.not_subset] at hB
      obtain ⟨v, hvs', hvs⟩ := hB
      refine ⟨v, s', hvs', ?_⟩
      intro u hvu
      by_cases huP' : u ∈ P'
      · exact hA u huP'
      by_cases hus' : u = s'
      · rw [hus']
      exfalso
      apply hvs
      by_cases huP : u ∈ P
      · obtain ⟨q, hqp, hqs'⟩ := hout u huP hus' huP'
        have hpath : (SimpleGraph.Walk.cons hs's q.reverse).IsPath := by
          rw [SimpleGraph.Walk.cons_isPath_iff]
          refine ⟨hqp.reverse, ?_⟩
          rw [SimpleGraph.Walk.support_reverse, List.mem_reverse]
          exact hqs'
        have hs_in : s ∈ (SimpleGraph.Walk.cons hs's q.reverse).support := by
          rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_reverse, List.mem_cons,
            List.mem_reverse]
          exact Or.inr q.end_mem_support
        exact hp s' s u _ hpath hs_in (Finset.mem_inter.mpr ⟨hvs', hvu⟩)
      · obtain ⟨q⟩ := ht.preconnected s' u
        have hsq := brClosed_walk_hits hc q.bypass hs'P huP
        exact hp s' s u q.bypass q.bypass_isPath hsq (Finset.mem_inter.mpr ⟨hvs', hvu⟩)
  obtain ⟨s1, v1, hv1⟩ := hne
  have hc0 : BrClosed t s1 (Finset.univ.erase s1) := by
    refine ⟨Finset.notMem_erase _ _, ?_⟩
    intro u _ w _ hws
    simp [hws]
  by_cases hall : ∃ w ∈ Finset.univ.erase s1, ¬ X w ⊆ X s1
  · exact key _ s1 _ rfl hc0 hall
  push_neg at hall
  refine ⟨v1, s1, hv1, ?_⟩
  intro s _
  by_cases hs : s = s1
  · rw [hs]
  · exact hall s (Finset.mem_erase.mpr ⟨hs, Finset.mem_univ _⟩)

/-- In a 3-tree, every clique of at most three vertices lies in a triangle. -/
theorem TTb.clique_in_tri {H : SimpleGraph V} {S : Finset V} {x y z : V} (h : TTb H S x y z) :
    ∀ K : Finset V, K ⊆ S → K.card ≤ 3 → (∀ a ∈ K, ∀ b ∈ K, a ≠ b → H.Adj a b) →
      ∃ p q r, H.Adj p q ∧ H.Adj q r ∧ H.Adj p r ∧ K ⊆ {p, q, r} := by
  induction h with
  | base x y z hxy hyz hxz =>
    intro K hK _ _
    refine ⟨x, y, z, ?_, ?_, ?_, hK⟩
    · rw [tri_adj]; exact ⟨hxy, Or.inl ⟨rfl, rfl⟩⟩
    · rw [tri_adj]; exact ⟨hyz, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · rw [tri_adj]; exact ⟨hxz, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩
  | @stack H S x y z v p q r hH hv hp hq hr hpq hqr hpr ih =>
    intro K hK hK3 hcl
    have hsupp := hH.supp
    have hle : H ≤ H ⊔ star3 v p q r := le_sup_left
    have hvp : v ≠ p := fun h => hv (h ▸ hp)
    have hvq : v ≠ q := fun h => hv (h ▸ hq)
    have hvr : v ≠ r := fun h => hv (h ▸ hr)
    have hst : ∀ a b, (star3 v p q r).Adj a b → (star3 v p q r ≤ H ⊔ star3 v p q r) →
        (H ⊔ star3 v p q r).Adj a b := fun a b h hs => hs h
    have hS1 : ∀ a b, a ≠ b → (a = v ∧ (b = p ∨ b = q ∨ b = r)) →
        (H ⊔ star3 v p q r).Adj a b := by
      intro a b hab hb
      apply hst a b _ le_sup_right
      rw [star3_adj]
      obtain ⟨rfl, hb⟩ := hb
      refine ⟨hab, ?_⟩
      rcases hb with rfl | rfl | rfl <;> simp
    have hS2 : ∀ a b, a ≠ b → (b = v ∧ (a = p ∨ a = q ∨ a = r)) →
        (H ⊔ star3 v p q r).Adj a b := by
      intro a b hab hb
      exact (hS1 b a (Ne.symm hab) hb).symm
    by_cases hvK : v ∈ K
    · -- every other element of `K` is a neighbour of `v`, hence one of `p, q, r`
      have hKn : ∀ a ∈ K, a ≠ v → a = p ∨ a = q ∨ a = r := by
        intro a ha hav
        have hadj := hcl v hvK a ha (Ne.symm hav)
        rw [SimpleGraph.sup_adj, star3_adj] at hadj
        rcases hadj with hadj | ⟨_, h⟩
        · exact absurd (hsupp v a hadj).1 hv
        · rcases h with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
          · exact Or.inl h
          · exact absurd h hav
          · exact Or.inr (Or.inl h)
          · exact absurd h hav
          · exact Or.inr (Or.inr h)
          · exact absurd h hav
      have hpq' : p ≠ q := hpq.ne
      have hqr' : q ≠ r := hqr.ne
      have hpr' : p ≠ r := hpr.ne
      by_cases hpK : p ∈ K
      · by_cases hqK : q ∈ K
        · have hrK : r ∉ K := by
            intro hrK
            have : ({v, p, q, r} : Finset V) ⊆ K := by
              intro a ha
              simp only [Finset.mem_insert, Finset.mem_singleton] at ha
              rcases ha with rfl | rfl | rfl | rfl <;> assumption
            have h4 := Finset.card_le_card this
            rw [Finset.card_insert_of_notMem (by simp [hvp, hvq, hvr]),
              Finset.card_insert_of_notMem (by simp [hpq', hpr']),
              Finset.card_pair hqr'] at h4
            omega
          refine ⟨v, p, q, hS1 v p hvp ⟨rfl, Or.inl rfl⟩, (hle hpq), hS1 v q hvq ⟨rfl, Or.inr (Or.inl rfl)⟩, ?_⟩
          intro a ha
          simp only [Finset.mem_insert, Finset.mem_singleton]
          by_cases hav : a = v
          · exact Or.inl hav
          · rcases hKn a ha hav with h | h | h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
            · exact absurd (h ▸ ha) hrK
        · refine ⟨v, p, r, hS1 v p hvp ⟨rfl, Or.inl rfl⟩, (hle hpr), hS1 v r hvr ⟨rfl, Or.inr (Or.inr rfl)⟩, ?_⟩
          intro a ha
          simp only [Finset.mem_insert, Finset.mem_singleton]
          by_cases hav : a = v
          · exact Or.inl hav
          · rcases hKn a ha hav with h | h | h
            · exact Or.inr (Or.inl h)
            · exact absurd (h ▸ ha) hqK
            · exact Or.inr (Or.inr h)
      · refine ⟨v, q, r, hS1 v q hvq ⟨rfl, Or.inr (Or.inl rfl)⟩, (hle hqr), hS1 v r hvr ⟨rfl, Or.inr (Or.inr rfl)⟩, ?_⟩
        intro a ha
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_cases hav : a = v
        · exact Or.inl hav
        · rcases hKn a ha hav with h | h | h
          · exact absurd (h ▸ ha) hpK
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
    · have hKS : K ⊆ S := by
        intro a ha
        have := hK ha
        rw [Finset.mem_insert] at this
        rcases this with h | h
        · exact absurd (h ▸ ha) hvK
        · exact h
      have hclH : ∀ a ∈ K, ∀ b ∈ K, a ≠ b → H.Adj a b := by
        intro a ha b hb hab
        have hadj := hcl a ha b hb hab
        rw [SimpleGraph.sup_adj, star3_adj] at hadj
        rcases hadj with hadj | ⟨_, h⟩
        · exact hadj
        · exfalso
          rcases h with ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ | ⟨_, h⟩ <;>
            exact hvK (h ▸ (by assumption))
      obtain ⟨a, b, c, h1, h2, h3, h4⟩ := ih K hKS hK3 hclH
      exact ⟨a, b, c, hle h1, hle h2, hle h3, h4⟩

/-- C1 core: the chordal completion of a width-3 tree decomposition covering `S` is contained
in a 3-tree on `S`. -/
theorem c1_core {T : Type} [Fintype T] [DecidableEq T] (t : SimpleGraph T) (ht : t.Connected)
    (hac : t.IsAcyclic) : ∀ n : ℕ, ∀ (S : Finset V) (X : T → Finset V), S.card = n → 3 ≤ n →
      (∀ s, X s ⊆ S) → (∀ v ∈ S, ∃ s, v ∈ X s) → (∀ s, (X s).card ≤ 4) → PathProp t X →
      ∃ H, TT H S ∧ ∀ s, ∀ a ∈ X s, ∀ b ∈ X s, a ≠ b → H.Adj a b := by
  intro n
  induction n with
  | zero => intro S X _ h3; omega
  | succ n ih =>
    intro S X hSn h3 hXS hcov h4 hp
    rcases Nat.lt_or_ge n 3 with hn | hn
    · -- `|S| = 3`
      have hS3 : S.card = 3 := by omega
      obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hS3
      refine ⟨tri x y z, ⟨x, y, z, TTb.base x y z hxy hyz hxz⟩, ?_⟩
      intro s a ha b hb hab
      have ha' := hXS s ha
      have hb' := hXS s hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha' hb'
      rw [tri_adj]
      refine ⟨hab, ?_⟩
      rcases ha' with rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl <;> simp_all
    · obtain ⟨u0, hu0⟩ : S.Nonempty := by
        rw [← Finset.card_pos]; omega
      obtain ⟨s1, hs1⟩ := hcov u0 hu0
      obtain ⟨v, s0, hvs0, hsimp⟩ := exists_simplicial t ht hac X hp ⟨s1, ⟨u0, hs1⟩⟩
      have hvS : v ∈ S := hXS s0 hvs0
      set X' : T → Finset V := fun s => (X s).erase v with hX'
      have hS'n : (S.erase v).card = n := by
        rw [Finset.card_erase_of_mem hvS]; omega
      have hp' : PathProp t X' := by
        intro s s' s'' p hpth hmem a ha
        simp only [hX', Finset.mem_inter, Finset.mem_erase] at ha ⊢
        exact ⟨ha.1.1, hp s s' s'' p hpth hmem (Finset.mem_inter.mpr ⟨ha.1.2, ha.2.2⟩)⟩
      obtain ⟨H', ⟨x, y, z, hH'⟩, hcl'⟩ := ih (S.erase v) X' hS'n hn
        (fun s => Finset.erase_subset_erase v (hXS s))
        (by
          intro a ha
          obtain ⟨hav, haS⟩ := Finset.mem_erase.mp ha
          obtain ⟨s, hs⟩ := hcov a haS
          exact ⟨s, Finset.mem_erase.mpr ⟨hav, hs⟩⟩)
        (fun s => (Finset.card_erase_le).trans (h4 s)) hp'
      have hK3 : ((X s0).erase v).card ≤ 3 := by
        rw [Finset.card_erase_of_mem hvs0]; have := h4 s0; omega
      obtain ⟨p, q, r, hpq, hqr, hpr, hK⟩ := hH'.clique_in_tri ((X s0).erase v)
        (Finset.erase_subset_erase v (hXS s0)) hK3 (hcl' s0)
      have hpS := (hH'.supp p q hpq).1
      have hqS := (hH'.supp q r hqr).1
      have hrS := (hH'.supp q r hqr).2
      have hvS' : v ∉ S.erase v := Finset.notMem_erase v S
      have hT := TTb.stack v p q r hH' hvS' hpS hqS hrS hpq hqr hpr
      rw [Finset.insert_erase hvS] at hT
      refine ⟨H' ⊔ star3 v p q r, ⟨x, y, z, hT⟩, ?_⟩
      have hvp : v ≠ p := fun h => hvS' (h ▸ hpS)
      have hvq : v ≠ q := fun h => hvS' (h ▸ hqS)
      have hvr : v ≠ r := fun h => hvS' (h ▸ hrS)
      have hstar : ∀ b, b ∈ (X s0).erase v → (H' ⊔ star3 v p q r).Adj v b := by
        intro b hb
        have hb' := hK hb
        have hbv : b ≠ v := (Finset.mem_erase.mp hb).1
        rw [SimpleGraph.sup_adj, star3_adj]
        right
        refine ⟨Ne.symm hbv, ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb'
        rcases hb' with rfl | rfl | rfl <;> simp
      intro s a ha b hb hab
      by_cases hav : a = v
      · subst hav
        exact hstar b (Finset.mem_erase.mpr ⟨Ne.symm hab, hsimp s ha hb⟩)
      by_cases hbv : b = v
      · subst hbv
        exact (hstar a (Finset.mem_erase.mpr ⟨hav, hsimp s hb ha⟩)).symm
      exact (le_sup_left : H' ≤ H' ⊔ star3 v p q r)
        (hcl' s a (Finset.mem_erase.mpr ⟨hav, ha⟩) b (Finset.mem_erase.mpr ⟨hbv, hb⟩) hab)

/-- C1: a graph of tree-width at most 3 supported on `S` with `|S| ≥ 3` is a subgraph of a 3-tree
on `S`. -/
theorem c1_tw {S : Finset V} {G : SimpleGraph V} (hsupp : ∀ x y, G.Adj x y → x ∈ S ∧ y ∈ S)
    (h3 : 3 ≤ S.card) (htw : RobertsonSeymour1986.GM5.TreewidthLE G 3) :
    ∃ H, G ≤ H ∧ TT H S := by
  classical
  obtain ⟨T, _, t, X, ⟨htree, hcov, hedge, hpath⟩, hw⟩ := htw
  set X2 : T → Finset V := fun s => X s ∩ S with hX2
  have hp2 : PathProp t X2 := by
    intro s s' s'' p hpth hmem a ha
    simp only [hX2, Finset.mem_inter] at ha ⊢
    exact ⟨hpath s s' s'' p hpth hmem (Finset.mem_inter.mpr ⟨ha.1.1, ha.2.1⟩), ha.1.2⟩
  obtain ⟨H, hT, hcl⟩ := c1_core t htree.connected htree.isAcyclic S.card S X2 rfl h3
    (fun s => Finset.inter_subset_right)
    (by
      intro v hv
      obtain ⟨s, hs⟩ := hcov v
      exact ⟨s, Finset.mem_inter.mpr ⟨hs, hv⟩⟩)
    (fun s => (Finset.card_le_card Finset.inter_subset_left).trans (hw s)) hp2
  refine ⟨H, ?_, hT⟩
  intro a b hab
  obtain ⟨s, has, hbs⟩ := hedge a b hab
  obtain ⟨haS, hbS⟩ := hsupp a b hab
  exact hcl s a (Finset.mem_inter.mpr ⟨has, haS⟩) b (Finset.mem_inter.mpr ⟨hbs, hbS⟩) hab.ne

end C1

end PQL5

/-! Apollonian toolkit (session 3): stacking into a face keeps `TriCond`, the new triangles are
faces, gluing two 3-trees along a common triangle, small supports satisfy `TriCond`. -/

namespace PQL5

section Apoll

variable {V : Type} [DecidableEq V]

theorem In3_cover {p q r a b c : V} (ha : In3 p q r a) (hb : In3 p q r b) (hc : In3 p q r c)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) : ∀ u, In3 p q r u → In3 a b c u := by
  intro u hu
  unfold In3 at *
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;> rcases hu with rfl | rfl | rfl <;> simp_all

theorem adj_of_In3 {H : SimpleGraph V} {y a b c u : V} (ha : H.Adj y a) (hb : H.Adj y b)
    (hc : H.Adj y c) (hu : In3 a b c u) : H.Adj y u := by
  rcases hu with rfl | rfl | rfl <;> assumption

theorem star3_adj_of_In3 {v p q r s : V} (hvs : v ≠ s) (hs : In3 p q r s) :
    (star3 v p q r).Adj v s := by
  rw [star3_adj]
  refine ⟨hvs, ?_⟩
  rcases hs with rfl | rfl | rfl <;> simp

/-- neighbours of a freshly stacked vertex -/
theorem stack_nbr {H : SimpleGraph V} {v p q r : V} (hv : ∀ u, ¬ H.Adj v u)
    (hvp : v ≠ p) (hvq : v ≠ q) (hvr : v ≠ r) :
    ∀ u, (H ⊔ star3 v p q r).Adj v u → In3 p q r u := by
  intro u h
  rw [SimpleGraph.sup_adj, star3_adj] at h
  rcases h with h | ⟨_, h⟩
  · exact absurd h (hv u)
  · unfold In3
    rcases h with ⟨_, h⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact absurd h hvp
    · exact Or.inr (Or.inl h)
    · exact absurd h hvq
    · exact Or.inr (Or.inr h)
    · exact absurd h hvr

theorem stack_old {H : SimpleGraph V} {v p q r : V} :
    ∀ s t, (H ⊔ star3 v p q r).Adj s t → s ≠ v → t ≠ v → H.Adj s t := by
  intro s t h hs ht
  rw [SimpleGraph.sup_adj, star3_adj] at h
  rcases h with h | ⟨_, h⟩
  · exact h
  · exfalso
    rcases h with ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ | ⟨_, h⟩ <;>
      first | exact hs h | exact ht h

/-- Stacking a new vertex into a face keeps the Apollonian condition. -/
theorem triCond_stack {H : SimpleGraph V} {v p q r : V} (hT : TriCond H) (hF : Face H p q r)
    (hv : ∀ u, ¬ H.Adj v u) : TriCond (H ⊔ star3 v p q r) := by
  have hvp : v ≠ p := fun h => hv q (h ▸ hF.1)
  have hvq : v ≠ q := fun h => hv r (h ▸ hF.2.1)
  have hvr : v ≠ r := fun h => hv p (h ▸ hF.2.2.1.symm)
  have hN := stack_nbr hv hvp hvq hvr
  have hN' : ∀ u, (H ⊔ star3 v p q r).Adj u v → In3 p q r u := fun u h => hN u h.symm
  have hH := @stack_old V _ H v p q r
  have hpq : p ≠ q := hF.1.ne
  have hqr : q ≠ r := hF.2.1.ne
  have hpr : p ≠ r := hF.2.2.1.ne
  -- a common neighbour equal to `v`
  have hcom : ∀ a b c w y' z' : V, a ≠ b → b ≠ c → a ≠ c → a ≠ v → b ≠ v → c ≠ v →
      w = v → y' ≠ z' → y' ≠ v → z' ≠ v →
      (H ⊔ star3 v p q r).Adj w a → (H ⊔ star3 v p q r).Adj w b →
      (H ⊔ star3 v p q r).Adj w c →
      (H ⊔ star3 v p q r).Adj y' a → (H ⊔ star3 v p q r).Adj y' b →
      (H ⊔ star3 v p q r).Adj y' c →
      (H ⊔ star3 v p q r).Adj z' a → (H ⊔ star3 v p q r).Adj z' b →
      (H ⊔ star3 v p q r).Adj z' c → False := by
    intro a b c w y' z' hab hbc hac hav hbv hcv hw hyz hyv hzv hwa hwb hwc hya hyb hyc hza hzb hzc
    rw [hw] at hwa hwb hwc
    have hcov := In3_cover (hN a hwa) (hN b hwb) (hN c hwc) hab hbc hac
    have h1 := hH y' a hya hyv hav
    have h2 := hH y' b hyb hyv hbv
    have h3 := hH y' c hyc hyv hcv
    have h4 := hH z' a hza hzv hav
    have h5 := hH z' b hzb hzv hbv
    have h6 := hH z' c hzc hzv hcv
    exact hF.2.2.2 y' z' hyz (adj_of_In3 h1 h2 h3 (hcov p (Or.inl rfl)))
      (adj_of_In3 h1 h2 h3 (hcov q (Or.inr (Or.inl rfl))))
      (adj_of_In3 h1 h2 h3 (hcov r (Or.inr (Or.inr rfl))))
      (adj_of_In3 h4 h5 h6 (hcov p (Or.inl rfl)))
      (adj_of_In3 h4 h5 h6 (hcov q (Or.inr (Or.inl rfl))))
      (adj_of_In3 h4 h5 h6 (hcov r (Or.inr (Or.inr rfl))))
  intro a b c x y z hab hbc hac hxy hyz hxz hxa hxb hxc hya hyb hyc hza hzb hzc
  by_cases ha : a = v
  · rw [ha] at hab hac hxa hya
    exact four_of_three (hN b hab) (hN c hac) (hN' x hxa) (hN' y hya) hbc.ne (Ne.symm hxb.ne)
      (Ne.symm hyb.ne) (Ne.symm hxc.ne) (Ne.symm hyc.ne) hxy
  by_cases hb : b = v
  · rw [hb] at hab hbc hxb hyb
    exact four_of_three (hN a hab.symm) (hN c hbc) (hN' x hxb) (hN' y hyb) hac.ne
      (Ne.symm hxa.ne) (Ne.symm hya.ne) (Ne.symm hxc.ne) (Ne.symm hyc.ne) hxy
  by_cases hc : c = v
  · rw [hc] at hac hbc hxc hyc
    exact four_of_three (hN a hac.symm) (hN b hbc.symm) (hN' x hxc) (hN' y hyc) hab.ne
      (Ne.symm hxa.ne) (Ne.symm hya.ne) (Ne.symm hxb.ne) (Ne.symm hyb.ne) hxy
  by_cases hx : x = v
  · exact hcom a b c x y z hab.ne hbc.ne hac.ne ha hb hc hx hyz (fun h => hxy (hx.trans h.symm))
      (fun h => hxz (hx.trans h.symm)) hxa hxb hxc hya hyb hyc hza hzb hzc
  by_cases hy : y = v
  · exact hcom a b c y x z hab.ne hbc.ne hac.ne ha hb hc hy hxz (fun h => hxy (h.trans hy.symm))
      (fun h => hyz (hy.trans h.symm)) hya hyb hyc hxa hxb hxc hza hzb hzc
  by_cases hz : z = v
  · exact hcom a b c z x y hab.ne hbc.ne hac.ne ha hb hc hz hxy (fun h => hxz (h.trans hz.symm))
      (fun h => hyz (h.trans hz.symm)) hza hzb hzc hxa hxb hxc hya hyb hyc
  exact hT a b c x y z (hH a b hab ha hb) (hH b c hbc hb hc) (hH a c hac ha hc) hxy hyz hxz
    (hH x a hxa hx ha) (hH x b hxb hx hb) (hH x c hxc hx hc) (hH y a hya hy ha)
    (hH y b hyb hy hb) (hH y c hyc hy hc) (hH z a hza hz ha) (hH z b hzb hz hb) (hH z c hzc hz hc)

/-- The triangles through a freshly stacked vertex are faces. -/
theorem face_stack {H : SimpleGraph V} {v p q r s t : V} (hv : ∀ u, ¬ H.Adj v u)
    (hvp : v ≠ p) (hvq : v ≠ q) (hvr : v ≠ r) (hs : In3 p q r s) (ht : In3 p q r t)
    (hst : H.Adj s t) : Face (H ⊔ star3 v p q r) v s t := by
  have hN := stack_nbr hv hvp hvq hvr
  have hvs : v ≠ s := by rcases hs with rfl | rfl | rfl <;> assumption
  have hvt : v ≠ t := by rcases ht with rfl | rfl | rfl <;> assumption
  have hle : star3 v p q r ≤ H ⊔ star3 v p q r := le_sup_right
  refine ⟨hle (star3_adj_of_In3 hvs hs), (le_sup_left : H ≤ _) hst,
    hle (star3_adj_of_In3 hvt ht), ?_⟩
  intro w w' hww' hwv hws hwt hw'v hw's hw't
  exact four_of_three hs ht (hN w hwv.symm) (hN w' hw'v.symm) hst.ne (Ne.symm hws.ne)
    (Ne.symm hw's.ne) (Ne.symm hwt.ne) (Ne.symm hw't.ne) hww'

/-- Gluing a 3-tree grown from `a b c` onto another 3-tree containing the triangle `a b c`,
the two supports meeting only in `a, b, c`. -/
theorem TTb.glue3 {H1 : SimpleGraph V} {S1 : Finset V} {a b c : V} (h : TTb H1 S1 a b c) :
    ∀ {H2 : SimpleGraph V} {S2 : Finset V}, TT H2 S2 → H2.Adj a b → H2.Adj b c → H2.Adj a c →
      (∀ u ∈ S1, u ∈ S2 → In3 a b c u) → TT (H1 ⊔ H2) (S1 ∪ S2) := by
  induction h with
  | base x y z hxy hyz hxz =>
    intro H2 S2 hT2 h1 h2 h3 _
    obtain ⟨x0, y0, z0, hT2'⟩ := hT2
    have hsupp := hT2'.supp
    have heq : tri x y z ⊔ H2 = H2 := by
      apply sup_eq_right.mpr
      intro u w huw
      obtain ⟨hu, hw⟩ := tri_In3_of_adj huw
      unfold In3 at hu hw
      rcases hu with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
        first | exact absurd rfl huw.ne | assumption | exact SimpleGraph.Adj.symm (by assumption)
    have hS : ({x, y, z} : Finset V) ∪ S2 = S2 := by
      apply Finset.union_eq_right.mpr
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl
      · exact (hsupp _ _ h1).1
      · exact (hsupp _ _ h2).1
      · exact (hsupp _ _ h3).2
    rw [heq, hS]
    exact ⟨x0, y0, z0, hT2'⟩
  | @stack H S x y z v p q r hH hvS hp hq hr hpq hqr hpr ih =>
    intro H2 S2 hT2 h1 h2 h3 hint
    obtain ⟨x0, y0, z0, hK⟩ := ih hT2 h1 h2 h3
      (fun u hu hu2 => hint u (Finset.mem_insert_of_mem hu) hu2)
    have hb := hH.base_mem
    have hv : v ∉ S ∪ S2 := by
      rw [Finset.mem_union]
      rintro (h | h)
      · exact hvS h
      · have := hint v (Finset.mem_insert_self v S) h
        rcases this with rfl | rfl | rfl
        · exact hvS hb.1
        · exact hvS hb.2.1
        · exact hvS hb.2.2.1
    have hle : H ≤ H ⊔ H2 := le_sup_left
    have hT := TTb.stack v p q r hK hv (Finset.mem_union_left _ hp) (Finset.mem_union_left _ hq)
      (Finset.mem_union_left _ hr) (hle hpq) (hle hqr) (hle hpr)
    refine ⟨x0, y0, z0, ?_⟩
    have e1 : H ⊔ star3 v p q r ⊔ H2 = H ⊔ H2 ⊔ star3 v p q r := sup_right_comm _ _ _
    have e2 : insert v S ∪ S2 = insert v (S ∪ S2) := Finset.insert_union _ _ _
    rw [e1, e2]
    exact hT

/-- Gluing two Apollonian graphs along a triangle that is a face of both keeps `TriCond`. -/
theorem triCond_glue3 {H1 H2 : SimpleGraph V} {S1 S2 : Finset V} {a b c : V}
    (hT1 : TriCond H1) (hT2 : TriCond H2)
    (hs1 : ∀ u w, H1.Adj u w → u ∈ S1 ∧ w ∈ S1) (hs2 : ∀ u w, H2.Adj u w → u ∈ S2 ∧ w ∈ S2)
    (hint : ∀ u ∈ S1, u ∈ S2 → In3 a b c u) (hF1 : Face H1 a b c) (hF2 : Face H2 a b c) :
    TriCond (H1 ⊔ H2) := by
  have hab : a ≠ b := hF1.1.ne
  have hbc : b ≠ c := hF1.2.1.ne
  have hac : a ≠ c := hF1.2.2.1.ne
  have htri1 : ∀ u w, In3 a b c u → In3 a b c w → u ≠ w → H1.Adj u w := by
    intro u w hu hw huw
    rcases hu with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
      first | exact absurd rfl huw | exact hF1.1 | exact hF1.2.1 | exact hF1.2.2.1 |
        exact hF1.1.symm | exact hF1.2.1.symm | exact hF1.2.2.1.symm
  have htri2 : ∀ u w, In3 a b c u → In3 a b c w → u ≠ w → H2.Adj u w := by
    intro u w hu hw huw
    rcases hu with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
      first | exact absurd rfl huw | exact hF2.1 | exact hF2.2.1 | exact hF2.2.2.1 |
        exact hF2.1.symm | exact hF2.2.1.symm | exact hF2.2.2.1.symm
  -- edges between vertices of one side
  have side1 : ∀ u w, u ∈ S1 → w ∈ S1 → (H1 ⊔ H2).Adj u w → H1.Adj u w := by
    intro u w hu hw h
    rcases h with h | h
    · exact h
    · have := hs2 u w h
      exact htri1 u w (hint u hu this.1) (hint w hw this.2) h.ne
  have side2 : ∀ u w, u ∈ S2 → w ∈ S2 → (H1 ⊔ H2).Adj u w → H2.Adj u w := by
    intro u w hu hw h
    rcases h with h | h
    · have := hs1 u w h
      exact htri2 u w (hint u this.1 hu) (hint w this.2 hw) h.ne
    · exact h
  -- a neighbour of a vertex lying on one side only lies on that side
  have nb1 : ∀ u w, u ∈ S1 → u ∉ S2 → (H1 ⊔ H2).Adj u w → w ∈ S1 := by
    intro u w hu hu2 h
    rcases h with h | h
    · exact (hs1 u w h).2
    · exact absurd (hs2 u w h).1 hu2
  have nb2 : ∀ u w, u ∈ S2 → u ∉ S1 → (H1 ⊔ H2).Adj u w → w ∈ S2 := by
    intro u w hu hu1 h
    rcases h with h | h
    · exact absurd (hs1 u w h).1 hu1
    · exact (hs2 u w h).2
  have mem : ∀ u w, (H1 ⊔ H2).Adj u w → u ∈ S1 ∨ u ∈ S2 := by
    intro u w h
    rcases h with h | h
    · exact Or.inl (hs1 u w h).1
    · exact Or.inr (hs2 u w h).1
  intro u1 u2 u3 x y z h12 h23 h13 hxy hyz hxz hx1 hx2 hx3 hy1 hy2 hy3 hz1 hz2 hz3
  -- all six on side 1
  have all1 : u1 ∈ S1 → u2 ∈ S1 → u3 ∈ S1 → x ∈ S1 → y ∈ S1 → z ∈ S1 → False := by
    intro a1 a2 a3 ax ay az
    exact hT1 u1 u2 u3 x y z (side1 _ _ a1 a2 h12) (side1 _ _ a2 a3 h23) (side1 _ _ a1 a3 h13)
      hxy hyz hxz (side1 _ _ ax a1 hx1) (side1 _ _ ax a2 hx2) (side1 _ _ ax a3 hx3)
      (side1 _ _ ay a1 hy1) (side1 _ _ ay a2 hy2) (side1 _ _ ay a3 hy3)
      (side1 _ _ az a1 hz1) (side1 _ _ az a2 hz2) (side1 _ _ az a3 hz3)
  have all2 : u1 ∈ S2 → u2 ∈ S2 → u3 ∈ S2 → x ∈ S2 → y ∈ S2 → z ∈ S2 → False := by
    intro a1 a2 a3 ax ay az
    exact hT2 u1 u2 u3 x y z (side2 _ _ a1 a2 h12) (side2 _ _ a2 a3 h23) (side2 _ _ a1 a3 h13)
      hxy hyz hxz (side2 _ _ ax a1 hx1) (side2 _ _ ax a2 hx2) (side2 _ _ ax a3 hx3)
      (side2 _ _ ay a1 hy1) (side2 _ _ ay a2 hy2) (side2 _ _ ay a3 hy3)
      (side2 _ _ az a1 hz1) (side2 _ _ az a2 hz2) (side2 _ _ az a3 hz3)
  -- a vertex `u_i` on side 1 only forces everything onto side 1
  have hm1 := mem u1 u2 h12
  have hm2 := mem u2 u3 h23
  have hm3 := mem u3 u1 h13.symm
  by_cases c11 : u1 ∈ S1 ∧ u1 ∉ S2
  · have a2 := nb1 u1 u2 c11.1 c11.2 h12
    have a3 := nb1 u1 u3 c11.1 c11.2 h13
    exact all1 c11.1 a2 a3 (nb1 u1 x c11.1 c11.2 hx1.symm) (nb1 u1 y c11.1 c11.2 hy1.symm)
      (nb1 u1 z c11.1 c11.2 hz1.symm)
  by_cases c12 : u1 ∈ S2 ∧ u1 ∉ S1
  · have a2 := nb2 u1 u2 c12.1 c12.2 h12
    have a3 := nb2 u1 u3 c12.1 c12.2 h13
    exact all2 c12.1 a2 a3 (nb2 u1 x c12.1 c12.2 hx1.symm) (nb2 u1 y c12.1 c12.2 hy1.symm)
      (nb2 u1 z c12.1 c12.2 hz1.symm)
  by_cases c21 : u2 ∈ S1 ∧ u2 ∉ S2
  · have a1 := nb1 u2 u1 c21.1 c21.2 h12.symm
    have a3 := nb1 u2 u3 c21.1 c21.2 h23
    exact all1 a1 c21.1 a3 (nb1 u2 x c21.1 c21.2 hx2.symm) (nb1 u2 y c21.1 c21.2 hy2.symm)
      (nb1 u2 z c21.1 c21.2 hz2.symm)
  by_cases c22 : u2 ∈ S2 ∧ u2 ∉ S1
  · have a1 := nb2 u2 u1 c22.1 c22.2 h12.symm
    have a3 := nb2 u2 u3 c22.1 c22.2 h23
    exact all2 a1 c22.1 a3 (nb2 u2 x c22.1 c22.2 hx2.symm) (nb2 u2 y c22.1 c22.2 hy2.symm)
      (nb2 u2 z c22.1 c22.2 hz2.symm)
  by_cases c31 : u3 ∈ S1 ∧ u3 ∉ S2
  · have a1 := nb1 u3 u1 c31.1 c31.2 h13.symm
    have a2 := nb1 u3 u2 c31.1 c31.2 h23.symm
    exact all1 a1 a2 c31.1 (nb1 u3 x c31.1 c31.2 hx3.symm) (nb1 u3 y c31.1 c31.2 hy3.symm)
      (nb1 u3 z c31.1 c31.2 hz3.symm)
  by_cases c32 : u3 ∈ S2 ∧ u3 ∉ S1
  · have a1 := nb2 u3 u1 c32.1 c32.2 h13.symm
    have a2 := nb2 u3 u2 c32.1 c32.2 h23.symm
    exact all2 a1 a2 c32.1 (nb2 u3 x c32.1 c32.2 hx3.symm) (nb2 u3 y c32.1 c32.2 hy3.symm)
      (nb2 u3 z c32.1 c32.2 hz3.symm)
  -- all of `u1 u2 u3` are shared, hence are `a b c`
  have b1 : u1 ∈ S1 ∧ u1 ∈ S2 := by
    rcases hm1 with h | h
    · exact ⟨h, by_contra fun h' => c11 ⟨h, h'⟩⟩
    · exact ⟨by_contra fun h' => c12 ⟨h, h'⟩, h⟩
  have b2 : u2 ∈ S1 ∧ u2 ∈ S2 := by
    rcases hm2 with h | h
    · exact ⟨h, by_contra fun h' => c21 ⟨h, h'⟩⟩
    · exact ⟨by_contra fun h' => c22 ⟨h, h'⟩, h⟩
  have b3 : u3 ∈ S1 ∧ u3 ∈ S2 := by
    rcases hm3 with h | h
    · exact ⟨h, by_contra fun h' => c31 ⟨h, h'⟩⟩
    · exact ⟨by_contra fun h' => c32 ⟨h, h'⟩, h⟩
  have i1 := hint u1 b1.1 b1.2
  have i2 := hint u2 b2.1 b2.2
  have i3 := hint u3 b3.1 b3.2
  have hcov := In3_cover i1 i2 i3 h12.ne h23.ne h13.ne
  -- each common neighbour is a common neighbour of `a b c` on one side
  have hsidew : ∀ w, (H1 ⊔ H2).Adj w u1 → (H1 ⊔ H2).Adj w u2 → (H1 ⊔ H2).Adj w u3 →
      (H1.Adj w a ∧ H1.Adj w b ∧ H1.Adj w c) ∨ (H2.Adj w a ∧ H2.Adj w b ∧ H2.Adj w c) := by
    intro w hw1 hw2 hw3
    rcases mem w u1 hw1 with hwS | hwS
    · by_cases hw2' : w ∈ S2
      · exfalso
        have hi := hint w hwS hw2'
        have hiu := hcov w hi
        rcases hiu with rfl | rfl | rfl
        · exact hw1.ne rfl
        · exact hw2.ne rfl
        · exact hw3.ne rfl
      · left
        have e1 := side1 w u1 hwS b1.1 hw1
        have e2 := side1 w u2 hwS b2.1 hw2
        have e3 := side1 w u3 hwS b3.1 hw3
        exact ⟨adj_of_In3 e1 e2 e3 (hcov a (Or.inl rfl)),
          adj_of_In3 e1 e2 e3 (hcov b (Or.inr (Or.inl rfl))),
          adj_of_In3 e1 e2 e3 (hcov c (Or.inr (Or.inr rfl)))⟩
    · by_cases hw1' : w ∈ S1
      · exfalso
        have hi := hint w hw1' hwS
        have hiu := hcov w hi
        rcases hiu with rfl | rfl | rfl
        · exact hw1.ne rfl
        · exact hw2.ne rfl
        · exact hw3.ne rfl
      · right
        have e1 := side2 w u1 hwS b1.2 hw1
        have e2 := side2 w u2 hwS b2.2 hw2
        have e3 := side2 w u3 hwS b3.2 hw3
        exact ⟨adj_of_In3 e1 e2 e3 (hcov a (Or.inl rfl)),
          adj_of_In3 e1 e2 e3 (hcov b (Or.inr (Or.inl rfl))),
          adj_of_In3 e1 e2 e3 (hcov c (Or.inr (Or.inr rfl)))⟩
  have sx := hsidew x hx1 hx2 hx3
  have sy := hsidew y hy1 hy2 hy3
  have sz := hsidew z hz1 hz2 hz3
  rcases sx with sx | sx <;> rcases sy with sy | sy <;> rcases sz with sz | sz
  · exact hF1.2.2.2 x y hxy sx.1 sx.2.1 sx.2.2 sy.1 sy.2.1 sy.2.2
  · exact hF1.2.2.2 x y hxy sx.1 sx.2.1 sx.2.2 sy.1 sy.2.1 sy.2.2
  · exact hF1.2.2.2 x z hxz sx.1 sx.2.1 sx.2.2 sz.1 sz.2.1 sz.2.2
  · exact hF2.2.2.2 y z hyz sy.1 sy.2.1 sy.2.2 sz.1 sz.2.1 sz.2.2
  · exact hF1.2.2.2 y z hyz sy.1 sy.2.1 sy.2.2 sz.1 sz.2.1 sz.2.2
  · exact hF2.2.2.2 x z hxz sx.1 sx.2.1 sx.2.2 sz.1 sz.2.1 sz.2.2
  · exact hF2.2.2.2 x y hxy sx.1 sx.2.1 sx.2.2 sy.1 sy.2.1 sy.2.2
  · exact hF2.2.2.2 x y hxy sx.1 sx.2.1 sx.2.2 sy.1 sy.2.1 sy.2.2

/-- A graph supported on at most five vertices satisfies `TriCond` (a violation needs six). -/
theorem triCond_small {H : SimpleGraph V} {S : Finset V} (hs : ∀ u w, H.Adj u w → u ∈ S ∧ w ∈ S)
    (h5 : S.card ≤ 5) : TriCond H := by
  intro a b c x y z hab hbc hac hxy hyz hxz hxa hxb hxc hya hyb hyc hza hzb hzc
  have hsub : ({a, b, c, x, y, z} : Finset V) ⊆ S := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hs _ _ hab).1
    · exact (hs _ _ hbc).1
    · exact (hs _ _ hac).2
    · exact (hs _ _ hxa).1
    · exact (hs _ _ hya).1
    · exact (hs _ _ hza).1
  have h6 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hab.ne, hac.ne, Ne.symm hxa.ne, Ne.symm hya.ne, Ne.symm hza.ne⟩),
    Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hbc.ne, Ne.symm hxb.ne, Ne.symm hyb.ne, Ne.symm hzb.ne⟩),
    Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Ne.symm hxc.ne, Ne.symm hyc.ne, Ne.symm hzc.ne⟩),
    Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hxy, hxz⟩),
    Finset.card_pair hyz] at h6
  omega

end Apoll

end PQL5

/-! C2 toolkit A (session 3): face permutations, stacking an Apollonian graph into a face,
gluing two Apollonian graphs along 0, 1 or 2 shared vertices (Kratochvil-Vaner gluing steps,
done by stacking), and tree-width transfer lemmas. -/

namespace PQL5

section C2a

variable {V : Type} [DecidableEq V]

theorem Face.perm {H : SimpleGraph V} {x y z a b c : V} (h : Face H x y z) (ha : In3 x y z a)
    (hb : In3 x y z b) (hc : In3 x y z c) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    Face H a b c := by
  have hcov := In3_cover ha hb hc hab hbc hac
  have hadj : ∀ u w, In3 x y z u → In3 x y z w → u ≠ w → H.Adj u w := by
    intro u w hu hw huw
    rcases hu with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
      first | exact absurd rfl huw | exact h.1 | exact h.2.1 | exact h.2.2.1 |
        exact h.1.symm | exact h.2.1.symm | exact h.2.2.1.symm
  refine ⟨hadj a b ha hb hab, hadj b c hb hc hbc, hadj a c ha hc hac, ?_⟩
  intro p q hpq hpa hpb hpc hqa hqb hqc
  exact h.2.2.2 p q hpq (adj_of_In3 hpa hpb hpc (hcov x (Or.inl rfl)))
    (adj_of_In3 hpa hpb hpc (hcov y (Or.inr (Or.inl rfl))))
    (adj_of_In3 hpa hpb hpc (hcov z (Or.inr (Or.inr rfl))))
    (adj_of_In3 hqa hqb hqc (hcov x (Or.inl rfl)))
    (adj_of_In3 hqa hqb hqc (hcov y (Or.inr (Or.inl rfl))))
    (adj_of_In3 hqa hqb hqc (hcov z (Or.inr (Or.inr rfl))))

/-- Stack a new vertex into a face of an Apollonian graph. -/
theorem stack_ap {H : SimpleGraph V} {S : Finset V} {v p q r : V} (hT : TT H S) (hC : TriCond H)
    (hF : Face H p q r) (hv : v ∉ S) :
    TT (H ⊔ star3 v p q r) (insert v S) ∧ TriCond (H ⊔ star3 v p q r) ∧
      (∀ s t, In3 p q r s → In3 p q r t → H.Adj s t → Face (H ⊔ star3 v p q r) v s t) := by
  obtain ⟨x, y, z, hb⟩ := hT
  have hs := hb.supp
  have hp : p ∈ S := (hs p q hF.1).1
  have hq : q ∈ S := (hs p q hF.1).2
  have hr : r ∈ S := (hs q r hF.2.1).2
  have hnv : ∀ u, ¬ H.Adj v u := fun u h => hv (hs v u h).1
  have hvp : v ≠ p := fun h => hv (h ▸ hp)
  have hvq : v ≠ q := fun h => hv (h ▸ hq)
  have hvr : v ≠ r := fun h => hv (h ▸ hr)
  exact ⟨⟨x, y, z, TTb.stack v p q r hb hv hp hq hr hF.1 hF.2.1 hF.2.2.1⟩,
    triCond_stack hC hF hnv, fun s t hs' ht' hst => face_stack hnv hvp hvq hvr hs' ht' hst⟩

theorem glue_face3 {H1 H2 : SimpleGraph V} {A B : Finset V} {a b c : V} (hT1 : TT H1 A)
    (hC1 : TriCond H1) (hT2 : TT H2 B) (hC2 : TriCond H2) (hF1 : Face H1 a b c)
    (hF2 : Face H2 a b c) (hint : ∀ u ∈ A, u ∈ B → In3 a b c u) :
    TT (H1 ⊔ H2) (A ∪ B) ∧ TriCond (H1 ⊔ H2) := by
  obtain ⟨x, y, z, hb1⟩ := hT1
  have hb1' := hb1.reroot a b c hF1.1 hF1.2.1 hF1.2.2.1
  refine ⟨hb1'.glue3 hT2 hF2.1 hF2.2.1 hF2.2.2.1 hint, ?_⟩
  obtain ⟨x2, y2, z2, hb2⟩ := hT2
  exact triCond_glue3 hC1 hC2 hb1.supp hb2.supp hint hF1 hF2

theorem TTb.vertex_face {H : SimpleGraph V} {S : Finset V} {x y z : V} (h : TTb H S x y z)
    (u : V) (hu : u ∈ S) : ∃ w t, Face H u w t := by
  obtain ⟨p, q, r, hpq, hqr, hpr, hK⟩ := h.clique_in_tri {u} (by simpa using hu) (by simp)
    (by
      intro a ha b hb hab
      rw [Finset.mem_singleton] at ha hb
      exact absurd (ha.trans hb.symm) hab)
  have hu' : u ∈ ({p, q, r} : Finset V) := hK (Finset.mem_singleton_self u)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu'
  rcases hu' with rfl | rfl | rfl
  · obtain ⟨t, ht⟩ := h.edge_face _ _ hpq
    exact ⟨_, t, ht⟩
  · obtain ⟨t, ht⟩ := h.edge_face _ _ hqr
    exact ⟨_, t, ht⟩
  · obtain ⟨t, ht⟩ := h.edge_face _ _ hpr.symm
    exact ⟨_, t, ht⟩

/-- Glue two Apollonian graphs sharing exactly an edge `a b`. -/
theorem glue_sep2 {H1 H2 : SimpleGraph V} {A B : Finset V} {a b : V} (hT1 : TT H1 A)
    (hC1 : TriCond H1) (hT2 : TT H2 B) (hC2 : TriCond H2) (h1 : H1.Adj a b) (h2 : H2.Adj a b)
    (hint : ∀ u ∈ A, u ∈ B → u = a ∨ u = b) :
    ∃ H, H1 ⊔ H2 ≤ H ∧ TT H (A ∪ B) ∧ TriCond H := by
  obtain ⟨x1, y1, z1, hb1⟩ := hT1
  obtain ⟨c1, hF1⟩ := hb1.edge_face a b h1
  obtain ⟨x2, y2, z2, hb2⟩ := hT2
  obtain ⟨x, hF2⟩ := hb2.edge_face a b h2
  have hc1A : c1 ∈ A := (hb1.supp b c1 hF1.2.1).2
  have hbc1 : b ≠ c1 := hF1.2.1.ne
  have hac1 : a ≠ c1 := hF1.2.2.1.ne
  have hc1B : c1 ∉ B := by
    intro h
    rcases hint c1 hc1A h with h' | h'
    · exact hac1 h'.symm
    · exact hbc1 h'.symm
  obtain ⟨hT2', hC2', hfn⟩ := stack_ap ⟨x2, y2, z2, hb2⟩ hC2 hF2 hc1B
  have hF2' := hfn a b (Or.inl rfl) (Or.inr (Or.inl rfl)) h2
  have hF2'' : Face (H2 ⊔ star3 c1 a b x) a b c1 :=
    hF2'.perm (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (Or.inl rfl) h2.ne hbc1 hac1
  have hint' : ∀ u ∈ A, u ∈ insert c1 B → In3 a b c1 u := by
    intro u hu hu'
    rw [Finset.mem_insert] at hu'
    rcases hu' with h | hu'
    · exact Or.inr (Or.inr h)
    · rcases hint u hu hu' with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  obtain ⟨hT, hC⟩ := glue_face3 ⟨x1, y1, z1, hb1⟩ hC1 hT2' hC2' hF1 hF2'' hint'
  refine ⟨H1 ⊔ (H2 ⊔ star3 c1 a b x), sup_le_sup_left le_sup_left _, ?_, hC⟩
  have e : A ∪ insert c1 B = A ∪ B := by
    rw [Finset.union_insert, Finset.insert_eq_of_mem (Finset.mem_union_left _ hc1A)]
  rw [← e]
  exact hT

/-- Glue two Apollonian graphs sharing exactly one vertex `a`. -/
theorem glue_sep1 {H1 H2 : SimpleGraph V} {A B : Finset V} {a : V} (hT1 : TT H1 A)
    (hC1 : TriCond H1) (hT2 : TT H2 B) (hC2 : TriCond H2) (ha1 : a ∈ A) (ha2 : a ∈ B)
    (hint : ∀ u ∈ A, u ∈ B → u = a) :
    ∃ H, H1 ⊔ H2 ≤ H ∧ TT H (A ∪ B) ∧ TriCond H := by
  obtain ⟨x1, y1, z1, hb1⟩ := hT1
  obtain ⟨b1, c1, hF1⟩ := hb1.vertex_face a ha1
  obtain ⟨x2, y2, z2, hb2⟩ := hT2
  obtain ⟨x, y, hF2⟩ := hb2.vertex_face a ha2
  have hb1A : b1 ∈ A := (hb1.supp a b1 hF1.1).2
  have hc1A : c1 ∈ A := (hb1.supp b1 c1 hF1.2.1).2
  have hab1 : a ≠ b1 := hF1.1.ne
  have hbc1 : b1 ≠ c1 := hF1.2.1.ne
  have hac1 : a ≠ c1 := hF1.2.2.1.ne
  have hb1B : b1 ∉ B := fun h => hab1 (hint b1 hb1A h).symm
  have hc1B : c1 ∉ B := fun h => hac1 (hint c1 hc1A h).symm
  obtain ⟨hTa, hCa, hfa⟩ := stack_ap ⟨x2, y2, z2, hb2⟩ hC2 hF2 hb1B
  have hFa := hfa a x (Or.inl rfl) (Or.inr (Or.inl rfl)) hF2.1
  have hc1B' : c1 ∉ insert b1 B := by
    rw [Finset.mem_insert]
    rintro (h | h)
    · exact hbc1 h.symm
    · exact hc1B h
  obtain ⟨hTb, hCb, hfb⟩ := stack_ap hTa hCa hFa hc1B'
  have hFb := hfb b1 a (Or.inl rfl) (Or.inr (Or.inl rfl)) hFa.1
  have hFb' := hFb.perm (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) (Or.inl rfl) hab1 hbc1 hac1
  have hint' : ∀ u ∈ A, u ∈ insert c1 (insert b1 B) → In3 a b1 c1 u := by
    intro u hu hu'
    rw [Finset.mem_insert, Finset.mem_insert] at hu'
    rcases hu' with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl (hint u hu h)
  obtain ⟨hT, hC⟩ := glue_face3 ⟨x1, y1, z1, hb1⟩ hC1 hTb hCb hF1 hFb' hint'
  refine ⟨_, sup_le_sup_left (le_sup_left.trans le_sup_left) _, ?_, hC⟩
  have e : A ∪ insert c1 (insert b1 B) = A ∪ B := by
    rw [Finset.union_insert, Finset.union_insert,
      Finset.insert_eq_of_mem (Finset.mem_union_left _ hb1A),
      Finset.insert_eq_of_mem (Finset.mem_union_left _ hc1A)]
  rw [← e]
  exact hT

/-- Glue two Apollonian graphs with disjoint supports. -/
theorem glue_sep0 {H1 H2 : SimpleGraph V} {A B : Finset V} (hT1 : TT H1 A)
    (hC1 : TriCond H1) (hT2 : TT H2 B) (hC2 : TriCond H2) (hint : ∀ u ∈ A, u ∉ B) :
    ∃ H, H1 ⊔ H2 ≤ H ∧ TT H (A ∪ B) ∧ TriCond H := by
  obtain ⟨x1, y1, z1, hb1⟩ := hT1
  obtain ⟨c1, hF1⟩ := hb1.edge_face x1 y1 hb1.base_mem.2.2.2.1
  obtain ⟨x2, y2, z2, hb2⟩ := hT2
  obtain ⟨z, hF2⟩ := hb2.edge_face x2 y2 hb2.base_mem.2.2.2.1
  have ha1A : x1 ∈ A := hb1.base_mem.1
  have hb1A : y1 ∈ A := hb1.base_mem.2.1
  have hc1A : c1 ∈ A := (hb1.supp y1 c1 hF1.2.1).2
  have hab1 : x1 ≠ y1 := hF1.1.ne
  have hbc1 : y1 ≠ c1 := hF1.2.1.ne
  have hac1 : x1 ≠ c1 := hF1.2.2.1.ne
  obtain ⟨hTa, hCa, hfa⟩ := stack_ap ⟨x2, y2, z2, hb2⟩ hC2 hF2 (hint x1 ha1A)
  have hFa := hfa x2 y2 (Or.inl rfl) (Or.inr (Or.inl rfl)) hF2.1
  have hb1B : y1 ∉ insert x1 B := by
    rw [Finset.mem_insert]
    rintro (h | h)
    · exact hab1 h.symm
    · exact hint y1 hb1A h
  obtain ⟨hTb, hCb, hfb⟩ := stack_ap hTa hCa hFa hb1B
  have hFb := hfb x1 x2 (Or.inl rfl) (Or.inr (Or.inl rfl)) hFa.1
  have hc1B : c1 ∉ insert y1 (insert x1 B) := by
    rw [Finset.mem_insert, Finset.mem_insert]
    rintro (h | h | h)
    · exact hbc1 h.symm
    · exact hac1 h.symm
    · exact hint c1 hc1A h
  obtain ⟨hTc, hCc, hfc⟩ := stack_ap hTb hCb hFb hc1B
  have hFc := hfc y1 x1 (Or.inl rfl) (Or.inr (Or.inl rfl)) hFb.1
  have hFc' := hFc.perm (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) (Or.inl rfl) hab1 hbc1 hac1
  have hint' : ∀ u ∈ A, u ∈ insert c1 (insert y1 (insert x1 B)) → In3 x1 y1 c1 u := by
    intro u hu hu'
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert] at hu'
    rcases hu' with h | h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact absurd h (hint u hu)
  obtain ⟨hT, hC⟩ := glue_face3 ⟨x1, y1, z1, hb1⟩ hC1 hTc hCc hF1 hFc' hint'
  refine ⟨_, sup_le_sup_left ((le_sup_left.trans le_sup_left).trans le_sup_left) _, ?_, hC⟩
  have e : A ∪ insert c1 (insert y1 (insert x1 B)) = A ∪ B := by
    rw [Finset.union_insert, Finset.union_insert, Finset.union_insert,
      Finset.insert_eq_of_mem (Finset.mem_union_left _ ha1A),
      Finset.insert_eq_of_mem (Finset.mem_union_left _ hb1A),
      Finset.insert_eq_of_mem (Finset.mem_union_left _ hc1A)]
  rw [← e]
  exact hT

/-- Tree-width transfer: a decomposition of `G` serves any graph whose edges are edges of `G`
or lie in a common bag. -/
theorem tw_transfer {T : Type} [Fintype T] {G G' : SimpleGraph V} {t : SimpleGraph T}
    {X : T → Finset V} (htd : RobertsonSeymour1986.GM5.IsTreeDecomposition G t X)
    (hw : ∀ s, (X s).card ≤ 3 + 1)
    (h : ∀ x y, G'.Adj x y → G.Adj x y ∨ ∃ s, x ∈ X s ∧ y ∈ X s) :
    RobertsonSeymour1986.GM5.TreewidthLE G' 3 := by
  obtain ⟨h1, h2, h3, h4⟩ := htd
  refine ⟨T, inferInstance, t, X, ⟨h1, h2, ?_, h4⟩, hw⟩
  intro x y hxy
  rcases h x y hxy with h' | h'
  · exact h3 x y h'
  · exact h'

theorem tw_mono {G G' : SimpleGraph V} (hle : G' ≤ G)
    (h : RobertsonSeymour1986.GM5.TreewidthLE G 3) : RobertsonSeymour1986.GM5.TreewidthLE G' 3 := by
  obtain ⟨T, hT, t, X, htd, hw⟩ := h
  exact tw_transfer htd hw (fun x y hxy => Or.inl (hle hxy))

end C2a

end PQL5

/-! C2 toolkit B (session 3): SEP — in a 3-tree, a triangle with two common neighbours `p, q`
separates `p` from `q` (stated with a closed predicate: no walk from `p` to `q` avoids it). -/

namespace PQL5

section C2b

variable {V : Type} [DecidableEq V]

theorem TTb.sep {H : SimpleGraph V} {S : Finset V} {x y z : V} (h : TTb H S x y z) :
    ∀ a b c p q : V, H.Adj a b → H.Adj b c → H.Adj a c → p ≠ q → H.Adj p a → H.Adj p b →
      H.Adj p c → H.Adj q a → H.Adj q b → H.Adj q c →
      ∃ P : V → Prop, P p ∧ ¬ P q ∧
        ∀ u w, P u → ¬ In3 a b c u → H.Adj u w → ¬ In3 a b c w → P w := by
  induction h with
  | base x y z hxy hyz hxz =>
    intro a b c p q hab hbc hac hpq hpa hpb hpc _ _ _
    exfalso
    exact four_of_three (tri_In3_of_adj hab).1 (tri_In3_of_adj hab).2 (tri_In3_of_adj hbc).2
      (tri_In3_of_adj hpa).1 hab.ne hac.ne (Ne.symm hpa.ne) hbc.ne (Ne.symm hpb.ne)
      (Ne.symm hpc.ne)
  | @stack H S x y z v p0 q0 r0 hH hvS hp0 hq0 hr0 hpq0 hqr0 hpr0 ih =>
    intro a b c p q hab hbc hac hpq hpa hpb hpc hqa hqb hqc
    have hs := hH.supp
    have hnv : ∀ u, ¬ H.Adj v u := fun u h => hvS (hs v u h).1
    have hvp : v ≠ p0 := fun h => hvS (h ▸ hp0)
    have hvq : v ≠ q0 := fun h => hvS (h ▸ hq0)
    have hvr : v ≠ r0 := fun h => hvS (h ▸ hr0)
    have hN := stack_nbr hnv hvp hvq hvr
    have hN' : ∀ u, (H ⊔ star3 v p0 q0 r0).Adj u v → In3 p0 q0 r0 u := fun u h => hN u h.symm
    have hO := @stack_old V _ H v p0 q0 r0
    by_cases ha : a = v
    · exfalso
      rw [ha] at hab hac hpa hqa
      exact four_of_three (hN b hab) (hN c hac) (hN' p hpa) (hN' q hqa) hbc.ne
        (Ne.symm hpb.ne) (Ne.symm hqb.ne) (Ne.symm hpc.ne) (Ne.symm hqc.ne) hpq
    by_cases hb : b = v
    · exfalso
      rw [hb] at hab hbc hpb hqb
      exact four_of_three (hN a hab.symm) (hN c hbc) (hN' p hpb) (hN' q hqb) hac.ne
        (Ne.symm hpa.ne) (Ne.symm hqa.ne) (Ne.symm hpc.ne) (Ne.symm hqc.ne) hpq
    by_cases hc : c = v
    · exfalso
      rw [hc] at hac hbc hpc hqc
      exact four_of_three (hN a hac.symm) (hN b hbc.symm) (hN' p hpc) (hN' q hqc) hab.ne
        (Ne.symm hpa.ne) (Ne.symm hqa.ne) (Ne.symm hpb.ne) (Ne.symm hqb.ne) hpq
    by_cases hp : p = v
    · have hcov := In3_cover (hN a (hp ▸ hpa)) (hN b (hp ▸ hpb)) (hN c (hp ▸ hpc))
        hab.ne hbc.ne hac.ne
      refine ⟨fun u => u = v, hp, fun h => hpq (hp.trans h.symm), ?_⟩
      intro u w hu _ huw hw
      exact (hw (hcov w (hN w (hu ▸ huw)))).elim
    by_cases hq : q = v
    · have hcov := In3_cover (hN a (hq ▸ hqa)) (hN b (hq ▸ hqb)) (hN c (hq ▸ hqc))
        hab.ne hbc.ne hac.ne
      refine ⟨fun u => u ≠ v, hp, fun h => h hq, ?_⟩
      intro u w _ hu' huw _ hwv
      apply hu'
      rw [hwv] at huw
      exact hcov u (hN' u huw)
    obtain ⟨P, hPp, hPq, hPc⟩ := ih a b c p q (hO a b hab ha hb) (hO b c hbc hb hc)
      (hO a c hac ha hc) hpq (hO p a hpa hp ha) (hO p b hpb hp hb) (hO p c hpc hp hc)
      (hO q a hqa hq ha) (hO q b hqb hq hb) (hO q c hqc hq hc)
    have hF : ∀ s t, In3 p0 q0 r0 s → In3 p0 q0 r0 t → s ≠ t → H.Adj s t := by
      intro s t hs' ht' hst
      rcases hs' with rfl | rfl | rfl <;> rcases ht' with rfl | rfl | rfl <;>
        first | exact absurd rfl hst | exact hpq0 | exact hqr0 | exact hpr0 |
          exact hpq0.symm | exact hqr0.symm | exact hpr0.symm
    refine ⟨fun u => (u ≠ v ∧ P u) ∨ (u = v ∧ ∃ s, In3 p0 q0 r0 s ∧ ¬ In3 a b c s ∧ P s),
      Or.inl ⟨hp, hPp⟩, ?_, ?_⟩
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact hPq h
      · exact hq h
    · intro u w hu hu' huw hw
      by_cases hwv : w = v
      · right
        refine ⟨hwv, ?_⟩
        rw [hwv] at huw
        rcases hu with ⟨_, hPu⟩ | ⟨huv, _⟩
        · exact ⟨u, hN' u huw, hu', hPu⟩
        · exact absurd huv huw.ne
      · left
        refine ⟨hwv, ?_⟩
        rcases hu with ⟨huv, hPu⟩ | ⟨huv, s, hsF, hsT, hPs⟩
        · exact hPc u w hPu hu' (hO u w huw huv hwv) hw
        · rw [huv] at huw
          have hwF := hN w huw
          by_cases hsw : s = w
          · rw [← hsw]
            exact hPs
          · exact hPc s w hPs hsT (hF s w hsF hwF hsw) hw

end C2b

end PQL5

/-! C2 toolkit C (session 3): minors of subgraphs. -/

namespace PQL5

theorem minor_of_le {W V : Type} {K : SimpleGraph W} {G G' : SimpleGraph V} (hle : G' ≤ G)
    (hm : RobertsonSeymour1986.GM5.IsMinor K G') : RobertsonSeymour1986.GM5.IsMinor K G := by
  obtain ⟨β, h1, h2, h3⟩ := hm
  refine ⟨β, fun w => ⟨(h1 w).1, (h1 w).2.mono (fun a b h => hle h)⟩, h2, ?_⟩
  intro a b hab
  obtain ⟨x, hx, y, hy, hxy⟩ := h3 a b hab
  exact ⟨x, hx, y, hy, hle hxy⟩

end PQL5

/-! C2 toolkit D (session 4): set contraction, K33 from three sets, components, splits. -/

namespace PQL5

open RobertsonSeymour1986.GM5

abbrev KK33 : SimpleGraph (Fin 3 ⊕ Fin 3) := completeBipartiteGraph (Fin 3) (Fin 3)

theorem connected_of_le_on {V : Type} {G G2 : SimpleGraph V} {s : Set V}
    (hc : (G2.induce s).Connected) (h : ∀ x y, x ∈ s → y ∈ s → G2.Adj x y → G.Adj x y) :
    (G.induce s).Connected := by
  refine hc.mono ?_
  intro u w huw
  have := h u w u.2 w.2 (by simpa using huw)
  simpa using this

theorem induce_singleton_conn {V : Type} (G : SimpleGraph V) (v : V) :
    (G.induce ({v} : Set V)).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨v, rfl⟩, ?_⟩
  rintro ⟨y, hy⟩
  have : y = v := hy
  subst this
  exact SimpleGraph.Reachable.refl _

/-- **Set contraction.** Contracting a connected set `C` (adjacent to `a`) into `a`. -/
theorem minor_contract {W V : Type} (K : SimpleGraph W) (hKiso : ∀ w, ∃ w', K.Adj w w')
    (G G2 : SimpleGraph V) (C : Set V) (a : V) (hC : (G.induce C).Connected)
    (hac : ∃ c ∈ C, G.Adj a c)
    (hG2 : ∀ x y, G2.Adj x y → x ∉ C ∧ y ∉ C ∧ (G.Adj x y ∨ (x = a ∧ ∃ c ∈ C, G.Adj c y) ∨
      (y = a ∧ ∃ c ∈ C, G.Adj c x)))
    (hm : IsMinor K G2) : IsMinor K G := by
  classical
  obtain ⟨β, hβ, hpw, hadj⟩ := hm
  have hCβ : ∀ w, ∀ x ∈ β w, x ∉ C := by
    intro w x hx hxC
    obtain ⟨w', hww'⟩ := hKiso w
    obtain ⟨x', hx', y, _, hxy⟩ := hadj w w' hww'
    have hall : ∀ y ∈ β w, y = x :=
      induce_closed (hβ w).2 (fun y => y = x) hx rfl
        (fun u y _ _ huy hu => absurd (show u ∈ C by rw [hu]; exact hxC) (hG2 u y huy).1)
    have hx'C : x' ∈ C := by rw [hall x' hx']; exact hxC
    exact (hG2 x' y hxy).1 hx'C
  have hdis : ∀ p q x, x ∈ β p → x ∈ β q → p = q := by
    intro p q x hp hq
    by_contra hne
    exact Set.disjoint_left.1 (hpw hne) hp hq
  obtain ⟨c0, hc0, hac0⟩ := hac
  have hsub : ∀ w, β w ⊆ (if a ∈ β w then β w ∪ C else β w) := by
    intro w
    split_ifs
    · exact Set.subset_union_left
    · exact le_rfl
  refine ⟨fun w => if a ∈ β w then β w ∪ C else β w, ?_, ?_, ?_⟩
  · intro w
    refine ⟨(hβ w).1.mono (hsub w), ?_⟩
    show (G.induce (if a ∈ β w then β w ∪ C else β w)).Connected
    by_cases haw : a ∈ β w
    · rw [if_pos haw]
      have haU : a ∈ β w ∪ C := Or.inl haw
      have hCr : ∀ y ∈ C, ∃ hy : y ∈ β w ∪ C,
          (G.induce (β w ∪ C)).Reachable ⟨a, haU⟩ ⟨y, hy⟩ := by
        refine induce_closed hC (fun y => ∃ hy : y ∈ β w ∪ C,
          (G.induce (β w ∪ C)).Reachable ⟨a, haU⟩ ⟨y, hy⟩) hc0 ?_ ?_
        · exact ⟨Or.inr hc0, SimpleGraph.Adj.reachable (by simpa using hac0)⟩
        · rintro x y _ hy hxy ⟨_, hr⟩
          exact ⟨Or.inr hy, hr.trans (SimpleGraph.Adj.reachable (by simpa using hxy))⟩
      have hβr : ∀ y ∈ β w, ∃ hy : y ∈ β w ∪ C,
          (G.induce (β w ∪ C)).Reachable ⟨a, haU⟩ ⟨y, hy⟩ := by
        refine induce_closed (hβ w).2 (fun y => ∃ hy : y ∈ β w ∪ C,
          (G.induce (β w ∪ C)).Reachable ⟨a, haU⟩ ⟨y, hy⟩) haw
          ⟨haU, SimpleGraph.Reachable.refl _⟩ ?_
        rintro x y _ hy hxy ⟨_, hr⟩
        refine ⟨Or.inl hy, ?_⟩
        rcases (hG2 x y hxy).2.2 with h | ⟨_, c, hc, hcy⟩ | ⟨hya, _⟩
        · exact hr.trans (SimpleGraph.Adj.reachable (by simpa using h))
        · obtain ⟨_, hr'⟩ := hCr c hc
          exact hr'.trans (SimpleGraph.Adj.reachable (by simpa using hcy))
        · subst hya
          exact SimpleGraph.Reachable.refl _
      rw [SimpleGraph.connected_iff_exists_forall_reachable]
      refine ⟨⟨a, haU⟩, ?_⟩
      rintro ⟨y, hy⟩
      rcases hy with h | h
      · exact (hβr y h).2
      · exact (hCr y h).2
    · rw [if_neg haw]
      refine connected_of_le_on (hβ w).2 (fun x y hx hy hxy => ?_)
      rcases (hG2 x y hxy).2.2 with h | ⟨hxa, _⟩ | ⟨hya, _⟩
      · exact h
      · exact absurd (hxa ▸ hx) haw
      · exact absurd (hya ▸ hy) haw
  · intro p q hpq
    show Disjoint (if a ∈ β p then β p ∪ C else β p) (if a ∈ β q then β q ∪ C else β q)
    have hpq0 := hpw hpq
    rw [Set.disjoint_left]
    intro x hxp hxq
    have hx1 : x ∈ β p ∨ (a ∈ β p ∧ x ∈ C) := by
      split_ifs at hxp with h
      · rcases hxp with h' | h'
        · exact Or.inl h'
        · exact Or.inr ⟨h, h'⟩
      · exact Or.inl hxp
    have hx2 : x ∈ β q ∨ (a ∈ β q ∧ x ∈ C) := by
      split_ifs at hxq with h
      · rcases hxq with h' | h'
        · exact Or.inl h'
        · exact Or.inr ⟨h, h'⟩
      · exact Or.inl hxq
    rcases hx1 with h1 | ⟨ha1, hc1⟩ <;> rcases hx2 with h2 | ⟨ha2, hc2⟩
    · exact Set.disjoint_left.1 hpq0 h1 h2
    · exact hCβ p x h1 hc2
    · exact hCβ q x h2 hc1
    · exact hpq (hdis p q a ha1 ha2)
  · intro p q hpq
    obtain ⟨x, hx, y, hy, hxy⟩ := hadj p q hpq
    rcases (hG2 x y hxy).2.2 with h | ⟨hxa, c, hc, hcy⟩ | ⟨hya, c, hc, hcx⟩
    · exact ⟨x, hsub p hx, y, hsub q hy, h⟩
    · have hap : a ∈ β p := hxa ▸ hx
      refine ⟨c, ?_, y, hsub q hy, hcy⟩
      show c ∈ (if a ∈ β p then β p ∪ C else β p)
      rw [if_pos hap]
      exact Or.inr hc
    · have haq : a ∈ β q := hya ▸ hy
      refine ⟨x, hsub p hx, c, ?_, hcx.symm⟩
      show c ∈ (if a ∈ β q then β q ∪ C else β q)
      rw [if_pos haq]
      exact Or.inr hc

/-- Three disjoint connected sets each seeing all of `a, b, c` give a `K₃,₃` minor. -/
theorem K33_of_three {V : Type} (G : SimpleGraph V) (a b c : V) (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) (D : Fin 3 → Set V) (hD : ∀ i, (D i).Nonempty ∧ (G.induce (D i)).Connected)
    (hDd : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (hDT : ∀ i, a ∉ D i ∧ b ∉ D i ∧ c ∉ D i)
    (hsee : ∀ i, (∃ x ∈ D i, G.Adj a x) ∧ (∃ x ∈ D i, G.Adj b x) ∧ (∃ x ∈ D i, G.Adj c x)) :
    IsMinor KK33 G := by
  let f : Fin 3 → V := ![a, b, c]
  have hf : ∀ i j, f i = f j → i = j := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hfD : ∀ i j, f i ∉ D j := by
    intro i j
    fin_cases i <;> simp [f, hDT j]
  have hfs : ∀ i j, ∃ x ∈ D j, G.Adj (f i) x := by
    intro i j
    fin_cases i
    · exact (hsee j).1
    · exact (hsee j).2.1
    · exact (hsee j).2.2
  refine ⟨fun w => Sum.elim (fun i => ({f i} : Set V)) D w, ?_, ?_, ?_⟩
  · rintro (i | j)
    · exact ⟨Set.singleton_nonempty _, induce_singleton_conn G (f i)⟩
    · exact hD j
  · rintro (i | i) (j | j) hij
    · have : i ≠ j := fun h => hij (by rw [h])
      simp only [Sum.elim_inl, Set.disjoint_singleton]
      exact fun h => this (hf i j h)
    · simp only [Sum.elim_inl, Sum.elim_inr, Set.disjoint_singleton_left]
      exact hfD i j
    · simp only [Sum.elim_inl, Sum.elim_inr, Set.disjoint_singleton_right]
      exact hfD j i
    · exact hDd i j (fun h => hij (by rw [h]))
  · rintro (i | i) (j | j) hij
    · simp at hij
    · obtain ⟨x, hx, hxa⟩ := hfs i j
      exact ⟨f i, rfl, x, hx, hxa⟩
    · obtain ⟨x, hx, hxa⟩ := hfs j i
      exact ⟨x, hx, f j, rfl, hxa.symm⟩
    · simp at hij

/-- reachability inside `R` -/
def reachR {V : Type} (G : SimpleGraph V) (R : Finset V) : V → V → Prop :=
  Relation.ReflTransGen (fun x y => G.Adj x y ∧ x ∈ R ∧ y ∈ R)

theorem reachR_symm {V : Type} {G : SimpleGraph V} {R : Finset V} {x y : V}
    (h : reachR G R x y) : reachR G R y x := by
  unfold reachR at *
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head ⟨hbc.1.symm, hbc.2.2, hbc.2.1⟩ ih

theorem reachR_trans {V : Type} {G : SimpleGraph V} {R : Finset V} {x y z : V}
    (h : reachR G R x y) (h' : reachR G R y z) : reachR G R x z := by
  unfold reachR at *
  exact h.trans h'

open Classical in
/-- the component of `x` in `G[R]` -/
noncomputable def compR {V : Type} (G : SimpleGraph V) (R : Finset V) (x : V) : Finset V :=
  R.filter (fun y => reachR G R x y)

open Classical in
theorem compR_mem {V : Type} {G : SimpleGraph V} {R : Finset V} {x y : V} :
    y ∈ compR G R x ↔ y ∈ R ∧ reachR G R x y := by
  unfold compR
  rw [Finset.mem_filter]

theorem compR_sub {V : Type} {G : SimpleGraph V} {R : Finset V} {x : V} : compR G R x ⊆ R :=
  fun _ h => (compR_mem.1 h).1

theorem compR_self {V : Type} {G : SimpleGraph V} {R : Finset V} {x : V} (hx : x ∈ R) :
    x ∈ compR G R x := compR_mem.2 ⟨hx, Relation.ReflTransGen.refl⟩

theorem compR_closed {V : Type} {G : SimpleGraph V} {R : Finset V} {x y w : V}
    (hy : y ∈ compR G R x) (hw : w ∈ R) (hyw : G.Adj y w) : w ∈ compR G R x := by
  rw [compR_mem] at hy ⊢
  exact ⟨hw, Relation.ReflTransGen.tail hy.2 ⟨hyw, hy.1, hw⟩⟩

theorem compR_conn {V : Type} {G : SimpleGraph V} {R : Finset V} {x : V} (hx : x ∈ R) :
    (G.induce (↑(compR G R x) : Set V)).Connected := by
  have hxm : x ∈ (↑(compR G R x) : Set V) := compR_self hx
  have key : ∀ z, reachR G R x z → ∃ hz : z ∈ (↑(compR G R x) : Set V),
      (G.induce (↑(compR G R x) : Set V)).Reachable ⟨x, hxm⟩ ⟨z, hz⟩ := by
    intro z hz
    unfold reachR at hz
    induction hz with
    | refl => exact ⟨hxm, SimpleGraph.Reachable.refl _⟩
    | @tail b c hb hbc ih =>
      obtain ⟨_, hr⟩ := ih
      have hcm : c ∈ (↑(compR G R x) : Set V) := compR_mem.2 ⟨hbc.2.2, hb.tail hbc⟩
      exact ⟨hcm, hr.trans (SimpleGraph.Adj.reachable (by simpa using hbc.1))⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨x, hxm⟩, ?_⟩
  rintro ⟨y, hy⟩
  exact (key y (compR_mem.1 hy).2).2

theorem compR_disj {V : Type} {G : SimpleGraph V} {R : Finset V} {p q w : V} (hq : q ∈ R)
    (hpq : q ∉ compR G R p) (hwp : w ∈ compR G R p) (hwq : w ∈ compR G R q) : False :=
  hpq (compR_mem.2 ⟨hq, reachR_trans (compR_mem.1 hwp).2 (reachR_symm (compR_mem.1 hwq).2)⟩)

/-- `G` restricted to `A` -/
def res {V : Type} (G : SimpleGraph V) (A : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∈ A ∧ y ∈ A
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.ne_of_adj h.1 rfl⟩

theorem res_le {V : Type} {G : SimpleGraph V} {A : Finset V} : res G A ≤ G :=
  fun _ _ h => h.1

theorem card_lt_of_out {V : Type} {A S : Finset V} (h : A ⊆ S) {w : V} (hw : w ∈ S)
    (hwA : w ∉ A) : A.card < S.card :=
  Finset.card_lt_card ⟨h, fun h' => hwA (h' hw)⟩

theorem three_le_card {V : Type} {A : Finset V} {x y z : V} (hx : x ∈ A) (hy : y ∈ A)
    (hz : z ∈ A) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : 3 ≤ A.card := by
  have : 2 < A.card := Finset.two_lt_card.2 ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩
  omega

/-- the induction hypothesis of C2 -/
def C2IH (V : Type) [DecidableEq V] (n : ℕ) : Prop :=
  ∀ (S' : Finset V) (G' : SimpleGraph V), S'.card < n → (∀ x y, G'.Adj x y → x ∈ S' ∧ y ∈ S') →
    3 ≤ S'.card → TreewidthLE G' 3 → ¬ IsMinor KK33 G' → ∃ H, G' ≤ H ∧ TT H S' ∧ TriCond H

end PQL5

/-! C2 toolkit E (session 4): separations and the degree-3 step. -/

namespace PQL5

open RobertsonSeymour1986.GM5

theorem res_adj {V : Type} {G : SimpleGraph V} {A : Finset V} {x y : V} :
    (res G A).Adj x y ↔ G.Adj x y ∧ x ∈ A ∧ y ∈ A := Iff.rfl

theorem K33_of_three' {V : Type} (G : SimpleGraph V) (a b c : V) (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) (D0 D1 D2 : Set V) (h0 : D0.Nonempty ∧ (G.induce D0).Connected)
    (h1 : D1.Nonempty ∧ (G.induce D1).Connected) (h2 : D2.Nonempty ∧ (G.induce D2).Connected)
    (d01 : Disjoint D0 D1) (d02 : Disjoint D0 D2) (d12 : Disjoint D1 D2)
    (t0 : a ∉ D0 ∧ b ∉ D0 ∧ c ∉ D0) (t1 : a ∉ D1 ∧ b ∉ D1 ∧ c ∉ D1)
    (t2 : a ∉ D2 ∧ b ∉ D2 ∧ c ∉ D2)
    (s0 : (∃ x ∈ D0, G.Adj a x) ∧ (∃ x ∈ D0, G.Adj b x) ∧ (∃ x ∈ D0, G.Adj c x))
    (s1 : (∃ x ∈ D1, G.Adj a x) ∧ (∃ x ∈ D1, G.Adj b x) ∧ (∃ x ∈ D1, G.Adj c x))
    (s2 : (∃ x ∈ D2, G.Adj a x) ∧ (∃ x ∈ D2, G.Adj b x) ∧ (∃ x ∈ D2, G.Adj c x)) :
    IsMinor KK33 G := by
  refine K33_of_three G a b c hab hbc hac ![D0, D1, D2] ?_ ?_ ?_ ?_
  · intro i; fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | exact d01 | exact d01.symm | exact d02 | exact d02.symm | exact d12 | exact d12.symm
  · intro i; fin_cases i
    · exact t0
    · exact t1
    · exact t2
  · intro i; fin_cases i
    · exact s0
    · exact s1
    · exact s2

section C2e

variable {V : Type} [DecidableEq V]

theorem c2_split01 {S : Finset V} {G : SimpleGraph V}
    (hIH : C2IH V S.card) (hsupp : ∀ x y, G.Adj x y → x ∈ S ∧ y ∈ S)
    (hdeg : ∀ u ∈ S, ∃ w1 w2, w1 ≠ w2 ∧ G.Adj u w1 ∧ G.Adj u w2)
    (htw : TreewidthLE G 3) (hK : ¬ IsMinor KK33 G)
    (C Y : Finset V) (hCne : C.Nonempty) (hCS : C ⊆ S) (hY : Y.card ≤ 1) (hYS : Y ⊆ S)
    (hYC : ∀ u ∈ Y, u ∉ C) (hB3 : 3 ≤ (S \ C).card) (hout : ∃ w ∈ S, w ∉ C ∧ w ∉ Y)
    (hcl : ∀ c ∈ C, ∀ w, G.Adj c w → w ∈ C ∨ w ∈ Y) :
    ∃ H, G ≤ H ∧ TT H S ∧ TriCond H := by
  have hAS : C ∪ Y ⊆ S := Finset.union_subset hCS hYS
  have hAlt : (C ∪ Y).card < S.card := by
    obtain ⟨w, hw, hwC, hwY⟩ := hout
    exact card_lt_of_out hAS hw (by rw [Finset.mem_union]; tauto)
  obtain ⟨c, hc⟩ := hCne
  have hBlt : (S \ C).card < S.card :=
    card_lt_of_out Finset.sdiff_subset (hCS hc) (fun h => (Finset.mem_sdiff.1 h).2 hc)
  have hA3 : 3 ≤ (C ∪ Y).card := by
    obtain ⟨w1, w2, h12, h1, h2⟩ := hdeg c (hCS hc)
    have m1 : w1 ∈ C ∪ Y := Finset.mem_union.2 (hcl c hc w1 h1)
    have m2 : w2 ∈ C ∪ Y := Finset.mem_union.2 (hcl c hc w2 h2)
    exact three_le_card (Finset.mem_union_left _ hc) m1 m2 (G.ne_of_adj h1) (G.ne_of_adj h2) h12
  obtain ⟨H1, h1le, hT1, hC1⟩ := hIH (C ∪ Y) (res G (C ∪ Y)) hAlt
    (fun x y h => ⟨(res_adj.1 h).2.1, (res_adj.1 h).2.2⟩)
    hA3 (tw_mono res_le htw) (fun h => hK (minor_of_le res_le h))
  obtain ⟨H2, h2le, hT2, hC2⟩ := hIH (S \ C) (res G (S \ C)) hBlt
    (fun x y h => ⟨(res_adj.1 h).2.1, (res_adj.1 h).2.2⟩)
    hB3 (tw_mono res_le htw) (fun h => hK (minor_of_le res_le h))
  have hcover : C ∪ Y ∪ S \ C = S := by
    ext u
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ((h | h) | ⟨h, _⟩)
      · exact hCS h
      · exact hYS h
      · exact h
    · intro h
      by_cases hu : u ∈ C
      · exact Or.inl (Or.inl hu)
      · exact Or.inr ⟨h, hu⟩
  have hGle : G ≤ H1 ⊔ H2 := by
    intro u w huw
    rw [SimpleGraph.sup_adj]
    by_cases hu : u ∈ C
    · exact Or.inl (h1le (res_adj.2 ⟨huw, Finset.mem_union_left _ hu,
        Finset.mem_union.2 (hcl u hu w huw)⟩))
    · by_cases hw : w ∈ C
      · exact Or.inl (h1le (res_adj.2 ⟨huw, Finset.mem_union.2 (hcl w hw u huw.symm),
          Finset.mem_union_left _ hw⟩))
      · exact Or.inr (h2le (res_adj.2 ⟨huw, Finset.mem_sdiff.2 ⟨(hsupp u w huw).1, hu⟩,
          Finset.mem_sdiff.2 ⟨(hsupp u w huw).2, hw⟩⟩))
  have fin : ∀ H, H1 ⊔ H2 ≤ H → TT H (C ∪ Y ∪ S \ C) → TriCond H →
      ∃ H, G ≤ H ∧ TT H S ∧ TriCond H := by
    intro H hle hT hC
    rw [hcover] at hT
    exact ⟨H, le_trans hGle hle, hT, hC⟩
  by_cases hy : ∃ y, y ∈ Y
  · obtain ⟨y, hyY⟩ := hy
    obtain ⟨H, hle, hT, hC⟩ := glue_sep1 (a := y) hT1 hC1 hT2 hC2 (Finset.mem_union_right _ hyY)
      (Finset.mem_sdiff.2 ⟨hYS hyY, hYC y hyY⟩) (by
        intro u hu1 hu2
        have huC := (Finset.mem_sdiff.1 hu2).2
        rcases Finset.mem_union.1 hu1 with h | h
        · exact absurd h huC
        · exact Finset.card_le_one.1 hY u h y hyY)
    exact fin H hle hT hC
  · push Not at hy
    obtain ⟨H, hle, hT, hC⟩ := glue_sep0 hT1 hC1 hT2 hC2 (by
        intro u hu1 hu2
        have huC := (Finset.mem_sdiff.1 hu2).2
        rcases Finset.mem_union.1 hu1 with h | h
        · exact huC h
        · exact hy u h)
    exact fin H hle hT hC

theorem c2_split2 {S : Finset V} {G : SimpleGraph V}
    (hIH : C2IH V S.card) (hsupp : ∀ x y, G.Adj x y → x ∈ S ∧ y ∈ S)
    (hK : ¬ IsMinor KK33 G) (y z v : V) (hyz : y ≠ z)
    (htw : TreewidthLE (G ⊔ tri y z z) 3) (hvy : G.Adj v y) (hvz : G.Adj v z)
    (C : Finset V) (hCS : C ⊆ S) (hvC : v ∉ C) (hyC : y ∉ C) (hzC : z ∉ C)
    (hCconn : (G.induce (↑C : Set V)).Connected)
    (hcl : ∀ c ∈ C, ∀ w, G.Adj c w → w ∈ C ∨ w = y ∨ w = z)
    (hsy : ∃ c ∈ C, G.Adj c y) (hsz : ∃ c ∈ C, G.Adj c z) :
    ∃ H, G ≤ H ∧ TT H S ∧ TriCond H := by
  have hvS := (hsupp v y hvy).1
  have hyS := (hsupp v y hvy).2
  have hzS := (hsupp v z hvz).2
  have hvy' := G.ne_of_adj hvy
  have hvz' := G.ne_of_adj hvz
  obtain ⟨c, hc, hcy⟩ := hsy
  have hmA : ∀ u, u ∈ C ∪ {y, z} ↔ u ∈ C ∨ u = y ∨ u = z := by
    intro u
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  have hAS : C ∪ {y, z} ⊆ S := by
    intro u hu
    rcases (hmA u).1 hu with h | h | h
    · exact hCS h
    · rw [h]; exact hyS
    · rw [h]; exact hzS
  have hAlt : (C ∪ {y, z}).card < S.card := card_lt_of_out hAS hvS (by
    rw [hmA]
    rintro (h | h | h)
    · exact hvC h
    · exact hvy' h
    · exact hvz' h)
  have hBlt : (S \ C).card < S.card :=
    card_lt_of_out Finset.sdiff_subset (hCS hc) (fun h => (Finset.mem_sdiff.1 h).2 hc)
  have hcy' : c ≠ y := fun h => hyC (h ▸ hc)
  have hcz' : c ≠ z := fun h => hzC (h ▸ hc)
  have hA3 : 3 ≤ (C ∪ {y, z}).card :=
    three_le_card ((hmA c).2 (Or.inl hc)) ((hmA y).2 (Or.inr (Or.inl rfl)))
      ((hmA z).2 (Or.inr (Or.inr rfl))) hcy' hcz' hyz
  have hB3 : 3 ≤ (S \ C).card :=
    three_le_card (Finset.mem_sdiff.2 ⟨hvS, hvC⟩) (Finset.mem_sdiff.2 ⟨hyS, hyC⟩)
      (Finset.mem_sdiff.2 ⟨hzS, hzC⟩) hvy' hvz' hyz
  have hyzA : ∀ u, In3 y z z u → u ∈ C ∪ {y, z} := by
    intro u hu
    rcases hu with h | h | h
    · exact (hmA u).2 (Or.inr (Or.inl h))
    · exact (hmA u).2 (Or.inr (Or.inr h))
    · exact (hmA u).2 (Or.inr (Or.inr h))
  have hyzB : ∀ u, In3 y z z u → u ∈ S \ C := by
    intro u hu
    rcases hu with h | h | h
    · rw [h]; exact Finset.mem_sdiff.2 ⟨hyS, hyC⟩
    · rw [h]; exact Finset.mem_sdiff.2 ⟨hzS, hzC⟩
    · rw [h]; exact Finset.mem_sdiff.2 ⟨hzS, hzC⟩
  have hG1K : ¬ IsMinor KK33 (res G (C ∪ {y, z}) ⊔ tri y z z) := by
    intro hm
    refine hK (minor_YDelta KK33 K33_triangle_free K33_no_isolated G _ v y z z hvy hvz hvz ?_ hm)
    intro x w hxw
    rw [SimpleGraph.sup_adj] at hxw
    rcases hxw with h | h
    · have h' := res_adj.1 h
      refine ⟨?_, Or.inl h'.1⟩
      intro hxv
      rw [hxv] at h'
      rcases (hmA _).1 h'.2.1 with h1 | h1 | h1
      · exact hvC h1
      · exact hvy' h1
      · exact hvz' h1
    · obtain ⟨h1, h2⟩ := tri_In3_of_adj h
      refine ⟨?_, Or.inr ⟨h1, h2⟩⟩
      intro hxv
      rw [hxv] at h1
      rcases h1 with h1 | h1 | h1
      · exact hvy' h1
      · exact hvz' h1
      · exact hvz' h1
  have hG2K : ¬ IsMinor KK33 (res G (S \ C) ⊔ tri y z z) := by
    intro hm
    refine hK (minor_contract KK33 K33_no_isolated G _ (↑C) y hCconn ⟨c, hc, hcy.symm⟩ ?_ hm)
    intro x w hxw
    rw [SimpleGraph.sup_adj] at hxw
    rcases hxw with h | h
    · have h' := res_adj.1 h
      exact ⟨(Finset.mem_sdiff.1 h'.2.1).2, (Finset.mem_sdiff.1 h'.2.2).2, Or.inl h'.1⟩
    · have hne := (tri y z z).ne_of_adj h
      obtain ⟨h1, h2⟩ := tri_In3_of_adj h
      have hx : x = y ∨ x = z := by rcases h1 with h1 | h1 | h1 <;> tauto
      have hw : w = y ∨ w = z := by rcases h2 with h2 | h2 | h2 <;> tauto
      rcases hx with hx | hx <;> rcases hw with hw | hw
      · exact absurd (hx.trans hw.symm) hne
      · rw [hx, hw]
        exact ⟨hyC, hzC, Or.inr (Or.inl ⟨rfl, hsz⟩)⟩
      · rw [hx, hw]
        exact ⟨hzC, hyC, Or.inr (Or.inr ⟨rfl, hsz⟩)⟩
      · exact absurd (hx.trans hw.symm) hne
  obtain ⟨H1, h1le, hT1, hC1⟩ := hIH (C ∪ {y, z}) (res G (C ∪ {y, z}) ⊔ tri y z z) hAlt
    (by
      intro x w h
      rw [SimpleGraph.sup_adj] at h
      rcases h with h | h
      · exact ⟨(res_adj.1 h).2.1, (res_adj.1 h).2.2⟩
      · exact ⟨hyzA x (tri_In3_of_adj h).1, hyzA w (tri_In3_of_adj h).2⟩)
    hA3 (tw_mono (sup_le_sup_right res_le _) htw) hG1K
  obtain ⟨H2, h2le, hT2, hC2⟩ := hIH (S \ C) (res G (S \ C) ⊔ tri y z z) hBlt
    (by
      intro x w h
      rw [SimpleGraph.sup_adj] at h
      rcases h with h | h
      · exact ⟨(res_adj.1 h).2.1, (res_adj.1 h).2.2⟩
      · exact ⟨hyzB x (tri_In3_of_adj h).1, hyzB w (tri_In3_of_adj h).2⟩)
    hB3 (tw_mono (sup_le_sup_right res_le _) htw) hG2K
  have htyz : (tri y z z).Adj y z := tri_adj_of_In3 (Or.inl rfl) (Or.inr (Or.inl rfl)) hyz
  obtain ⟨H, hle, hT, hC⟩ := glue_sep2 (a := y) (b := z) hT1 hC1 hT2 hC2
    (h1le (by rw [SimpleGraph.sup_adj]; exact Or.inr htyz))
    (h2le (by rw [SimpleGraph.sup_adj]; exact Or.inr htyz)) (by
      intro u hu1 hu2
      rcases (hmA u).1 hu1 with h | h | h
      · exact absurd h (Finset.mem_sdiff.1 hu2).2
      · exact Or.inl h
      · exact Or.inr h)
  have hcover : C ∪ {y, z} ∪ S \ C = S := by
    ext u
    rw [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (h | ⟨h, _⟩)
      · exact hAS h
      · exact h
    · intro h
      by_cases hu : u ∈ C
      · exact Or.inl ((hmA u).2 (Or.inl hu))
      · exact Or.inr ⟨h, hu⟩
  have hGle : G ≤ H1 ⊔ H2 := by
    intro u w huw
    rw [SimpleGraph.sup_adj]
    by_cases hu : u ∈ C
    · refine Or.inl (h1le ?_)
      rw [SimpleGraph.sup_adj]
      exact Or.inl (res_adj.2 ⟨huw, (hmA u).2 (Or.inl hu), (hmA w).2 (hcl u hu w huw)⟩)
    · by_cases hw : w ∈ C
      · refine Or.inl (h1le ?_)
        rw [SimpleGraph.sup_adj]
        exact Or.inl (res_adj.2 ⟨huw, (hmA u).2 (hcl w hw u huw.symm), (hmA w).2 (Or.inl hw)⟩)
      · refine Or.inr (h2le ?_)
        rw [SimpleGraph.sup_adj]
        exact Or.inl (res_adj.2 ⟨huw, Finset.mem_sdiff.2 ⟨(hsupp u w huw).1, hu⟩,
          Finset.mem_sdiff.2 ⟨(hsupp u w huw).2, hw⟩⟩)
  rw [hcover] at hT
  exact ⟨H, le_trans hGle hle, hT, hC⟩

/-- the separation step: `C` is a union of components of `G - {y, z}` not containing `v`. -/
theorem c2_split {S : Finset V} {G : SimpleGraph V}
    (hIH : C2IH V S.card) (hsupp : ∀ x y, G.Adj x y → x ∈ S ∧ y ∈ S)
    (hdeg : ∀ u ∈ S, ∃ w1 w2, w1 ≠ w2 ∧ G.Adj u w1 ∧ G.Adj u w2)
    (htw0 : TreewidthLE G 3) (hK : ¬ IsMinor KK33 G) (y z v : V) (hyz : y ≠ z)
    (htw : TreewidthLE (G ⊔ tri y z z) 3) (hvy : G.Adj v y) (hvz : G.Adj v z)
    (C : Finset V) (hCne : C.Nonempty) (hCS : C ⊆ S) (hvC : v ∉ C) (hyC : y ∉ C) (hzC : z ∉ C)
    (hCconn : (G.induce (↑C : Set V)).Connected)
    (hcl : ∀ c ∈ C, ∀ w, G.Adj c w → w ∈ C ∨ w = y ∨ w = z) :
    ∃ H, G ≤ H ∧ TT H S ∧ TriCond H := by
  have hvS := (hsupp v y hvy).1
  have hyS := (hsupp v y hvy).2
  have hzS := (hsupp v z hvz).2
  have hvy' := G.ne_of_adj hvy
  have hvz' := G.ne_of_adj hvz
  have hB3 : 3 ≤ (S \ C).card :=
    three_le_card (Finset.mem_sdiff.2 ⟨hvS, hvC⟩) (Finset.mem_sdiff.2 ⟨hyS, hyC⟩)
      (Finset.mem_sdiff.2 ⟨hzS, hzC⟩) hvy' hvz' hyz
  by_cases hsy : ∃ c ∈ C, G.Adj c y
  · by_cases hsz : ∃ c ∈ C, G.Adj c z
    · exact c2_split2 hIH hsupp hK y z v hyz htw hvy hvz C hCS hvC hyC hzC hCconn hcl hsy hsz
    · push Not at hsz
      refine c2_split01 hIH hsupp hdeg htw0 hK C {y} hCne hCS (by simp)
        (Finset.singleton_subset_iff.2 hyS) (fun u hu => by rw [Finset.mem_singleton.1 hu]; exact hyC)
        hB3 ⟨v, hvS, hvC, by rw [Finset.mem_singleton]; exact hvy'⟩ ?_
      intro c hc w hw
      rcases hcl c hc w hw with h | h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_singleton.2 h)
      · exact absurd (h ▸ hw) (hsz c hc)
  · push Not at hsy
    by_cases hsz : ∃ c ∈ C, G.Adj c z
    · refine c2_split01 hIH hsupp hdeg htw0 hK C {z} hCne hCS (by simp)
        (Finset.singleton_subset_iff.2 hzS) (fun u hu => by rw [Finset.mem_singleton.1 hu]; exact hzC)
        hB3 ⟨v, hvS, hvC, by rw [Finset.mem_singleton]; exact hvz'⟩ ?_
      intro c hc w hw
      rcases hcl c hc w hw with h | h | h
      · exact Or.inl h
      · exact absurd (h ▸ hw) (hsy c hc)
      · exact Or.inr (Finset.mem_singleton.2 h)
    · push Not at hsz
      refine c2_split01 hIH hsupp hdeg htw0 hK C ∅ hCne hCS (by simp) (Finset.empty_subset _)
        (fun u hu => absurd hu (Finset.notMem_empty u)) hB3
        ⟨v, hvS, hvC, Finset.notMem_empty v⟩ ?_
      intro c hc w hw
      rcases hcl c hc w hw with h | h | h
      · exact Or.inl h
      · exact absurd (h ▸ hw) (hsy c hc)
      · exact absurd (h ▸ hw) (hsz c hc)

end C2e

end PQL5

/-! C2 toolkit F (session 4): the reduction steps and the C2 induction. -/

namespace PQL5

open RobertsonSeymour1986.GM5

section C2f

variable {V : Type} [DecidableEq V]

/-- degree-3 step: `v` simplicial with `N(v) = {a, b, c}`. -/
theorem c2_deg3 {S : Finset V} {G : SimpleGraph V}
    (hIH : C2IH V S.card) (hsupp : ∀ x y, G.Adj x y → x ∈ S ∧ y ∈ S)
    (hdeg : ∀ u ∈ S, ∃ w1 w2, w1 ≠ w2 ∧ G.Adj u w1 ∧ G.Adj u w2)
    (htw0 : TreewidthLE G 3) (hK : ¬ IsMinor KK33 G) (h4 : 4 ≤ S.card)
    (v a b c : V) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hN : ∀ w, G.Adj v w ↔ In3 a b c w)
    (htw : TreewidthLE (G ⊔ tri a b c) 3) :
    ∃ H, G ≤ H ∧ TT H S ∧ TriCond H := by
  have hva : G.Adj v a := (hN a).2 (Or.inl rfl)
  have hvb : G.Adj v b := (hN b).2 (Or.inr (Or.inl rfl))
  have hvc : G.Adj v c := (hN c).2 (Or.inr (Or.inr rfl))
  have hvS := (hsupp v a hva).1
  have haS := (hsupp v a hva).2
  have hbS := (hsupp v b hvb).2
  have hcS := (hsupp v c hvc).2
  have hvT : ∀ x, In3 a b c x → x ≠ v := fun x hx h => G.ne_of_adj ((hN x).2 hx) h.symm
  have hmT : ∀ u, In3 a b c u → u ∈ S.erase v := by
    intro u hu
    refine Finset.mem_erase.2 ⟨hvT u hu, ?_⟩
    rcases hu with h | h | h
    · rw [h]; exact haS
    · rw [h]; exact hbS
    · rw [h]; exact hcS
  have hG''s : ∀ x w, (res G (S.erase v) ⊔ tri a b c).Adj x w →
      x ∈ S.erase v ∧ w ∈ S.erase v := by
    intro x w h
    rw [SimpleGraph.sup_adj] at h
    rcases h with h | h
    · exact ⟨(res_adj.1 h).2.1, (res_adj.1 h).2.2⟩
    · obtain ⟨h1, h2⟩ := tri_In3_of_adj h
      exact ⟨hmT x h1, hmT w h2⟩
  have hG''K : ¬ IsMinor KK33 (res G (S.erase v) ⊔ tri a b c) := by
    intro hm
    refine hK (minor_YDelta KK33 K33_triangle_free K33_no_isolated G _ v a b c hva hvb hvc ?_ hm)
    intro x w hxw
    refine ⟨(Finset.mem_erase.1 (hG''s x w hxw).1).1, ?_⟩
    rw [SimpleGraph.sup_adj] at hxw
    rcases hxw with h | h
    · exact Or.inl (res_adj.1 h).1
    · exact Or.inr (tri_In3_of_adj h)
  have hcard : (S.erase v).card = S.card - 1 := Finset.card_erase_of_mem hvS
  obtain ⟨H'', h''le, hT'', hC''⟩ := hIH (S.erase v) _ (by omega) hG''s (by omega)
    (tw_mono (sup_le_sup_right res_le _) htw) hG''K
  have hT3 : ∀ x w, In3 a b c x → In3 a b c w → x ≠ w → H''.Adj x w := by
    intro x w hx hw hxw
    exact h''le (by rw [SimpleGraph.sup_adj]; exact Or.inr (tri_adj_of_In3 hx hw hxw))
  have hab'' := hT3 a b (Or.inl rfl) (Or.inr (Or.inl rfl)) hab
  have hbc'' := hT3 b c (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) hbc
  have hac'' := hT3 a c (Or.inl rfl) (Or.inr (Or.inr rfl)) hac
  have hGres : ∀ x w, G.Adj x w → x ≠ v → w ≠ v → H''.Adj x w := by
    intro x w h hx hw
    exact h''le (by rw [SimpleGraph.sup_adj]; exact Or.inl (res_adj.2 ⟨h,
      Finset.mem_erase.2 ⟨hx, (hsupp x w h).1⟩, Finset.mem_erase.2 ⟨hw, (hsupp x w h).2⟩⟩))
  by_cases hF : Face H'' a b c
  · obtain ⟨hT, hC, -⟩ := stack_ap hT'' hC'' hF (Finset.notMem_erase v S)
    rw [Finset.insert_erase hvS] at hT
    refine ⟨_, ?_, hT, hC⟩
    intro x w hxw
    rw [SimpleGraph.sup_adj]
    by_cases hx : x = v
    · rw [hx] at hxw ⊢
      exact Or.inr (star3_adj_of_In3 (G.ne_of_adj hxw) ((hN w).1 hxw))
    · by_cases hw : w = v
      · rw [hw] at hxw ⊢
        exact Or.inr ((star3_adj_of_In3 (G.ne_of_adj hxw.symm) ((hN x).1 hxw.symm)).symm)
      · exact Or.inl (hGres x w hxw hx hw)
  · have hpq : ∃ p q, p ≠ q ∧ H''.Adj p a ∧ H''.Adj p b ∧ H''.Adj p c ∧
        H''.Adj q a ∧ H''.Adj q b ∧ H''.Adj q c := by
      by_contra hno
      exact hF ⟨hab'', hbc'', hac'', fun p q hpq e1 e2 e3 e4 e5 e6 =>
        hno ⟨p, q, hpq, e1, e2, e3, e4, e5, e6⟩⟩
    obtain ⟨p, q, hpq, hpa, hpb, hpc, hqa, hqb, hqc⟩ := hpq
    obtain ⟨x0, y0, z0, hb⟩ := hT''
    obtain ⟨P, hPp, hPq, hPcl⟩ := hb.sep a b c p q hab'' hbc'' hac'' hpq hpa hpb hpc hqa hqb hqc
    have hsupp'' := hb.supp
    obtain ⟨R, hRdef⟩ : ∃ R : Finset V, R = S \ {v, a, b, c} := ⟨_, rfl⟩
    have hmR : ∀ u, u ∈ R ↔ u ∈ S ∧ u ≠ v ∧ ¬ In3 a b c u := by
      intro u
      rw [hRdef]
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, In3]
      tauto
    have hcommon : ∀ r, H''.Adj r a → H''.Adj r b → H''.Adj r c → r ∈ R := by
      intro r hra hrb hrc
      have hr := (hsupp'' r a hra).1
      refine (hmR r).2 ⟨(Finset.mem_erase.1 hr).2, (Finset.mem_erase.1 hr).1, ?_⟩
      rintro (h | h | h)
      · exact H''.ne_of_adj hra h
      · exact H''.ne_of_adj hrb h
      · exact H''.ne_of_adj hrc h
    have hpR := hcommon p hpa hpb hpc
    have hqR := hcommon q hqa hqb hqc
    have hprop : ∀ w, reachR G R p w → P w := by
      intro w hw
      unfold reachR at hw
      induction hw with
      | refl => exact hPp
      | @tail b' c' _ hst ih =>
        obtain ⟨hadj, hb'R, hc'R⟩ := hst
        have hb' := (hmR b').1 hb'R
        have hc' := (hmR c').1 hc'R
        exact hPcl b' c' ih hb'.2.2 (hGres b' c' hadj hb'.2.1 hc'.2.1) hc'.2.2
    have hqC : q ∉ compR G R p := fun h => hPq (hprop q (compR_mem.1 h).2)
    have key : ∀ r ∈ R, ∀ x y z, (∀ w, In3 a b c w ↔ In3 x y z w) → y ≠ z →
        (∀ u ∈ compR G R r, ¬ G.Adj u x) → ∃ H, G ≤ H ∧ TT H S ∧ TriCond H := by
      intro r hr x y z hiff hyz hnx
      have hyT : In3 a b c y := (hiff y).2 (Or.inr (Or.inl rfl))
      have hzT : In3 a b c z := (hiff z).2 (Or.inr (Or.inr rfl))
      have htw' : TreewidthLE (G ⊔ tri y z z) 3 := by
        refine tw_mono (sup_le_sup_left ?_ _) htw
        intro u w h
        obtain ⟨h1, h2⟩ := tri_In3_of_adj h
        have m : ∀ t, In3 y z z t → In3 a b c t := by
          rintro t (h | h | h)
          · rw [h]; exact hyT
          · rw [h]; exact hzT
          · rw [h]; exact hzT
        exact tri_adj_of_In3 (m u h1) (m w h2) ((tri y z z).ne_of_adj h)
      have hnot : ∀ u ∈ compR G R r, u ∈ S ∧ u ≠ v ∧ ¬ In3 a b c u :=
        fun u hu => (hmR u).1 (compR_sub hu)
      refine c2_split hIH hsupp hdeg htw0 hK y z v hyz htw' ((hN y).2 hyT) ((hN z).2 hzT)
        (compR G R r) ⟨r, compR_self hr⟩ (fun u hu => (hnot u hu).1) (fun h => (hnot v h).2.1 rfl)
        (fun h => (hnot y h).2.2 hyT) (fun h => (hnot z h).2.2 hzT) (compR_conn hr) ?_
      intro u hu w huw
      have hu' := hnot u hu
      by_cases hwT : In3 a b c w
      · rcases (hiff w).1 hwT with h | h | h
        · rw [h] at huw
          exact absurd huw (hnx u hu)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · by_cases hwv : w = v
        · rw [hwv] at huw
          exact absurd ((hN u).1 huw.symm) hu'.2.2
        · exact Or.inl (compR_closed hu ((hmR w).2 ⟨(hsupp u w huw).2, hwv, hwT⟩) huw)
    have disp : ∀ r ∈ R, ∀ x, In3 a b c x → (∀ u ∈ compR G R r, ¬ G.Adj u x) →
        ∃ H, G ≤ H ∧ TT H S ∧ TriCond H := by
      intro r hr x hx hnx
      rcases hx with h | h | h
      · rw [h] at hnx
        exact key r hr a b c (fun w => Iff.rfl) hbc hnx
      · rw [h] at hnx
        exact key r hr b a c (fun w => by unfold In3; tauto) hac hnx
      · rw [h] at hnx
        exact key r hr c a b (fun w => by unfold In3; tauto) hab hnx
    by_cases hpall : ∀ x, In3 a b c x → ∃ u ∈ compR G R p, G.Adj u x
    · by_cases hqall : ∀ x, In3 a b c x → ∃ u ∈ compR G R q, G.Adj u x
      · exfalso
        apply hK
        have sees : ∀ r, (∀ x, In3 a b c x → ∃ u ∈ compR G R r, G.Adj u x) →
            (∃ x ∈ (↑(compR G R r) : Set V), G.Adj a x) ∧
            (∃ x ∈ (↑(compR G R r) : Set V), G.Adj b x) ∧
            (∃ x ∈ (↑(compR G R r) : Set V), G.Adj c x) := by
          intro r hr
          obtain ⟨u1, hu1, e1⟩ := hr a (Or.inl rfl)
          obtain ⟨u2, hu2, e2⟩ := hr b (Or.inr (Or.inl rfl))
          obtain ⟨u3, hu3, e3⟩ := hr c (Or.inr (Or.inr rfl))
          exact ⟨⟨u1, hu1, e1.symm⟩, ⟨u2, hu2, e2.symm⟩, ⟨u3, hu3, e3.symm⟩⟩
        have notin : ∀ r, ∀ x, In3 a b c x → x ∉ (↑(compR G R r) : Set V) := by
          intro r x hx h
          exact ((hmR x).1 (compR_sub h)).2.2 hx
        have vnot : ∀ r, v ∉ (↑(compR G R r) : Set V) :=
          fun r h => ((hmR v).1 (compR_sub h)).2.1 rfl
        exact K33_of_three' G a b c hab hbc hac {v} _ _
          ⟨Set.singleton_nonempty v, induce_singleton_conn G v⟩
          ⟨⟨p, compR_self hpR⟩, compR_conn hpR⟩ ⟨⟨q, compR_self hqR⟩, compR_conn hqR⟩
          (Set.disjoint_singleton_left.2 (vnot p)) (Set.disjoint_singleton_left.2 (vnot q))
          (Set.disjoint_left.2 (fun w hwp hwq => compR_disj hqR hqC hwp hwq))
          ⟨fun h => hvT a (Or.inl rfl) h, fun h => hvT b (Or.inr (Or.inl rfl)) h,
            fun h => hvT c (Or.inr (Or.inr rfl)) h⟩
          ⟨notin p a (Or.inl rfl), notin p b (Or.inr (Or.inl rfl)), notin p c (Or.inr (Or.inr rfl))⟩
          ⟨notin q a (Or.inl rfl), notin q b (Or.inr (Or.inl rfl)), notin q c (Or.inr (Or.inr rfl))⟩
          ⟨⟨v, Set.mem_singleton v, hva.symm⟩, ⟨v, Set.mem_singleton v, hvb.symm⟩,
            ⟨v, Set.mem_singleton v, hvc.symm⟩⟩ (sees p hpall) (sees q hqall)
      · push Not at hqall
        obtain ⟨x, hx, hnx⟩ := hqall
        exact disp q hqR x hx hnx
    · push Not at hpall
      obtain ⟨x, hx, hnx⟩ := hpall
      exact disp p hpR x hx hnx

/-- degree-2 step: `v` simplicial with `N(v) = {s, t}`. -/
theorem c2_deg2 {S : Finset V} {G : SimpleGraph V}
    (hIH : C2IH V S.card) (hsupp : ∀ x y, G.Adj x y → x ∈ S ∧ y ∈ S)
    (hK : ¬ IsMinor KK33 G) (h4 : 4 ≤ S.card)
    (v s t : V) (hst : s ≠ t) (hN : ∀ w, G.Adj v w ↔ w = s ∨ w = t)
    (htw : TreewidthLE (G ⊔ tri s t t) 3) :
    ∃ H, G ≤ H ∧ TT H S ∧ TriCond H := by
  have hvs : G.Adj v s := (hN s).2 (Or.inl rfl)
  have hvt : G.Adj v t := (hN t).2 (Or.inr rfl)
  have hvS := (hsupp v s hvs).1
  have hsS := (hsupp v s hvs).2
  have htS := (hsupp v t hvt).2
  have hmT : ∀ u, In3 s t t u → u ∈ S.erase v := by
    intro u hu
    rcases hu with h | h | h
    · rw [h]; exact Finset.mem_erase.2 ⟨(G.ne_of_adj hvs).symm, hsS⟩
    · rw [h]; exact Finset.mem_erase.2 ⟨(G.ne_of_adj hvt).symm, htS⟩
    · rw [h]; exact Finset.mem_erase.2 ⟨(G.ne_of_adj hvt).symm, htS⟩
  have hG''s : ∀ x w, (res G (S.erase v) ⊔ tri s t t).Adj x w →
      x ∈ S.erase v ∧ w ∈ S.erase v := by
    intro x w h
    rw [SimpleGraph.sup_adj] at h
    rcases h with h | h
    · exact ⟨(res_adj.1 h).2.1, (res_adj.1 h).2.2⟩
    · obtain ⟨h1, h2⟩ := tri_In3_of_adj h
      exact ⟨hmT x h1, hmT w h2⟩
  have hG''K : ¬ IsMinor KK33 (res G (S.erase v) ⊔ tri s t t) := by
    intro hm
    refine hK (minor_YDelta KK33 K33_triangle_free K33_no_isolated G _ v s t t hvs hvt hvt ?_ hm)
    intro x w hxw
    refine ⟨(Finset.mem_erase.1 (hG''s x w hxw).1).1, ?_⟩
    rw [SimpleGraph.sup_adj] at hxw
    rcases hxw with h | h
    · exact Or.inl (res_adj.1 h).1
    · exact Or.inr (tri_In3_of_adj h)
  have hcard : (S.erase v).card = S.card - 1 := Finset.card_erase_of_mem hvS
  obtain ⟨H'', h''le, hT'', hC''⟩ := hIH (S.erase v) _ (by omega) hG''s (by omega)
    (tw_mono (sup_le_sup_right res_le _) htw) hG''K
  have hst'' : H''.Adj s t := h''le (by
    rw [SimpleGraph.sup_adj]
    exact Or.inr (tri_adj_of_In3 (Or.inl rfl) (Or.inr (Or.inl rfl)) hst))
  obtain ⟨x0, y0, z0, hb⟩ := hT''
  obtain ⟨r, hF⟩ := hb.edge_face s t hst''
  obtain ⟨hT, hC, -⟩ := stack_ap ⟨x0, y0, z0, hb⟩ hC'' hF (Finset.notMem_erase v S)
  rw [Finset.insert_erase hvS] at hT
  refine ⟨_, ?_, hT, hC⟩
  have hin : ∀ w, G.Adj v w → In3 s t r w := by
    intro w hw
    rcases (hN w).1 hw with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  intro x w hxw
  rw [SimpleGraph.sup_adj]
  by_cases hx : x = v
  · rw [hx] at hxw ⊢
    exact Or.inr (star3_adj_of_In3 (G.ne_of_adj hxw) (hin w hxw))
  · by_cases hw : w = v
    · rw [hw] at hxw ⊢
      exact Or.inr ((star3_adj_of_In3 (G.ne_of_adj hxw.symm) (hin x hxw.symm)).symm)
    · exact Or.inl (h''le (by rw [SimpleGraph.sup_adj]; exact Or.inl (res_adj.2 ⟨hxw,
        Finset.mem_erase.2 ⟨hx, (hsupp x w hxw).1⟩, Finset.mem_erase.2 ⟨hw, (hsupp x w hxw).2⟩⟩)))

/-- degree-at-most-1 step at any vertex `u`. -/
theorem c2_low {S : Finset V} {G : SimpleGraph V}
    (hIH : C2IH V S.card) (hsupp : ∀ x y, G.Adj x y → x ∈ S ∧ y ∈ S)
    (htw0 : TreewidthLE G 3) (hK : ¬ IsMinor KK33 G) (h4 : 4 ≤ S.card)
    (u : V) (huS : u ∈ S) (hlow : ∀ w1 w2, G.Adj u w1 → G.Adj u w2 → w1 = w2) :
    ∃ H, G ≤ H ∧ TT H S ∧ TriCond H := by
  have hcard : (S.erase u).card = S.card - 1 := Finset.card_erase_of_mem huS
  obtain ⟨H', h'le, hT', hC'⟩ := hIH (S.erase u) (res G (S.erase u)) (by omega)
    (fun x y h => ⟨(res_adj.1 h).2.1, (res_adj.1 h).2.2⟩) (by omega)
    (tw_mono res_le htw0) (fun h => hK (minor_of_le res_le h))
  obtain ⟨s, hs, hsn⟩ : ∃ s ∈ S.erase u, ∀ w, G.Adj u w → w = s := by
    by_cases hn : ∃ w, G.Adj u w
    · obtain ⟨w, hw⟩ := hn
      exact ⟨w, Finset.mem_erase.2 ⟨(G.ne_of_adj hw).symm, (hsupp u w hw).2⟩,
        fun w' hw' => hlow w' w hw' hw⟩
    · push Not at hn
      obtain ⟨s, hs⟩ : (S.erase u).Nonempty := Finset.card_pos.1 (by omega)
      exact ⟨s, hs, fun w hw => absurd hw (hn w)⟩
  obtain ⟨x0, y0, z0, hb⟩ := hT'
  obtain ⟨w, t, hF⟩ := hb.vertex_face s hs
  obtain ⟨hT, hC, -⟩ := stack_ap ⟨x0, y0, z0, hb⟩ hC' hF (Finset.notMem_erase u S)
  rw [Finset.insert_erase huS] at hT
  refine ⟨_, ?_, hT, hC⟩
  intro x y hxy
  rw [SimpleGraph.sup_adj]
  by_cases hx : x = u
  · rw [hx] at hxy ⊢
    have e := hsn y hxy
    rw [e] at hxy ⊢
    exact Or.inr (star3_adj_of_In3 (G.ne_of_adj hxy) (Or.inl rfl))
  · by_cases hy : y = u
    · rw [hy] at hxy ⊢
      have e := hsn x hxy.symm
      rw [e] at hxy ⊢
      exact Or.inr (star3_adj_of_In3 (G.ne_of_adj hxy.symm) (Or.inl rfl)).symm
    · exact Or.inl (h'le (res_adj.2 ⟨hxy, Finset.mem_erase.2 ⟨hx, (hsupp x y hxy).1⟩,
        Finset.mem_erase.2 ⟨hy, (hsupp x y hxy).2⟩⟩))

end C2f

/-- **C2** by strong induction on `|S|`. -/
theorem c2_main : ∀ (n : ℕ) {V : Type} [DecidableEq V] (S : Finset V) (G : SimpleGraph V),
    S.card = n → (∀ x y, G.Adj x y → x ∈ S ∧ y ∈ S) → 3 ≤ S.card → TreewidthLE G 3 →
    ¬ IsMinor KK33 G → ∃ H, G ≤ H ∧ TT H S ∧ TriCond H := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ S G hn hsupp h3 htw hK
  have hIH : C2IH V S.card := by
    intro S' G' hlt hs' h3' htw' hK'
    exact ih S'.card (hn ▸ hlt) S' G' rfl hs' h3' htw' hK'
  by_cases h5 : S.card ≤ 5
  · obtain ⟨H, hle, hT⟩ := c1_tw hsupp h3 htw
    obtain ⟨x0, y0, z0, hb⟩ := hT
    exact ⟨H, hle, ⟨x0, y0, z0, hb⟩, triCond_small hb.supp h5⟩
  by_cases hlow : ∃ u ∈ S, ∀ w1 w2, G.Adj u w1 → G.Adj u w2 → w1 = w2
  · obtain ⟨u, hu, hl⟩ := hlow
    exact c2_low hIH hsupp htw hK (by omega) u hu hl
  push Not at hlow
  have hdeg : ∀ u ∈ S, ∃ w1 w2, w1 ≠ w2 ∧ G.Adj u w1 ∧ G.Adj u w2 := by
    intro u hu
    obtain ⟨w1, w2, h1, h2, h12⟩ := hlow u hu
    exact ⟨w1, w2, h12, h1, h2⟩
  obtain ⟨T, hTf, t, X, htd, hw⟩ := htw
  have htd0 := htd
  obtain ⟨htree, hcov, hedge, hpath⟩ := htd
  haveI : DecidableEq T := Classical.decEq T
  have hp2 : PathProp t (fun s => X s ∩ S) := by
    intro s s' s'' p hp hs' u hu
    rw [Finset.mem_inter, Finset.mem_inter, Finset.mem_inter] at *
    exact ⟨hpath s s' s'' p hp hs' (Finset.mem_inter.2 ⟨hu.1.1, hu.2.1⟩), hu.1.2⟩
  have hne : ∃ s, (X s ∩ S).Nonempty := by
    obtain ⟨u0, hu0⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨s, hs⟩ := hcov u0
    exact ⟨s, u0, Finset.mem_inter.2 ⟨hs, hu0⟩⟩
  obtain ⟨v, s0, hv0, hsimp⟩ := exists_simplicial t htree.isConnected htree.IsAcyclic
    (fun s => X s ∩ S) hp2 hne
  have hvS : v ∈ S := (Finset.mem_inter.1 hv0).2
  have hNB : ∀ w, G.Adj v w → w ∈ (X s0 ∩ S).erase v := by
    intro w hvw
    obtain ⟨s, hvs, hws⟩ := hedge v w hvw
    have hsub := hsimp s (Finset.mem_inter.2 ⟨hvs, hvS⟩)
    exact Finset.mem_erase.2 ⟨(G.ne_of_adj hvw).symm,
      hsub (Finset.mem_inter.2 ⟨hws, (hsupp v w hvw).2⟩)⟩
  have hBX : ∀ w, w ∈ (X s0 ∩ S).erase v → w ∈ X s0 :=
    fun w h => (Finset.mem_inter.1 (Finset.mem_erase.1 h).2).1
  have hB3 : ((X s0 ∩ S).erase v).card ≤ 3 := by
    have h1 := Finset.card_erase_of_mem hv0
    have h2 : (X s0 ∩ S).card ≤ (X s0).card := Finset.card_le_card Finset.inter_subset_left
    have h3 := hw s0
    omega
  have twtri : ∀ a b c, a ∈ X s0 → b ∈ X s0 → c ∈ X s0 → TreewidthLE (G ⊔ tri a b c) 3 := by
    intro a b c ha hb hc
    refine tw_transfer htd0 hw (fun x y h => ?_)
    rw [SimpleGraph.sup_adj] at h
    rcases h with h | h
    · exact Or.inl h
    · obtain ⟨h1, h2⟩ := tri_In3_of_adj h
      have m : ∀ u, In3 a b c u → u ∈ X s0 := by
        rintro u (e | e | e)
        · rw [e]; exact ha
        · rw [e]; exact hb
        · rw [e]; exact hc
      exact Or.inr ⟨s0, m x h1, m y h2⟩
  obtain ⟨w1, w2, h12, hv1, hv2⟩ := hdeg v hvS
  have hm1 := hNB w1 hv1
  have hm2 := hNB w2 hv2
  by_cases hall : ∀ w ∈ (X s0 ∩ S).erase v, G.Adj v w
  · have hc2 : 2 ≤ ((X s0 ∩ S).erase v).card := by
      have : 1 < ((X s0 ∩ S).erase v).card := Finset.one_lt_card.2 ⟨w1, hm1, w2, hm2, h12⟩
      omega
    by_cases hc3 : ((X s0 ∩ S).erase v).card = 3
    · obtain ⟨a, b, c, hab, hac, hbc, hE⟩ := Finset.card_eq_three.1 hc3
      have hN : ∀ w, G.Adj v w ↔ In3 a b c w := by
        intro w
        constructor
        · intro h
          have := hNB w h
          rw [hE] at this
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          exact this
        · intro h
          apply hall
          rw [hE]
          simp only [Finset.mem_insert, Finset.mem_singleton]
          exact h
      have hmem : ∀ x, In3 a b c x → x ∈ X s0 := by
        intro x hx
        apply hBX
        rw [hE]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact hx
      exact c2_deg3 hIH hsupp hdeg ⟨T, hTf, t, X, htd0, hw⟩ hK (by omega) v a b c hab hbc hac hN
        (twtri a b c (hmem a (Or.inl rfl)) (hmem b (Or.inr (Or.inl rfl)))
          (hmem c (Or.inr (Or.inr rfl))))
    · have hc2' : ((X s0 ∩ S).erase v).card = 2 := by omega
      obtain ⟨a, b, hab, hE⟩ := Finset.card_eq_two.1 hc2'
      have hN : ∀ w, G.Adj v w ↔ w = a ∨ w = b := by
        intro w
        constructor
        · intro h
          have := hNB w h
          rw [hE] at this
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          exact this
        · intro h
          apply hall
          rw [hE]
          simp only [Finset.mem_insert, Finset.mem_singleton]
          exact h
      have ha : a ∈ X s0 := hBX a (by rw [hE]; simp)
      have hb : b ∈ X s0 := hBX b (by rw [hE]; simp)
      exact c2_deg2 hIH hsupp hK (by omega) v a b hab hN (twtri a b b ha hb hb)
  · push Not at hall
    obtain ⟨b0, hb0, hnb0⟩ := hall
    have hN : ∀ w, G.Adj v w ↔ w = w1 ∨ w = w2 := by
      intro w
      constructor
      · intro h
        by_contra hne'
        push Not at hne'
        have m : ∀ x, G.Adj v x → x ∈ ((X s0 ∩ S).erase v).erase b0 := by
          intro x hx
          exact Finset.mem_erase.2 ⟨fun e => hnb0 (e ▸ hx), hNB x hx⟩
        have h3' := three_le_card (m w h) (m w1 hv1) (m w2 hv2) hne'.1 hne'.2 h12
        have := Finset.card_erase_of_mem hb0
        omega
      · rintro (h | h)
        · rw [h]; exact hv1
        · rw [h]; exact hv2
    exact c2_deg2 hIH hsupp hK (by omega) v w1 w2 h12 hN
      (twtri w1 w2 w2 (hBX w1 hm1) (hBX w2 hm2) (hBX w2 hm2))

theorem childC2_holds : ChildC2 := by
  intro V _ _ S G hsupp h3 htw hK
  exact c2_main _ S G rfl hsupp h3 htw hK

end PQL5

/-! C3 part A (session 4): abstract assembly of the 5-queue layout (Alam et al., levels + bags). -/

namespace PQL5

open PlanarQueue.Planar

section C3a

variable {V B : Type}

/-- the queue of the ordered pair `x y`: level edges `q0`, binding edges `2 + role`. -/
noncomputable def asmQ (l : V → ℕ) (bag : V → B) (role : V → V → ℕ) (q0 : V → V → ℕ)
    (x y : V) : ℕ := by
  classical
  exact if bag x = bag y then q0 x y else if l x < l y then 2 + role x y
    else if l y < l x then 2 + role y x else 0

theorem asmQ_symm (l : V → ℕ) (bag : V → B) (role : V → V → ℕ) (q0 : V → V → ℕ)
    (hq0s : ∀ x y, q0 x y = q0 y x) (x y : V) :
    asmQ l bag role q0 x y = asmQ l bag role q0 y x := by
  classical
  unfold asmQ
  by_cases h : bag x = bag y
  · rw [if_pos h, if_pos h.symm, hq0s]
  · rw [if_neg h, if_neg (Ne.symm h)]
    by_cases h1 : l x < l y
    · rw [if_pos h1, if_neg (show ¬ l y < l x by omega), if_pos h1]
    · by_cases h2 : l y < l x
      · rw [if_neg h1, if_pos h2, if_pos h2]
      · rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1]

theorem asmQ_le (l : V → ℕ) (bag : V → B) (role : V → V → ℕ) (q0 : V → V → ℕ)
    (hq0 : ∀ x y, q0 x y < 2) (hrole : ∀ x y, role x y < 3) (x y : V) :
    asmQ l bag role q0 x y ≤ 4 := by
  classical
  unfold asmQ
  have := hq0 x y
  have := hrole x y
  have := hrole y x
  split_ifs <;> omega

/-- **Assembly (C3a).** Levels `l`, bags (contiguous, ordered by level), level edges inside a bag
coloured by `q0` without nesting, binding edges from a vertex `y` to vertex `role` of the attachment
triangle `t (bag y)` one level up, and attachment triangles forming a coordinatewise chain in the
order of the bags give a 5-queue layout. -/
theorem assembly5 (H : SimpleGraph V) (ord : V → ℕ) (hinj : Function.Injective ord)
    (l : V → ℕ) (bag : V → B) (t : B → ℕ → V) (role : V → V → ℕ) (q0 : V → V → ℕ)
    (hq0s : ∀ x y, q0 x y = q0 y x) (hq0 : ∀ x y, q0 x y < 2) (hrole : ∀ x y, role x y < 3)
    (hedge : ∀ x y, H.Adj x y → bag x ≠ bag y →
      (l y = l x + 1 ∧ x = t (bag y) (role x y)) ∨ (l x = l y + 1 ∧ y = t (bag x) (role y x)))
    (hlev : ∀ u v, l u < l v → ord u < ord v)
    (hcont : ∀ u u' v v', bag u = bag u' → bag v = bag v' → bag u ≠ bag v → l u = l v →
      ord u < ord v → ord u' < ord v')
    (hbagl : ∀ u v, bag u = bag v → l u = l v)
    (hchain : ∀ u v, l u = l v → bag u ≠ bag v → ord u < ord v → ∀ j,
      ord (t (bag u) j) ≤ ord (t (bag v) j))
    (hin : ∀ a b c d, H.Adj a d → H.Adj b c → bag a = bag d → bag b = bag c → bag a = bag b →
      q0 a d = q0 b c → ord a < ord b → ord b < ord c → ord c < ord d → False) :
    HasQueueLayout H 5 := by
  classical
  set Q := asmQ l bag role q0 with hQdef
  have hQs : ∀ x y, Q x y = Q y x := asmQ_symm l bag role q0 hq0s
  have hQle : ∀ x y, Q x y ≤ 4 := asmQ_le l bag role q0 hq0 hrole
  -- the core: no two edges with equal `Q` nest
  have core : ∀ a b c d, H.Adj a d → H.Adj b c → Q a d = Q b c → ord a < ord b →
      ord b < ord c → ord c < ord d → False := by
    intro a b c d had hbc hQ h1 h2 h3
    have hlv : ∀ u v, ord u < ord v → l u ≤ l v := by
      intro u v h
      by_contra hc
      have := hlev v u (by omega)
      omega
    by_cases had' : bag a = bag d
    · by_cases hbc' : bag b = bag c
      · have e1 : Q a d = q0 a d := by rw [hQdef]; unfold asmQ; rw [if_pos had']
        have e2 : Q b c = q0 b c := by rw [hQdef]; unfold asmQ; rw [if_pos hbc']
        by_cases hab : bag a = bag b
        · exact hin a b c d had hbc had' hbc' hab (by rw [← e1, ← e2]; exact hQ) h1 h2 h3
        · have la := hbagl a d had'
          have lb := hbagl b c hbc'
          have lab := hlv a b h1
          have lcd := hlv c d h3
          have hle : l a = l b := by omega
          have := hcont a d b c had' hbc' hab hle h1
          omega
      · have e1 : Q a d = q0 a d := by rw [hQdef]; unfold asmQ; rw [if_pos had']
        have hb := hq0 a d
        rcases hedge b c hbc hbc' with ⟨hl, _⟩ | ⟨hl, _⟩
        · have e2 : Q b c = 2 + role b c := by
            rw [hQdef]; unfold asmQ; rw [if_neg hbc', if_pos (show l b < l c by omega)]
          omega
        · have := hlev c b (by omega)
          omega
    · rcases hedge a d had had' with ⟨hl1, ht1⟩ | ⟨hl1, _⟩
      · have e1 : Q a d = 2 + role a d := by
          rw [hQdef]; unfold asmQ; rw [if_neg had', if_pos (show l a < l d by omega)]
        by_cases hbc' : bag b = bag c
        · have e2 : Q b c = q0 b c := by rw [hQdef]; unfold asmQ; rw [if_pos hbc']
          have := hq0 b c
          omega
        · rcases hedge b c hbc hbc' with ⟨hl2, ht2⟩ | ⟨hl2, _⟩
          · have e2 : Q b c = 2 + role b c := by
              rw [hQdef]; unfold asmQ; rw [if_neg hbc', if_pos (show l b < l c by omega)]
            have hr : role a d = role b c := by omega
            have lab := hlv a b h1
            have lcd := hlv c d h3
            have hcd : l c = l d := by omega
            by_cases hcd' : bag c = bag d
            · have : a = b := by rw [ht1, ht2, hr, hcd']
              rw [this] at h1
              omega
            · have := hchain c d hcd hcd' h3 (role a d)
              rw [← ht1, hr, ← ht2] at this
              omega
          · have := hlev c b (by omega)
            omega
      · have := hlev d a (by omega)
        omega
  refine ⟨ord, fun e => ⟨min (Sym2.lift ⟨Q, hQs⟩ e.1) 4, by omega⟩, hinj, ?_⟩
  intro e f hq hn
  obtain ⟨a, b, c, d, hcase, h1, h2, h3⟩ := hn
  have hmin : ∀ x y, min (Q x y) 4 = Q x y := fun x y => min_eq_left (hQle x y)
  rcases hcase with ⟨he, hf⟩ | ⟨he, hf⟩
  · have had : H.Adj a d := by
      have := e.2; rw [he, SimpleGraph.mem_edgeSet] at this; exact this
    have hbc : H.Adj b c := by
      have := f.2; rw [hf, SimpleGraph.mem_edgeSet] at this; exact this
    have hq' := congrArg Fin.val hq
    simp only [he, hf, Sym2.lift_mk, hmin, Fin.val_mk] at hq'
    exact core a b c d had hbc hq' h1 h2 h3
  · have had : H.Adj a d := by
      have := f.2; rw [hf, SimpleGraph.mem_edgeSet] at this; exact this
    have hbc : H.Adj b c := by
      have := e.2; rw [he, SimpleGraph.mem_edgeSet] at this; exact this
    have hq' := congrArg Fin.val hq
    simp only [he, hf, Sym2.lift_mk, hmin, Fin.val_mk] at hq'
    exact core a b c d had hbc hq'.symm h1 h2 h3

end C3a

end PQL5

/-! C3 part L (session 5): Apollonian region trees and the bag layout (DPW04 Lemma 22 rows,
in-order x-coordinates). See scratch/decomp/1576ebc4.plan.md "session 5". -/

namespace PQL5

/-- Apollonian region tree: `nd v t1 t2 t3` placed in the region `(a,b,c)` stacks `v` there;
its children live in the regions `(a,b,v)`, `(b,c,v)`, `(c,a,v)`. -/
inductive RT (V : Type) where
  | lf : RT V
  | nd : V → RT V → RT V → RT V → RT V

section RTbasic

variable {V : Type} [DecidableEq V]

/-- the stacked vertices of a region tree -/
def RT.vs : RT V → Finset V
  | .lf => ∅
  | .nd v t1 t2 t3 => insert v (t1.vs ∪ t2.vs ∪ t3.vs)

/-- the edges created inside the region `(a,b,c)` -/
def RT.gr : RT V → V → V → V → SimpleGraph V
  | .lf, _, _, _ => ⊥
  | .nd v t1 t2 t3, a, b, c => star3 v a b c ⊔ t1.gr a b v ⊔ t2.gr b c v ⊔ t3.gr c a v

/-- labels are distinct and avoid the region boundary -/
def RT.wf : RT V → V → V → V → Prop
  | .lf, a, b, c => a ≠ b ∧ b ≠ c ∧ a ≠ c
  | .nd v t1 t2 t3, a, b, c => a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ v ≠ a ∧ v ≠ b ∧ v ≠ c ∧
      t1.wf a b v ∧ t2.wf b c v ∧ t3.wf c a v ∧ c ∉ t1.vs ∧ a ∉ t2.vs ∧ b ∉ t3.vs ∧
      Disjoint t1.vs t2.vs ∧ Disjoint t1.vs t3.vs ∧ Disjoint t2.vs t3.vs

theorem RT.vs_nd {v : V} {t1 t2 t3 : RT V} {z : V} :
    z ∈ (RT.nd v t1 t2 t3).vs ↔ z = v ∨ z ∈ t1.vs ∨ z ∈ t2.vs ∨ z ∈ t3.vs := by
  simp [RT.vs]

theorem RT.wf_ne {T : RT V} {a b c : V} (h : T.wf a b c) : a ≠ b ∧ b ≠ c ∧ a ≠ c := by
  cases T with
  | lf => exact h
  | nd v t1 t2 t3 => exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem RT.wf_out {T : RT V} {a b c : V} (h : T.wf a b c) :
    a ∉ T.vs ∧ b ∉ T.vs ∧ c ∉ T.vs := by
  induction T generalizing a b c with
  | lf => simp [RT.vs]
  | nd v t1 t2 t3 ih1 ih2 ih3 =>
    obtain ⟨_, _, _, hva, hvb, hvc, h1, h2, h3, hc1, ha2, hb3, _, _, _⟩ := h
    have o1 := ih1 h1
    have o2 := ih2 h2
    have o3 := ih3 h3
    simp only [RT.vs_nd, not_or]
    exact ⟨⟨fun e => hva e.symm, o1.1, ha2, o3.2.1⟩, ⟨fun e => hvb e.symm, o1.2.1, o2.1, hb3⟩,
      ⟨fun e => hvc e.symm, hc1, o2.2.1, o3.1⟩⟩

/-- every edge created in a region has an endpoint inside and the other inside or on the boundary -/
theorem RT.gr_ends {T : RT V} {a b c x y : V} (h : (T.gr a b c).Adj x y) :
    (x ∈ T.vs ∨ x = a ∨ x = b ∨ x = c) ∧ (y ∈ T.vs ∨ y = a ∨ y = b ∨ y = c) ∧
      (x ∈ T.vs ∨ y ∈ T.vs) := by
  induction T generalizing a b c x y with
  | lf => exact absurd h (by simp [RT.gr])
  | nd v t1 t2 t3 ih1 ih2 ih3 =>
    simp only [RT.gr, SimpleGraph.sup_adj] at h
    simp only [RT.vs_nd]
    have hv : v = v ∨ v ∈ t1.vs ∨ v ∈ t2.vs ∨ v ∈ t3.vs := Or.inl rfl
    rcases h with ((h | h) | h) | h
    · rw [star3_adj] at h
      obtain ⟨_, h⟩ := h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        subst h1 h2
      · exact ⟨Or.inl hv, Or.inr (Or.inl rfl), Or.inl hv⟩
      · exact ⟨Or.inr (Or.inl rfl), Or.inl hv, Or.inr hv⟩
      · exact ⟨Or.inl hv, Or.inr (Or.inr (Or.inl rfl)), Or.inl hv⟩
      · exact ⟨Or.inr (Or.inr (Or.inl rfl)), Or.inl hv, Or.inr hv⟩
      · exact ⟨Or.inl hv, Or.inr (Or.inr (Or.inr rfl)), Or.inl hv⟩
      · exact ⟨Or.inr (Or.inr (Or.inr rfl)), Or.inl hv, Or.inr hv⟩
    · obtain ⟨hx, hy, hxy⟩ := ih1 h
      have L : ∀ z, (z ∈ t1.vs ∨ z = a ∨ z = b ∨ z = v) →
          ((z = v ∨ z ∈ t1.vs ∨ z ∈ t2.vs ∨ z ∈ t3.vs) ∨ z = a ∨ z = b ∨ z = c) := by
        intro z hz
        rcases hz with hz | hz | hz | hz
        exacts [Or.inl (Or.inr (Or.inl hz)), Or.inr (Or.inl hz), Or.inr (Or.inr (Or.inl hz)),
          Or.inl (Or.inl hz)]
      refine ⟨L x hx, L y hy, ?_⟩
      rcases hxy with hz | hz
      exacts [Or.inl (Or.inr (Or.inl hz)), Or.inr (Or.inr (Or.inl hz))]
    · obtain ⟨hx, hy, hxy⟩ := ih2 h
      have L : ∀ z, (z ∈ t2.vs ∨ z = b ∨ z = c ∨ z = v) →
          ((z = v ∨ z ∈ t1.vs ∨ z ∈ t2.vs ∨ z ∈ t3.vs) ∨ z = a ∨ z = b ∨ z = c) := by
        intro z hz
        rcases hz with hz | hz | hz | hz
        exacts [Or.inl (Or.inr (Or.inr (Or.inl hz))), Or.inr (Or.inr (Or.inl hz)),
          Or.inr (Or.inr (Or.inr hz)), Or.inl (Or.inl hz)]
      refine ⟨L x hx, L y hy, ?_⟩
      rcases hxy with hz | hz
      exacts [Or.inl (Or.inr (Or.inr (Or.inl hz))), Or.inr (Or.inr (Or.inr (Or.inl hz)))]
    · obtain ⟨hx, hy, hxy⟩ := ih3 h
      have L : ∀ z, (z ∈ t3.vs ∨ z = c ∨ z = a ∨ z = v) →
          ((z = v ∨ z ∈ t1.vs ∨ z ∈ t2.vs ∨ z ∈ t3.vs) ∨ z = a ∨ z = b ∨ z = c) := by
        intro z hz
        rcases hz with hz | hz | hz | hz
        exacts [Or.inl (Or.inr (Or.inr (Or.inr hz))), Or.inr (Or.inr (Or.inr hz)),
          Or.inr (Or.inl hz), Or.inl (Or.inl hz)]
      refine ⟨L x hx, L y hy, ?_⟩
      rcases hxy with hz | hz
      exacts [Or.inl (Or.inr (Or.inr (Or.inr hz))), Or.inr (Or.inr (Or.inr (Or.inr hz)))]

end RTbasic

end PQL5


/-! C3b: an Apollonian 3-tree is the graph of a region tree over one of its faces. -/

namespace PQL5

section C3b

variable {V : Type} [DecidableEq V]

/-- the graph of a region tree together with its boundary triangle -/
def GT (T : RT V) (a b c : V) : SimpleGraph V := tri a b c ⊔ T.gr a b c

theorem star3_adj' {v p q r u w : V} : (star3 v p q r).Adj u w ↔ u ≠ w ∧
    ((u = v ∧ In3 p q r w) ∨ (w = v ∧ In3 p q r u)) := by
  rw [star3_adj]; unfold In3; tauto

theorem star3_eq_of_cover {v p q r a b c : V} (h : ∀ u, In3 p q r u ↔ In3 a b c u) :
    star3 v p q r = star3 v a b c := by
  ext u w
  simp only [star3_adj', h]

theorem GT_ends {T : RT V} {a b c u u' : V} (h : (GT T a b c).Adj u u') :
    u ∈ T.vs ∨ In3 a b c u := by
  unfold GT at h
  rw [SimpleGraph.sup_adj] at h
  rcases h with h | h
  · exact Or.inr (tri_In3_of_adj h).1
  · rcases (RT.gr_ends h).1 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1

theorem gt_nd_adj {w : V} {t1 t2 t3 : RT V} {a b c u u' : V} :
    (GT (.nd w t1 t2 t3) a b c).Adj u u' ↔ (tri a b c).Adj u u' ∨ (star3 w a b c).Adj u u' ∨
      (t1.gr a b w).Adj u u' ∨ (t2.gr b c w).Adj u u' ∨ (t3.gr c a w).Adj u u' := by
  simp only [GT, RT.gr, SimpleGraph.sup_adj]
  tauto

theorem vs_ins1 (v w : V) (A B C : Finset V) :
    insert w (insert v A ∪ B ∪ C) = insert v (insert w (A ∪ B ∪ C)) := by
  ext z; simp only [Finset.mem_insert, Finset.mem_union]; tauto

theorem vs_ins2 (v w : V) (A B C : Finset V) :
    insert w (A ∪ insert v B ∪ C) = insert v (insert w (A ∪ B ∪ C)) := by
  ext z; simp only [Finset.mem_insert, Finset.mem_union]; tauto

theorem vs_ins3 (v w : V) (A B C : Finset V) :
    insert w (A ∪ B ∪ insert v C) = insert v (insert w (A ∪ B ∪ C)) := by
  ext z; simp only [Finset.mem_insert, Finset.mem_union]; tauto

omit [DecidableEq V] in
theorem gr_ins1 (A B C D X : SimpleGraph V) : A ⊔ (B ⊔ X) ⊔ C ⊔ D = A ⊔ B ⊔ C ⊔ D ⊔ X := by
  ext u w; simp only [SimpleGraph.sup_adj]; tauto

omit [DecidableEq V] in
theorem gr_ins2 (A B C D X : SimpleGraph V) : A ⊔ B ⊔ (C ⊔ X) ⊔ D = A ⊔ B ⊔ C ⊔ D ⊔ X := by
  ext u w; simp only [SimpleGraph.sup_adj]; tauto

omit [DecidableEq V] in
theorem gr_ins3 (A B C D X : SimpleGraph V) : A ⊔ B ⊔ C ⊔ (D ⊔ X) = A ⊔ B ⊔ C ⊔ D ⊔ X := by
  ext u w; simp only [SimpleGraph.sup_adj]; tauto

/-- the conclusion of the triangle-region lemma -/
def TRC (T : RT V) (a b c p q r : V) : Prop :=
  (∀ v, v ∉ T.vs → v ≠ a → v ≠ b → v ≠ c → ∃ T' : RT V, T'.wf a b c ∧
      T'.vs = insert v T.vs ∧ T'.gr a b c = T.gr a b c ⊔ star3 v p q r) ∨
  (∃ w ∈ T.vs, In3 a b c p ∧ In3 a b c q ∧ In3 a b c r ∧ (GT T a b c).Adj w p ∧
      (GT T a b c).Adj w q ∧ (GT T a b c).Adj w r) ∨
  (∃ w1 w2, w1 ≠ w2 ∧ (w1 ∈ T.vs ∨ In3 a b c w1) ∧ (w2 ∈ T.vs ∨ In3 a b c w2) ∧
      (GT T a b c).Adj w1 p ∧ (GT T a b c).Adj w1 q ∧ (GT T a b c).Adj w1 r ∧
      (GT T a b c).Adj w2 p ∧ (GT T a b c).Adj w2 q ∧ (GT T a b c).Adj w2 r)

/-- every triangle of a region-tree graph is a leaf region, or has two common neighbours -/
def TR (T : RT V) : Prop :=
  ∀ a b c p q r, T.wf a b c → (GT T a b c).Adj p q → (GT T a b c).Adj q r →
    (GT T a b c).Adj p r → TRC T a b c p q r

/-- the generic child step of the triangle-region lemma -/
theorem child_case {G : SimpleGraph V} {T t : RT V} {a b c a' b' w c' p q r : V}
    (ih : TR t) (hwf : t.wf a' b' w) (hle : GT t a' b' w ≤ G)
    (hP : ∀ u u', (u ∈ t.vs ∨ In3 a' b' w u) → (u' ∈ t.vs ∨ In3 a' b' w u') → G.Adj u u' →
      (GT t a' b' w).Adj u u')
    (hp : p ∈ t.vs ∨ In3 a' b' w p) (hq : q ∈ t.vs ∨ In3 a' b' w q)
    (hr : r ∈ t.vs ∨ In3 a' b' w r)
    (hpq : G.Adj p q) (hqr : G.Adj q r) (hpr : G.Adj p r)
    (hca : G.Adj c' a') (hcb : G.Adj c' b') (hcw : G.Adj c' w) (hct : c' ∉ t.vs)
    (hM : ∀ z, (z ∈ t.vs ∨ In3 a' b' w z) → z ∈ T.vs ∨ In3 a b c z)
    (hMc : c' ∈ T.vs ∨ In3 a b c c') (hGT : G = GT T a b c)
    (hreb : ∀ v, v ∉ T.vs → v ≠ a → v ≠ b → v ≠ c → v ∉ t.vs ∧ v ≠ a' ∧ v ≠ b' ∧ v ≠ w ∧
      ∀ t' : RT V, t'.wf a' b' w → t'.vs = insert v t.vs →
        t'.gr a' b' w = t.gr a' b' w ⊔ star3 v p q r →
        ∃ T' : RT V, T'.wf a b c ∧ T'.vs = insert v T.vs ∧
          T'.gr a b c = T.gr a b c ⊔ star3 v p q r) :
    TRC T a b c p q r := by
  have h := ih a' b' w p q r hwf (hP p q hp hq hpq) (hP q r hq hr hqr) (hP p r hp hr hpr)
  rcases h with h1 | ⟨w', hw', ip, iq, ir, ap, aq, ar⟩ | ⟨w1, w2, hne, m1, m2, a1p, a1q, a1r,
    a2p, a2q, a2r⟩
  · left
    intro v hv ha hb hc
    obtain ⟨hvt, hva, hvb, hvw, hreb'⟩ := hreb v hv ha hb hc
    obtain ⟨t', e1, e2, e3⟩ := h1 v hvt hva hvb hvw
    exact hreb' t' e1 e2 e3
  · right; right
    rw [← hGT]
    refine ⟨w', c', fun e => hct (e ▸ hw'), hM w' (Or.inl hw'), hMc, hle ap, hle aq, hle ar,
      adj_of_In3 hca hcb hcw ip, adj_of_In3 hca hcb hcw iq, adj_of_In3 hca hcb hcw ir⟩
  · right; right
    rw [← hGT]
    exact ⟨w1, w2, hne, hM w1 m1, hM w2 m2, hle a1p, hle a1q, hle a1r, hle a2p, hle a2q, hle a2r⟩

theorem four_split {a b c w p q r : V} (hp : p = w ∨ In3 a b c p) (hq : q = w ∨ In3 a b c q)
    (hr : r = w ∨ In3 a b c r) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r)
    (h1 : ¬ (In3 a b w p ∧ In3 a b w q ∧ In3 a b w r))
    (h2 : ¬ (In3 b c w p ∧ In3 b c w q ∧ In3 b c w r))
    (h3 : ¬ (In3 c a w p ∧ In3 c a w q ∧ In3 c a w r)) :
    In3 a b c p ∧ In3 a b c q ∧ In3 a b c r := by
  unfold In3 at *
  rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
    rcases hr with rfl | rfl | rfl | rfl <;> simp_all

set_option maxHeartbeats 1000000 in
/-- **Triangle-region lemma** (C3b core). -/
theorem tri_region (T : RT V) : TR T := by
  induction T with
  | lf =>
    intro a b c p q r hwf hpq hqr hpr
    have e : ∀ u u', (GT (RT.lf : RT V) a b c).Adj u u' → (tri a b c).Adj u u' := by
      intro u u' h
      simpa [GT, RT.gr] using h
    have ip := (tri_In3_of_adj (e _ _ hpq)).1
    have iq := (tri_In3_of_adj (e _ _ hqr)).1
    have ir := (tri_In3_of_adj (e _ _ hpr)).2
    have hcov := In3_cover ip iq ir hpq.ne hqr.ne hpr.ne
    have hcov' : ∀ u, In3 p q r u ↔ In3 a b c u := by
      intro u
      refine ⟨fun hu => ?_, hcov u⟩
      rcases hu with rfl | rfl | rfl
      exacts [ip, iq, ir]
    obtain ⟨hab, hbc, hac⟩ := hwf
    left
    intro v _ hva hvb hvc
    refine ⟨.nd v .lf .lf .lf, ?_, ?_, ?_⟩
    · refine ⟨hab, hbc, hac, hva, hvb, hvc, ⟨hab, fun e => hvb e.symm, fun e => hva e.symm⟩,
        ⟨hbc, fun e => hvc e.symm, fun e => hvb e.symm⟩,
        ⟨fun e => hac e.symm, fun e => hva e.symm, fun e => hvc e.symm⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [RT.vs]
    · simp [RT.vs]
    · simp only [RT.gr, sup_bot_eq, bot_sup_eq]
      exact (star3_eq_of_cover hcov').symm
  | nd w t1 t2 t3 ih1 ih2 ih3 =>
    intro a b c p q r hwf hpq hqr hpr
    have hwf0 := hwf
    obtain ⟨hab, hbc, hac, hwa, hwb, hwc, h1, h2, h3, hc1, ha2, hb3, d12, d13, d23⟩ := hwf
    have o1 := RT.wf_out h1
    have o2 := RT.wf_out h2
    have o3 := RT.wf_out h3
    set G := GT (.nd w t1 t2 t3) a b c with hG
    have hwT : w ∈ (RT.nd w t1 t2 t3).vs := by simp [RT.vs]
    have s1 : ∀ z, z ∈ t1.vs → z ∈ (RT.nd w t1 t2 t3).vs := by intro z hz; simp [RT.vs, hz]
    have s2 : ∀ z, z ∈ t2.vs → z ∈ (RT.nd w t1 t2 t3).vs := by intro z hz; simp [RT.vs, hz]
    have s3 : ∀ z, z ∈ t3.vs → z ∈ (RT.nd w t1 t2 t3).vs := by intro z hz; simp [RT.vs, hz]
    -- the K4 on a b c w
    have k4 : ∀ u u', (u = w ∨ In3 a b c u) → (u' = w ∨ In3 a b c u') → u ≠ u' → G.Adj u u' := by
      intro u u' hu hu' hne
      rw [hG, gt_nd_adj]
      rcases hu with rfl | hu
      · rcases hu' with rfl | hu'
        · exact absurd rfl hne
        · exact Or.inr (Or.inl (star3_adj'.2 ⟨hne, Or.inl ⟨rfl, hu'⟩⟩))
      · rcases hu' with rfl | hu'
        · exact Or.inr (Or.inl (star3_adj'.2 ⟨hne, Or.inr ⟨rfl, hu⟩⟩))
        · exact Or.inl (tri_adj_of_In3 hu hu' hne)
    -- locality of the three children
    have loc1 : ∀ u u', u ∈ t1.vs → G.Adj u u' → (t1.gr a b w).Adj u u' := by
      intro u u' hu h
      rw [hG, gt_nd_adj] at h
      rcases h with h | h | h | h | h
      · rcases (tri_In3_of_adj h).1 with e | e | e <;> subst e
        exacts [absurd hu o1.1, absurd hu o1.2.1, absurd hu hc1]
      · rcases (star3_adj'.1 h).2 with ⟨e, _⟩ | ⟨_, e⟩
        · subst e; exact absurd hu o1.2.2
        · rcases e with e | e | e <;> subst e
          exacts [absurd hu o1.1, absurd hu o1.2.1, absurd hu hc1]
      · exact h
      · rcases (RT.gr_ends h).1 with e | e | e | e
        · exact absurd e (Finset.disjoint_left.mp d12 hu)
        all_goals (subst e; first | exact absurd hu o1.2.1 | exact absurd hu hc1 |
          exact absurd hu o1.2.2)
      · rcases (RT.gr_ends h).1 with e | e | e | e
        · exact absurd e (Finset.disjoint_left.mp d13 hu)
        all_goals (subst e; first | exact absurd hu hc1 | exact absurd hu o1.1 |
          exact absurd hu o1.2.2)
    have loc2 : ∀ u u', u ∈ t2.vs → G.Adj u u' → (t2.gr b c w).Adj u u' := by
      intro u u' hu h
      rw [hG, gt_nd_adj] at h
      rcases h with h | h | h | h | h
      · rcases (tri_In3_of_adj h).1 with e | e | e <;> subst e
        exacts [absurd hu ha2, absurd hu o2.1, absurd hu o2.2.1]
      · rcases (star3_adj'.1 h).2 with ⟨e, _⟩ | ⟨_, e⟩
        · subst e; exact absurd hu o2.2.2
        · rcases e with e | e | e <;> subst e
          exacts [absurd hu ha2, absurd hu o2.1, absurd hu o2.2.1]
      · rcases (RT.gr_ends h).1 with e | e | e | e
        · exact absurd hu (Finset.disjoint_left.mp d12 e)
        all_goals (subst e; first | exact absurd hu ha2 | exact absurd hu o2.1 |
          exact absurd hu o2.2.2)
      · exact h
      · rcases (RT.gr_ends h).1 with e | e | e | e
        · exact absurd e (Finset.disjoint_left.mp d23 hu)
        all_goals (subst e; first | exact absurd hu o2.2.1 | exact absurd hu ha2 |
          exact absurd hu o2.2.2)
    have loc3 : ∀ u u', u ∈ t3.vs → G.Adj u u' → (t3.gr c a w).Adj u u' := by
      intro u u' hu h
      rw [hG, gt_nd_adj] at h
      rcases h with h | h | h | h | h
      · rcases (tri_In3_of_adj h).1 with e | e | e <;> subst e
        exacts [absurd hu o3.2.1, absurd hu hb3, absurd hu o3.1]
      · rcases (star3_adj'.1 h).2 with ⟨e, _⟩ | ⟨_, e⟩
        · subst e; exact absurd hu o3.2.2
        · rcases e with e | e | e <;> subst e
          exacts [absurd hu o3.2.1, absurd hu hb3, absurd hu o3.1]
      · rcases (RT.gr_ends h).1 with e | e | e | e
        · exact absurd hu (Finset.disjoint_left.mp d13 e)
        all_goals (subst e; first | exact absurd hu o3.2.1 | exact absurd hu hb3 |
          exact absurd hu o3.2.2)
      · rcases (RT.gr_ends h).1 with e | e | e | e
        · exact absurd hu (Finset.disjoint_left.mp d23 e)
        all_goals (subst e; first | exact absurd hu hb3 | exact absurd hu o3.1 |
          exact absurd hu o3.2.2)
      · exact h
    -- the neighbour of a child vertex lies in the child's closed region
    have side1 : ∀ u u', u ∈ t1.vs → G.Adj u u' → (u' ∈ t1.vs ∨ In3 a b w u') :=
      fun u u' hu h => (RT.gr_ends (loc1 u u' hu h)).2.1
    have side2 : ∀ u u', u ∈ t2.vs → G.Adj u u' → (u' ∈ t2.vs ∨ In3 b c w u') :=
      fun u u' hu h => (RT.gr_ends (loc2 u u' hu h)).2.1
    have side3 : ∀ u u', u ∈ t3.vs → G.Adj u u' → (u' ∈ t3.vs ∨ In3 c a w u') :=
      fun u u' hu h => (RT.gr_ends (loc3 u u' hu h)).2.1
    -- the closed child graphs embed
    have le1 : GT t1 a b w ≤ G := by
      intro u u' h
      rw [GT, SimpleGraph.sup_adj] at h
      rcases h with h | h
      · have hi := tri_In3_of_adj h
        have L : ∀ z, In3 a b w z → z = w ∨ In3 a b c z := by
          intro z hz; rcases hz with e | e | e
          exacts [Or.inr (Or.inl e), Or.inr (Or.inr (Or.inl e)), Or.inl e]
        exact k4 u u' (L u hi.1) (L u' hi.2) h.ne
      · rw [hG, gt_nd_adj]; exact Or.inr (Or.inr (Or.inl h))
    have le2 : GT t2 b c w ≤ G := by
      intro u u' h
      rw [GT, SimpleGraph.sup_adj] at h
      rcases h with h | h
      · have hi := tri_In3_of_adj h
        have L : ∀ z, In3 b c w z → z = w ∨ In3 a b c z := by
          intro z hz; rcases hz with e | e | e
          exacts [Or.inr (Or.inr (Or.inl e)), Or.inr (Or.inr (Or.inr e)), Or.inl e]
        exact k4 u u' (L u hi.1) (L u' hi.2) h.ne
      · rw [hG, gt_nd_adj]; exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    have le3 : GT t3 c a w ≤ G := by
      intro u u' h
      rw [GT, SimpleGraph.sup_adj] at h
      rcases h with h | h
      · have hi := tri_In3_of_adj h
        have L : ∀ z, In3 c a w z → z = w ∨ In3 a b c z := by
          intro z hz; rcases hz with e | e | e
          exacts [Or.inr (Or.inr (Or.inr e)), Or.inr (Or.inl e), Or.inl e]
        exact k4 u u' (L u hi.1) (L u' hi.2) h.ne
      · rw [hG, gt_nd_adj]; exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    have P1 : ∀ u u', (u ∈ t1.vs ∨ In3 a b w u) → (u' ∈ t1.vs ∨ In3 a b w u') → G.Adj u u' →
        (GT t1 a b w).Adj u u' := by
      intro u u' hu hu' h
      by_cases m : u ∈ t1.vs
      · exact (SimpleGraph.sup_adj _ _ _ _).2 (Or.inr (loc1 u u' m h))
      by_cases m' : u' ∈ t1.vs
      · exact ((SimpleGraph.sup_adj _ _ _ _).2 (Or.inr (loc1 u' u m' h.symm))).symm
      exact (SimpleGraph.sup_adj _ _ _ _).2 (Or.inl (tri_adj_of_In3 (hu.resolve_left m)
        (hu'.resolve_left m') h.ne))
    have P2 : ∀ u u', (u ∈ t2.vs ∨ In3 b c w u) → (u' ∈ t2.vs ∨ In3 b c w u') → G.Adj u u' →
        (GT t2 b c w).Adj u u' := by
      intro u u' hu hu' h
      by_cases m : u ∈ t2.vs
      · exact (SimpleGraph.sup_adj _ _ _ _).2 (Or.inr (loc2 u u' m h))
      by_cases m' : u' ∈ t2.vs
      · exact ((SimpleGraph.sup_adj _ _ _ _).2 (Or.inr (loc2 u' u m' h.symm))).symm
      exact (SimpleGraph.sup_adj _ _ _ _).2 (Or.inl (tri_adj_of_In3 (hu.resolve_left m)
        (hu'.resolve_left m') h.ne))
    have P3 : ∀ u u', (u ∈ t3.vs ∨ In3 c a w u) → (u' ∈ t3.vs ∨ In3 c a w u') → G.Adj u u' →
        (GT t3 c a w).Adj u u' := by
      intro u u' hu hu' h
      by_cases m : u ∈ t3.vs
      · exact (SimpleGraph.sup_adj _ _ _ _).2 (Or.inr (loc3 u u' m h))
      by_cases m' : u' ∈ t3.vs
      · exact ((SimpleGraph.sup_adj _ _ _ _).2 (Or.inr (loc3 u' u m' h.symm))).symm
      exact (SimpleGraph.sup_adj _ _ _ _).2 (Or.inl (tri_adj_of_In3 (hu.resolve_left m)
        (hu'.resolve_left m') h.ne))
    have ia : In3 a b c a := Or.inl rfl
    have ib : In3 a b c b := Or.inr (Or.inl rfl)
    have ic : In3 a b c c := Or.inr (Or.inr rfl)
    by_cases A1 : (p ∈ t1.vs ∨ In3 a b w p) ∧ (q ∈ t1.vs ∨ In3 a b w q) ∧
        (r ∈ t1.vs ∨ In3 a b w r)
    · refine child_case (c' := c) ih1 h1 le1 P1 A1.1 A1.2.1 A1.2.2 hpq hqr hpr
        (k4 c a (Or.inr ic) (Or.inr ia) hac.symm) (k4 c b (Or.inr ic) (Or.inr ib) hbc.symm)
        (k4 c w (Or.inr ic) (Or.inl rfl) hwc.symm) hc1 ?_ (Or.inr ic) rfl ?_
      · intro z hz
        rcases hz with hz | e | e | e
        exacts [Or.inl (s1 z hz), Or.inr (Or.inl e), Or.inr (Or.inr (Or.inl e)),
          Or.inl (e ▸ hwT)]
      · intro v hv hva hvb hvc
        have hvw : v ≠ w := fun e => hv (e ▸ hwT)
        refine ⟨fun h => hv (s1 v h), hva, hvb, hvw, ?_⟩
        intro t' e1 e2 e3
        refine ⟨.nd w t' t2 t3, ⟨hab, hbc, hac, hwa, hwb, hwc, e1, h2, h3, ?_, ha2, hb3, ?_, ?_,
          d23⟩, ?_, ?_⟩
        · rw [e2, Finset.mem_insert]; rintro (e | e); exact hvc e.symm; exact hc1 e
        · rw [e2, Finset.disjoint_insert_left]
          exact ⟨fun h => hv (s2 v h), d12⟩
        · rw [e2, Finset.disjoint_insert_left]
          exact ⟨fun h => hv (s3 v h), d13⟩
        · simp only [RT.vs, e2]; exact vs_ins1 _ _ _ _ _
        · simp only [RT.gr, e3]; exact gr_ins1 _ _ _ _ _
    by_cases A2 : (p ∈ t2.vs ∨ In3 b c w p) ∧ (q ∈ t2.vs ∨ In3 b c w q) ∧
        (r ∈ t2.vs ∨ In3 b c w r)
    · refine child_case (c' := a) ih2 h2 le2 P2 A2.1 A2.2.1 A2.2.2 hpq hqr hpr
        (k4 a b (Or.inr ia) (Or.inr ib) hab) (k4 a c (Or.inr ia) (Or.inr ic) hac)
        (k4 a w (Or.inr ia) (Or.inl rfl) hwa.symm) ha2 ?_ (Or.inr ia) rfl ?_
      · intro z hz
        rcases hz with hz | e | e | e
        exacts [Or.inl (s2 z hz), Or.inr (Or.inr (Or.inl e)), Or.inr (Or.inr (Or.inr e)),
          Or.inl (e ▸ hwT)]
      · intro v hv hva hvb hvc
        have hvw : v ≠ w := fun e => hv (e ▸ hwT)
        refine ⟨fun h => hv (s2 v h), hvb, hvc, hvw, ?_⟩
        intro t' e1 e2 e3
        refine ⟨.nd w t1 t' t3, ⟨hab, hbc, hac, hwa, hwb, hwc, h1, e1, h3, hc1, ?_, hb3, ?_, d13,
          ?_⟩, ?_, ?_⟩
        · rw [e2, Finset.mem_insert]; rintro (e | e); exact hva e.symm; exact ha2 e
        · rw [e2, Finset.disjoint_insert_right]
          exact ⟨fun h => hv (s1 v h), d12⟩
        · rw [e2, Finset.disjoint_insert_left]
          exact ⟨fun h => hv (s3 v h), d23⟩
        · simp only [RT.vs, e2]; exact vs_ins2 _ _ _ _ _
        · simp only [RT.gr, e3]; exact gr_ins2 _ _ _ _ _
    by_cases A3 : (p ∈ t3.vs ∨ In3 c a w p) ∧ (q ∈ t3.vs ∨ In3 c a w q) ∧
        (r ∈ t3.vs ∨ In3 c a w r)
    · refine child_case (c' := b) ih3 h3 le3 P3 A3.1 A3.2.1 A3.2.2 hpq hqr hpr
        (k4 b c (Or.inr ib) (Or.inr ic) hbc) (k4 b a (Or.inr ib) (Or.inr ia) hab.symm)
        (k4 b w (Or.inr ib) (Or.inl rfl) hwb.symm) hb3 ?_ (Or.inr ib) rfl ?_
      · intro z hz
        rcases hz with hz | e | e | e
        exacts [Or.inl (s3 z hz), Or.inr (Or.inr (Or.inr e)), Or.inr (Or.inl e),
          Or.inl (e ▸ hwT)]
      · intro v hv hva hvb hvc
        have hvw : v ≠ w := fun e => hv (e ▸ hwT)
        refine ⟨fun h => hv (s3 v h), hvc, hva, hvw, ?_⟩
        intro t' e1 e2 e3
        refine ⟨.nd w t1 t2 t', ⟨hab, hbc, hac, hwa, hwb, hwc, h1, h2, e1, hc1, ha2, ?_, d12, ?_,
          ?_⟩, ?_, ?_⟩
        · rw [e2, Finset.mem_insert]; rintro (e | e); exact hvb e.symm; exact hb3 e
        · rw [e2, Finset.disjoint_insert_right]
          exact ⟨fun h => hv (s1 v h), d13⟩
        · rw [e2, Finset.disjoint_insert_right]
          exact ⟨fun h => hv (s2 v h), d23⟩
        · simp only [RT.vs, e2]; exact vs_ins3 _ _ _ _ _
        · simp only [RT.gr, e3]; exact gr_ins3 _ _ _ _ _
    -- the triangle is the boundary triangle itself
    have key : ∀ z z', G.Adj z z' → (z = p ∨ z = q ∨ z = r) → z = w ∨ In3 a b c z := by
      intro z z' hz hzm
      have all1 : z ∈ t1.vs → False := by
        intro m; apply A1
        rcases hzm with rfl | rfl | rfl
        · exact ⟨Or.inl m, side1 _ _ m hpq, side1 _ _ m hpr⟩
        · exact ⟨side1 _ _ m hpq.symm, Or.inl m, side1 _ _ m hqr⟩
        · exact ⟨side1 _ _ m hpr.symm, side1 _ _ m hqr.symm, Or.inl m⟩
      have all2 : z ∈ t2.vs → False := by
        intro m; apply A2
        rcases hzm with rfl | rfl | rfl
        · exact ⟨Or.inl m, side2 _ _ m hpq, side2 _ _ m hpr⟩
        · exact ⟨side2 _ _ m hpq.symm, Or.inl m, side2 _ _ m hqr⟩
        · exact ⟨side2 _ _ m hpr.symm, side2 _ _ m hqr.symm, Or.inl m⟩
      have all3 : z ∈ t3.vs → False := by
        intro m; apply A3
        rcases hzm with rfl | rfl | rfl
        · exact ⟨Or.inl m, side3 _ _ m hpq, side3 _ _ m hpr⟩
        · exact ⟨side3 _ _ m hpq.symm, Or.inl m, side3 _ _ m hqr⟩
        · exact ⟨side3 _ _ m hpr.symm, side3 _ _ m hqr.symm, Or.inl m⟩
      rcases GT_ends hz with m | m
      · rcases RT.vs_nd.1 m with e | m | m | m
        · exact Or.inl e
        · exact (all1 m).elim
        · exact (all2 m).elim
        · exact (all3 m).elim
      · exact Or.inr m
    have N1 : ¬ (In3 a b w p ∧ In3 a b w q ∧ In3 a b w r) :=
      fun h => A1 ⟨Or.inr h.1, Or.inr h.2.1, Or.inr h.2.2⟩
    have N2 : ¬ (In3 b c w p ∧ In3 b c w q ∧ In3 b c w r) :=
      fun h => A2 ⟨Or.inr h.1, Or.inr h.2.1, Or.inr h.2.2⟩
    have N3 : ¬ (In3 c a w p ∧ In3 c a w q ∧ In3 c a w r) :=
      fun h => A3 ⟨Or.inr h.1, Or.inr h.2.1, Or.inr h.2.2⟩
    obtain ⟨ip, iq, ir⟩ := four_split (key p q hpq (Or.inl rfl)) (key q r hqr (Or.inr (Or.inl rfl)))
      (key r p hpr.symm (Or.inr (Or.inr rfl))) hpq.ne hqr.ne hpr.ne N1 N2 N3
    have hwn : ∀ z, In3 a b c z → w ≠ z := by
      intro z hz e; subst e
      rcases hz with e | e | e
      exacts [hwa e, hwb e, hwc e]
    right; left
    exact ⟨w, hwT, ip, iq, ir, k4 w p (Or.inl rfl) (Or.inr ip) (hwn p ip),
      k4 w q (Or.inl rfl) (Or.inr iq) (hwn q iq), k4 w r (Or.inl rfl) (Or.inr ir) (hwn r ir)⟩

set_option maxHeartbeats 1000000 in
/-- **Extraction (C3b).** A 3-tree inside an Apollonian graph `Hf`, grown from a face of `Hf`,
is the graph of a region tree over that face. -/
theorem extract_rt {Hf : SimpleGraph V} (hT : TriCond Hf) {H : SimpleGraph V} {S : Finset V}
    {x y z : V} (h : TTb H S x y z) (hle : H ≤ Hf) (hF : Face Hf x y z) :
    ∃ T : RT V, T.wf x y z ∧ H = GT T x y z ∧ ∀ u, u ∈ S ↔ u ∈ T.vs ∨ In3 x y z u := by
  induction h with
  | base x y z hxy hyz hxz =>
    refine ⟨.lf, ⟨hxy, hyz, hxz⟩, by simp [GT, RT.gr], ?_⟩
    intro u; simp [RT.vs, In3]
  | @stack H S x y z v p q r h hv hp hq hr hpq hqr hpr ih =>
    obtain ⟨T, hwf, hH, hS⟩ := ih (le_trans le_sup_left hle) hF
    have hH' : ∀ s t, (GT T x y z).Adj s t → Hf.Adj s t := by
      intro s t hst; rw [← hH] at hst; exact hle ((SimpleGraph.sup_adj _ _ _ _).2 (Or.inl hst))
    have hvS : ∀ u, u ∈ T.vs ∨ In3 x y z u → v ≠ u := by
      intro u hu e; subst e; exact hv ((hS _).2 hu)
    have hstar : ∀ s, In3 p q r s → Hf.Adj v s := by
      intro s hs
      have hs' : s ∈ S := by
        rcases hs with rfl | rfl | rfl
        exacts [hp, hq, hr]
      exact hle ((SimpleGraph.sup_adj _ _ _ _).2 (Or.inr (star3_adj_of_In3 (hvS s ((hS s).1 hs')) hs)))
    rw [hH] at hpq hqr hpr
    have hvT : v ∉ T.vs := fun m => hvS v (Or.inl m) rfl
    rcases tri_region T x y z p q r hwf hpq hqr hpr with h1 | ⟨w, hw, ip, iq, ir, ap, aq, ar⟩ |
      ⟨w1, w2, hne, m1, m2, a1p, a1q, a1r, a2p, a2q, a2r⟩
    · obtain ⟨T', e1, e2, e3⟩ := h1 v hvT (hvS _ (Or.inr (Or.inl rfl)))
        (hvS _ (Or.inr (Or.inr (Or.inl rfl)))) (hvS _ (Or.inr (Or.inr (Or.inr rfl))))
      refine ⟨T', e1, ?_, ?_⟩
      · rw [hH]; simp only [GT, e3, sup_assoc]
      · intro u; rw [e2, Finset.mem_insert, Finset.mem_insert, hS]; tauto
    · exfalso
      have cov := In3_cover ip iq ir hpq.ne hqr.ne hpr.ne
      have hw' : ∀ s, In3 p q r s → Hf.Adj w s := fun s hs =>
        adj_of_In3 (hH' _ _ ap) (hH' _ _ aq) (hH' _ _ ar) hs
      exact hF.2.2.2 w v (fun e => hvT (e ▸ hw)) (hw' _ (cov _ (Or.inl rfl)))
        (hw' _ (cov _ (Or.inr (Or.inl rfl)))) (hw' _ (cov _ (Or.inr (Or.inr rfl))))
        (hstar _ (cov _ (Or.inl rfl))) (hstar _ (cov _ (Or.inr (Or.inl rfl))))
        (hstar _ (cov _ (Or.inr (Or.inr rfl))))
    · exfalso
      exact hT p q r w1 w2 v (hH' _ _ hpq) (hH' _ _ hqr) (hH' _ _ hpr) hne
        (fun e => hvS w2 m2 e.symm) (fun e => hvS w1 m1 e.symm)
        (hH' _ _ a1p) (hH' _ _ a1q) (hH' _ _ a1r) (hH' _ _ a2p) (hH' _ _ a2q) (hH' _ _ a2r)
        (hstar p (Or.inl rfl)) (hstar q (Or.inr (Or.inl rfl))) (hstar r (Or.inr (Or.inr rfl)))

/-- **C3b.** An Apollonian 3-tree on all of `V` is the graph of a region tree over a face. -/
theorem rt_of_TT {V : Type} [Fintype V] [DecidableEq V] {H : SimpleGraph V}
    (hT : TT H Finset.univ) (hC : TriCond H) :
    ∃ (x y z : V) (T : RT V), T.wf x y z ∧ H = GT T x y z ∧ ∀ u, u ∈ T.vs ∨ In3 x y z u := by
  obtain ⟨x, y, z, h⟩ := hT
  have hb := h.base_mem
  obtain ⟨t, hF⟩ := h.edge_face x y hb.2.2.2.1
  have h' := h.reroot x y t hF.1 hF.2.1 hF.2.2.1
  obtain ⟨T, hw, hH, hS⟩ := extract_rt hC h' le_rfl hF
  exact ⟨x, y, t, T, hw, hH, fun u => (hS u).1 (Finset.mem_univ u)⟩

end C3b

end PQL5

/-! Q1 (8100c3d9): straight-line drawing of Apollonian region-tree graphs `GT T a b c`
(centroid stacking), hence `IsPlanar`. Pure orientation-determinant algebra. -/

namespace PQL5

section SLgeom

/-- twice the signed area of the triangle `A B C` -/
def orient (A B C : ℝ × ℝ) : ℝ := (B.1 - A.1) * (C.2 - A.2) - (B.2 - A.2) * (C.1 - A.1)

/-- the point at parameter `t` on the segment from `P` to `Q` -/
def segP (P Q : ℝ × ℝ) (t : ℝ) : ℝ × ℝ := (P.1 + t * (Q.1 - P.1), P.2 + t * (Q.2 - P.2))

/-- the open segment -/
def OP (P Q : ℝ × ℝ) : Set (ℝ × ℝ) := {X | ∃ t : ℝ, 0 < t ∧ t < 1 ∧ X = segP P Q t}

/-- `P` lies in the open triangle `A B C` (positively oriented) -/
def Ins (A B C P : ℝ × ℝ) : Prop := 0 < orient A B P ∧ 0 < orient B C P ∧ 0 < orient C A P

/-- the centroid -/
noncomputable def cen (A B C : ℝ × ℝ) : ℝ × ℝ := ((A.1 + B.1 + C.1) / 3, (A.2 + B.2 + C.2) / 3)

/-- one of the three corners -/
def Cor (A B C X : ℝ × ℝ) : Prop := X = A ∨ X = B ∨ X = C

theorem orient_cyc (A B C : ℝ × ℝ) : orient B C A = orient A B C := by
  unfold orient; ring

theorem orient_swap (A B C : ℝ × ℝ) : orient B A C = - orient A B C := by
  unfold orient; ring

theorem orient_aab (A C : ℝ × ℝ) : orient A A C = 0 := by unfold orient; ring

theorem orient_aba (A B : ℝ × ℝ) : orient A B A = 0 := by unfold orient; ring

theorem orient_abb (A B : ℝ × ℝ) : orient A B B = 0 := by unfold orient; ring

theorem orient_seg (X Y P Q : ℝ × ℝ) (t : ℝ) :
    orient X Y (segP P Q t) = (1 - t) * orient X Y P + t * orient X Y Q := by
  simp only [orient, segP]; ring

theorem segP_zero (P Q : ℝ × ℝ) : segP P Q 0 = P := by
  simp [segP]

theorem segP_one (P Q : ℝ × ℝ) : segP P Q 1 = Q := by
  ext <;> simp [segP]

theorem segP_inj {P Q : ℝ × ℝ} (hPQ : P ≠ Q) {s t : ℝ} (h : segP P Q s = segP P Q t) : s = t := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [segP] at h1 h2
  have e1 : (s - t) * (Q.1 - P.1) = 0 := by linear_combination h1
  have e2 : (s - t) * (Q.2 - P.2) = 0 := by linear_combination h2
  rcases mul_eq_zero.1 e1 with e | e
  · linarith
  rcases mul_eq_zero.1 e2 with e' | e'
  · linarith
  exact absurd (Prod.ext (by linarith) (by linarith)) (Ne.symm hPQ)

theorem OP_symm (P Q : ℝ × ℝ) : OP P Q = OP Q P := by
  have key : ∀ P Q : ℝ × ℝ, OP P Q ⊆ OP Q P := by
    intro P Q X hX
    obtain ⟨t, h0, h1, hX⟩ := hX
    refine ⟨1 - t, by linarith, by linarith, ?_⟩
    rw [hX]
    ext <;> simp only [segP] <;> ring
  exact Set.Subset.antisymm (key P Q) (key Q P)

theorem Ins_rot {A B C P : ℝ × ℝ} (h : Ins A B C P) : Ins B C A P := ⟨h.2.1, h.2.2, h.1⟩

theorem orient_cen1 (A B C : ℝ × ℝ) : orient A B (cen A B C) = orient A B C / 3 := by
  simp only [orient, cen]; ring

theorem orient_cen2 (A B C : ℝ × ℝ) : orient B C (cen A B C) = orient A B C / 3 := by
  simp only [orient, cen]; ring

theorem orient_cen3 (A B C : ℝ × ℝ) : orient C A (cen A B C) = orient A B C / 3 := by
  simp only [orient, cen]; ring

theorem cen_ins {A B C : ℝ × ℝ} (h : 0 < orient A B C) : Ins A B C (cen A B C) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [orient_cen1]; linarith
  · rw [orient_cen2]; linarith
  · rw [orient_cen3]; linarith

theorem not_ins_A {A B C : ℝ × ℝ} : ¬ Ins A B C A := fun h => by
  have := h.1; rw [orient_aba] at this; exact lt_irrefl _ this

theorem not_ins_B {A B C : ℝ × ℝ} : ¬ Ins A B C B := fun h => by
  have := h.1; rw [orient_abb] at this; exact lt_irrefl _ this

theorem not_ins_C {A B C : ℝ × ℝ} : ¬ Ins A B C C := fun h => by
  have := h.2.1; rw [orient_abb] at this; exact lt_irrefl _ this

theorem not_ins_cor {A B C X : ℝ × ℝ} (h : Cor A B C X) : ¬ Ins A B C X := by
  rcases h with rfl | rfl | rfl
  · exact not_ins_A
  · exact not_ins_B
  · exact not_ins_C

theorem cor_ne {A B C : ℝ × ℝ} (h0 : 0 < orient A B C) : A ≠ B ∧ B ≠ C ∧ A ≠ C := by
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
  · rw [e, orient_aab] at h0; exact lt_irrefl _ h0
  · rw [e, orient_abb] at h0; exact lt_irrefl _ h0
  · rw [e, orient_aba] at h0; exact lt_irrefl _ h0

theorem pos_of_mul_pos' {a b : ℝ} (ha : 0 < a) (h : 0 < a * b) : 0 < b := by
  by_contra hb
  have hb' : b ≤ 0 := le_of_not_gt hb
  nlinarith

theorem ins_sub {A B C V P : ℝ × ℝ} (h0 : 0 < orient A B C) (hV : Ins A B C V)
    (hP : Ins A B V P) : Ins A B C P := by
  obtain ⟨v1, v2, v3⟩ := hV
  obtain ⟨p1, p2, p3⟩ := hP
  have i1 : orient A B V * orient B C P =
      orient B V P * orient A B C + orient A B P * orient B C V := by
    simp only [orient]; ring
  have i2 : orient A B V * orient C A P =
      orient V A P * orient A B C + orient A B P * orient C A V := by
    simp only [orient]; ring
  refine ⟨p1, pos_of_mul_pos' v1 ?_, pos_of_mul_pos' v1 ?_⟩
  · rw [i1]; exact add_pos (mul_pos p2 h0) (mul_pos p1 v2)
  · rw [i2]; exact add_pos (mul_pos p3 h0) (mul_pos p1 v3)

theorem ins_sub2 {A B C V P : ℝ × ℝ} (h0 : 0 < orient A B C) (hV : Ins A B C V)
    (hP : Ins B C V P) : Ins A B C P := by
  have h0' : 0 < orient B C A := by rw [orient_cyc]; exact h0
  exact Ins_rot (Ins_rot (ins_sub h0' (Ins_rot hV) hP))

theorem ins_sub3 {A B C V P : ℝ × ℝ} (h0 : 0 < orient A B C) (hV : Ins A B C V)
    (hP : Ins C A V P) : Ins A B C P := by
  have h0' : 0 < orient C A B := by rw [orient_cyc, orient_cyc]; exact h0
  exact Ins_rot (ins_sub h0' (Ins_rot (Ins_rot hV)) hP)

theorem dis12 {A B C V P : ℝ × ℝ} (h1 : Ins A B V P) (h2 : Ins B C V P) : False := by
  have e := orient_swap V B P
  linarith [h1.2.1, h2.2.2]

theorem dis13 {A B C V P : ℝ × ℝ} (h1 : Ins A B V P) (h3 : Ins C A V P) : False := by
  have e := orient_swap V A P
  linarith [h1.2.2, h3.2.1]

theorem dis23 {A B C V P : ℝ × ℝ} (h2 : Ins B C V P) (h3 : Ins C A V P) : False := by
  have e := orient_swap V C P
  linarith [h2.2.1, h3.2.2]

theorem starA_in {A B C V : ℝ × ℝ} (h0 : 0 < orient A B C) (hV : Ins A B C V) :
    ∀ X ∈ OP V A, Ins A B C X := by
  rintro X ⟨t, t0, t1, rfl⟩
  obtain ⟨v1, v2, v3⟩ := hV
  have c1 := orient_cyc A B C
  refine ⟨?_, ?_, ?_⟩
  · rw [orient_seg, orient_aba]
    have := mul_pos (sub_pos.2 t1) v1; linarith
  · rw [orient_seg, c1]
    have := mul_pos (sub_pos.2 t1) v2; have := mul_pos t0 h0; linarith
  · rw [orient_seg, orient_abb]
    have := mul_pos (sub_pos.2 t1) v3; linarith

theorem starA_out {A B C V : ℝ × ℝ} (hV : Ins A B C V) :
    ∀ X ∈ OP V A, ¬ Ins A B V X ∧ ¬ Ins B C V X ∧ ¬ Ins C A V X := by
  rintro X ⟨t, t0, t1, rfl⟩
  obtain ⟨v1, v2, v3⟩ := hV
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := h.2.2; rw [orient_seg, orient_aba, orient_abb] at this; linarith
  · have := h.2.1; rw [orient_seg, orient_abb, orient_cyc, orient_swap] at this
    have := mul_pos t0 v3; linarith
  · have := h.2.1; rw [orient_seg, orient_abb, orient_aba] at this; linarith

theorem starAB_dis {A B C V : ℝ × ℝ} (hV : Ins A B C V) : ∀ X ∈ OP V A, X ∉ OP V B := by
  rintro X ⟨s, s0, s1, rfl⟩ ⟨t, t0, t1, ht⟩
  have e := congrArg (orient V A) ht
  rw [orient_seg, orient_seg, orient_aba, orient_abb] at e
  rw [← orient_cyc V A B] at e
  have := mul_pos t0 hV.1
  linarith

theorem star_V {A B C V Z : ℝ × ℝ} (hV : Ins A B C V) (hZ : Cor A B C Z) : V ∉ OP V Z := by
  rintro ⟨t, t0, t1, ht⟩
  have hVZ : V ≠ Z := fun e => not_ins_cor hZ (e ▸ hV)
  have := segP_inj hVZ (ht.symm.trans (segP_zero V Z).symm)
  linarith

theorem star_props {A B C V Z : ℝ × ℝ} (h0 : 0 < orient A B C) (hV : Ins A B C V)
    (hZ : Cor A B C Z) :
    (∀ X ∈ OP V Z, Ins A B C X) ∧
      (∀ X ∈ OP V Z, ¬ Ins A B V X ∧ ¬ Ins B C V X ∧ ¬ Ins C A V X) := by
  have h0b : 0 < orient B C A := by rw [orient_cyc]; exact h0
  have h0c : 0 < orient C A B := by rw [orient_cyc, orient_cyc]; exact h0
  rcases hZ with rfl | rfl | rfl
  · exact ⟨starA_in h0 hV, starA_out hV⟩
  · refine ⟨fun X hX => Ins_rot (Ins_rot (starA_in h0b (Ins_rot hV) X hX)), fun X hX => ?_⟩
    obtain ⟨n1, n2, n3⟩ := starA_out (Ins_rot hV) X hX
    exact ⟨n3, n1, n2⟩
  · refine ⟨fun X hX => Ins_rot (starA_in h0c (Ins_rot (Ins_rot hV)) X hX), fun X hX => ?_⟩
    obtain ⟨n1, n2, n3⟩ := starA_out (Ins_rot (Ins_rot hV)) X hX
    exact ⟨n2, n3, n1⟩

theorem star_dis {A B C V Z Z' : ℝ × ℝ} (hV : Ins A B C V) (hZ : Cor A B C Z)
    (hZ' : Cor A B C Z') (hne : Z ≠ Z') : ∀ X ∈ OP V Z, X ∉ OP V Z' := by
  have hb : Ins B C A V := Ins_rot hV
  have hc : Ins C A B V := Ins_rot hb
  intro X hX hX'
  rcases hZ with rfl | rfl | rfl <;> rcases hZ' with rfl | rfl | rfl
  · exact hne rfl
  · exact starAB_dis hV X hX hX'
  · exact starAB_dis hc X hX' hX
  · exact starAB_dis hV X hX' hX
  · exact hne rfl
  · exact starAB_dis hb X hX hX'
  · exact starAB_dis hc X hX hX'
  · exact starAB_dis hb X hX' hX
  · exact hne rfl

/-- points of a side of the triangle are not inside it -/
theorem side_AB {A B X : ℝ × ℝ} (h : X ∈ OP A B) : orient A B X = 0 := by
  obtain ⟨t, _, _, rfl⟩ := h
  rw [orient_seg, orient_aba, orient_abb]; ring

theorem side_BC {B C X : ℝ × ℝ} (h : X ∈ OP B C) : orient B C X = 0 := side_AB h

theorem side_CA {A C X : ℝ × ℝ} (h : X ∈ OP A C) : orient C A X = 0 := by
  rw [OP_symm] at h; exact side_AB h

end SLgeom

section SLpath

/-- the straight segment as a path -/
def segPath (P Q : ℝ × ℝ) : Path P Q where
  toFun t := segP P Q (t : ℝ)
  continuous_toFun := by unfold segP; fun_prop
  source' := by simp [segP]
  target' := by ext <;> simp [segP]

theorem segPath_apply (P Q : ℝ × ℝ) (t : unitInterval) : segPath P Q t = segP P Q (t : ℝ) := rfl

theorem unit_tri3 (t : unitInterval) : t = 0 ∨ t = 1 ∨ (0 < (t : ℝ) ∧ (t : ℝ) < 1) := by
  rcases eq_or_lt_of_le t.2.1 with h | h
  · left; exact Subtype.ext h.symm
  rcases eq_or_lt_of_le t.2.2 with h' | h'
  · right; left; exact Subtype.ext h'
  · right; right; exact ⟨h, h'⟩

/-- a straight-line drawing with pairwise disjoint open edges avoiding all vertices is a plane
drawing -/
theorem planar_of_straight {W : Type} (G : SimpleGraph W) (p : W → ℝ × ℝ)
    (hinj : Function.Injective p)
    (hdis : ∀ u w x y, G.Adj u w → G.Adj x y → s(u, w) ≠ s(x, y) →
      ∀ X ∈ OP (p u) (p w), X ∉ OP (p x) (p y))
    (hav : ∀ u w, G.Adj u w → ∀ x, p x ∉ OP (p u) (p w)) :
    RobertsonSeymour1986.GM5.IsPlanar G := by
  have hne : ∀ {u w : W}, G.Adj u w → p u ≠ p w := fun h e => G.ne_of_adj h (hinj e)
  refine ⟨{
    vertex := p
    vertex_injective := hinj
    arc := fun {u w} _ => segPath (p u) (p w)
    arc_injective := ?_
    arc_reverse := ?_
    arc_avoids_vertices := ?_
    arcs_meet_only_at_endpoints := ?_ }⟩
  · intro u w h s t hst
    rw [segPath_apply, segPath_apply] at hst
    exact Subtype.ext (segP_inj (hne h) hst)
  · intro u w h
    ext t <;> simp [segPath_apply, segP, Function.comp_apply, unitInterval.coe_symm_eq] <;> ring
  · intro u w h t x hx
    rcases unit_tri3 t with rfl | rfl | ⟨t0, t1⟩
    · left; apply hinj; rw [← hx, Path.source]
    · right; apply hinj; rw [← hx, Path.target]
    · exact absurd ⟨(t : ℝ), t0, t1, hx.symm⟩ (hav u w h x)
  · intro u w x y h k s t hst
    rcases unit_tri3 s with hs | hs | ⟨s0, s1⟩ <;> rcases unit_tri3 t with ht | ht | ⟨t0, t1⟩
    · exact Or.inr (Or.inr ⟨Or.inl hs, Or.inl ht⟩)
    · exact Or.inr (Or.inr ⟨Or.inl hs, Or.inr ht⟩)
    · subst hs
      rw [Path.source] at hst
      exact absurd ⟨(t : ℝ), t0, t1, hst⟩ (hav x y k u)
    · exact Or.inr (Or.inr ⟨Or.inr hs, Or.inl ht⟩)
    · exact Or.inr (Or.inr ⟨Or.inr hs, Or.inr ht⟩)
    · subst hs
      rw [Path.target] at hst
      exact absurd ⟨(t : ℝ), t0, t1, hst⟩ (hav x y k w)
    · subst ht
      rw [Path.source] at hst
      exact absurd ⟨(s : ℝ), s0, s1, hst.symm⟩ (hav u w h x)
    · subst ht
      rw [Path.target] at hst
      exact absurd ⟨(s : ℝ), s0, s1, hst.symm⟩ (hav u w h y)
    · by_cases hsym : s(u, w) = s(x, y)
      · rcases Sym2.eq_iff.1 hsym with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr (Or.inl ⟨h1, h2⟩)
      · exact absurd ⟨(t : ℝ), t0, t1, hst⟩
          (hdis u w x y h k hsym _ ⟨(s : ℝ), s0, s1, rfl⟩)

end SLpath

section SLrt

variable {V : Type} [DecidableEq V]

/-- centroid placement of the stacked vertices of a region tree in the triangle `A B C` -/
noncomputable def RT.pl : RT V → ℝ × ℝ → ℝ × ℝ → ℝ × ℝ → V → ℝ × ℝ
  | .lf, _, _, _, _ => (0, 0)
  | .nd v t1 t2 t3, A, B, C, u =>
      if u = v then cen A B C
      else if u ∈ t1.vs then t1.pl A B (cen A B C) u
      else if u ∈ t2.vs then t2.pl B C (cen A B C) u
      else t3.pl C A (cen A B C) u

/-- the region invariant of the centroid drawing -/
structure RegOK (T : RT V) (a b c : V) (A B C : ℝ × ℝ) (p : V → ℝ × ℝ) : Prop where
  r1 : ∀ u ∈ T.vs, Ins A B C (p u)
  r2 : ∀ u w, (T.gr a b c).Adj u w → ∀ X ∈ OP (p u) (p w), Ins A B C X
  r3 : ∀ u w x y, (T.gr a b c).Adj u w → (T.gr a b c).Adj x y → s(u, w) ≠ s(x, y) →
        ∀ X ∈ OP (p u) (p w), X ∉ OP (p x) (p y)
  r4 : ∀ u w, (T.gr a b c).Adj u w → ∀ x ∈ T.vs, p x ∉ OP (p u) (p w)
  r5 : ∀ x ∈ T.vs, ∀ y ∈ T.vs, p x = p y → x = y

theorem OP_of_sym2 (p : V → ℝ × ℝ) {u w x y : V} (h : s(u, w) = s(x, y)) :
    OP (p u) (p w) = OP (p x) (p y) := by
  rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact OP_symm _ _

theorem gr_nd_cases {v : V} {t1 t2 t3 : RT V} {a b c u w : V}
    (h : ((RT.nd v t1 t2 t3).gr a b c).Adj u w) :
    (∃ z, In3 a b c z ∧ s(u, w) = s(v, z)) ∨ (t1.gr a b v).Adj u w ∨
      (t2.gr b c v).Adj u w ∨ (t3.gr c a v).Adj u w := by
  simp only [RT.gr, SimpleGraph.sup_adj] at h
  rcases h with ((h | h) | h) | h
  · left
    rw [star3_adj] at h
    obtain ⟨_, h⟩ := h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨_, Or.inl rfl, rfl⟩
    · exact ⟨_, Or.inl rfl, Sym2.eq_swap⟩
    · exact ⟨_, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨_, Or.inr (Or.inl rfl), Sym2.eq_swap⟩
    · exact ⟨_, Or.inr (Or.inr rfl), rfl⟩
    · exact ⟨_, Or.inr (Or.inr rfl), Sym2.eq_swap⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem cor_of_in3 {p : V → ℝ × ℝ} {a b c : V} {A B C : ℝ × ℝ}
    (hpa : p a = A) (hpb : p b = B) (hpc : p c = C) {z : V} (hz : In3 a b c z) :
    Cor A B C (p z) := by
  rcases hz with rfl | rfl | rfl
  · exact Or.inl hpa
  · exact Or.inr (Or.inl hpb)
  · exact Or.inr (Or.inr hpc)

theorem in3_inj {p : V → ℝ × ℝ} {a b c : V} {A B C : ℝ × ℝ} (h0 : 0 < orient A B C)
    (hpa : p a = A) (hpb : p b = B) (hpc : p c = C) {z z' : V} (hz : In3 a b c z)
    (hz' : In3 a b c z') (h : p z = p z') : z = z' := by
  obtain ⟨n1, n2, n3⟩ := cor_ne h0
  rcases hz with rfl | rfl | rfl <;> rcases hz' with rfl | rfl | rfl
  all_goals first
    | rfl
    | (exfalso; rw [hpa, hpb] at h; first | exact n1 h | exact n1 h.symm)
    | (exfalso; rw [hpb, hpc] at h; first | exact n2 h | exact n2 h.symm)
    | (exfalso; rw [hpa, hpc] at h; first | exact n3 h | exact n3 h.symm)

theorem reg_ok (T : RT V) : ∀ (a b c : V) (A B C : ℝ × ℝ) (p : V → ℝ × ℝ), T.wf a b c →
    0 < orient A B C → p a = A → p b = B → p c = C → (∀ u ∈ T.vs, p u = T.pl A B C u) →
    RegOK T a b c A B C p := by
  induction T with
  | lf =>
    intro a b c A B C p _ _ _ _ _ _
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [RT.vs, RT.gr]
  | nd v t1 t2 t3 ih1 ih2 ih3 =>
    intro a b c A B C p hwf h0 hpa hpb hpc hpl
    obtain ⟨_, _, _, _, _, _, w1, w2, w3, _, _, _, d12, d13, d23⟩ := hwf
    have o1 := RT.wf_out w1
    have o2 := RT.wf_out w2
    have o3 := RT.wf_out w3
    have hV : Ins A B C (cen A B C) := cen_ins h0
    have hpv : p v = cen A B C := by
      rw [hpl v (RT.vs_nd.2 (Or.inl rfl))]; simp [RT.pl]
    have hp1 : ∀ u ∈ t1.vs, p u = t1.pl A B (cen A B C) u := by
      intro u hu
      have huv : u ≠ v := fun e => o1.2.2 (e ▸ hu)
      rw [hpl u (RT.vs_nd.2 (Or.inr (Or.inl hu)))]
      simp [RT.pl, huv, hu]
    have hp2 : ∀ u ∈ t2.vs, p u = t2.pl B C (cen A B C) u := by
      intro u hu
      have huv : u ≠ v := fun e => o2.2.2 (e ▸ hu)
      have hu1 : u ∉ t1.vs := fun h => Finset.disjoint_left.1 d12 h hu
      rw [hpl u (RT.vs_nd.2 (Or.inr (Or.inr (Or.inl hu))))]
      simp [RT.pl, huv, hu1, hu]
    have hp3 : ∀ u ∈ t3.vs, p u = t3.pl C A (cen A B C) u := by
      intro u hu
      have huv : u ≠ v := fun e => o3.2.2 (e ▸ hu)
      have hu1 : u ∉ t1.vs := fun h => Finset.disjoint_left.1 d13 h hu
      have hu2 : u ∉ t2.vs := fun h => Finset.disjoint_left.1 d23 h hu
      rw [hpl u (RT.vs_nd.2 (Or.inr (Or.inr (Or.inr hu))))]
      simp [RT.pl, huv, hu1, hu2]
    have I1 := ih1 a b v A B (cen A B C) p w1 hV.1 hpa hpb hpv hp1
    have I2 := ih2 b c v B C (cen A B C) p w2 hV.2.1 hpb hpc hpv hp2
    have I3 := ih3 c a v C A (cen A B C) p w3 hV.2.2 hpc hpa hpv hp3
    have nV1 : ¬ Ins A B (cen A B C) (cen A B C) := not_ins_C
    have nV2 : ¬ Ins B C (cen A B C) (cen A B C) := not_ins_C
    have nV3 : ¬ Ins C A (cen A B C) (cen A B C) := not_ins_C
    -- star edges: open part of `v z`
    have hstar : ∀ {u w z : V}, In3 a b c z → s(u, w) = s(v, z) →
        OP (p u) (p w) = OP (cen A B C) (p z) := by
      intro u w z _ hs
      rw [OP_of_sym2 p hs, hpv]
    have SP := fun (z : V) (hz : In3 a b c z) => star_props h0 hV (cor_of_in3 hpa hpb hpc hz)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- r1
      intro u hu
      rcases RT.vs_nd.1 hu with rfl | hu | hu | hu
      · rw [hpv]; exact hV
      · exact ins_sub h0 hV (I1.r1 u hu)
      · exact ins_sub2 h0 hV (I2.r1 u hu)
      · exact ins_sub3 h0 hV (I3.r1 u hu)
    · -- r2
      intro u w he X hX
      rcases gr_nd_cases he with ⟨z, hz, hs⟩ | he | he | he
      · rw [hstar hz hs] at hX; exact (SP z hz).1 X hX
      · exact ins_sub h0 hV (I1.r2 u w he X hX)
      · exact ins_sub2 h0 hV (I2.r2 u w he X hX)
      · exact ins_sub3 h0 hV (I3.r2 u w he X hX)
    · -- r3
      intro u w x y he hf hne X hX hX'
      rcases gr_nd_cases he with ⟨z, hz, hs⟩ | e1 | e2 | e3 <;>
        rcases gr_nd_cases hf with ⟨z', hz', hs'⟩ | f1 | f2 | f3
      · rw [hstar hz hs] at hX; rw [hstar hz' hs'] at hX'
        have hzz : z ≠ z' := fun e => hne (by rw [hs, hs', e])
        exact star_dis hV (cor_of_in3 hpa hpb hpc hz) (cor_of_in3 hpa hpb hpc hz')
          (fun e => hzz (in3_inj h0 hpa hpb hpc hz hz' e)) X hX hX'
      · rw [hstar hz hs] at hX; exact ((SP z hz).2 X hX).1 (I1.r2 x y f1 X hX')
      · rw [hstar hz hs] at hX; exact ((SP z hz).2 X hX).2.1 (I2.r2 x y f2 X hX')
      · rw [hstar hz hs] at hX; exact ((SP z hz).2 X hX).2.2 (I3.r2 x y f3 X hX')
      · rw [hstar hz' hs'] at hX'; exact ((SP z' hz').2 X hX').1 (I1.r2 u w e1 X hX)
      · exact I1.r3 u w x y e1 f1 hne X hX hX'
      · exact dis12 (I1.r2 u w e1 X hX) (I2.r2 x y f2 X hX')
      · exact dis13 (I1.r2 u w e1 X hX) (I3.r2 x y f3 X hX')
      · rw [hstar hz' hs'] at hX'; exact ((SP z' hz').2 X hX').2.1 (I2.r2 u w e2 X hX)
      · exact dis12 (I1.r2 x y f1 X hX') (I2.r2 u w e2 X hX)
      · exact I2.r3 u w x y e2 f2 hne X hX hX'
      · exact dis23 (I2.r2 u w e2 X hX) (I3.r2 x y f3 X hX')
      · rw [hstar hz' hs'] at hX'; exact ((SP z' hz').2 X hX').2.2 (I3.r2 u w e3 X hX)
      · exact dis13 (I1.r2 x y f1 X hX') (I3.r2 u w e3 X hX)
      · exact dis23 (I2.r2 x y f2 X hX') (I3.r2 u w e3 X hX)
      · exact I3.r3 u w x y e3 f3 hne X hX hX'
    · -- r4
      intro u w he x hx0 hX
      rcases RT.vs_nd.1 hx0 with rfl | hx | hx | hx <;>
        rcases gr_nd_cases he with ⟨z, hz, hs⟩ | e1 | e2 | e3
      · rw [hstar hz hs, hpv] at hX
        exact star_V hV (cor_of_in3 hpa hpb hpc hz) hX
      · rw [hpv] at hX; exact nV1 (I1.r2 u w e1 _ hX)
      · rw [hpv] at hX; exact nV2 (I2.r2 u w e2 _ hX)
      · rw [hpv] at hX; exact nV3 (I3.r2 u w e3 _ hX)
      · rw [hstar hz hs] at hX; exact ((SP z hz).2 _ hX).1 (I1.r1 x hx)
      · exact I1.r4 u w e1 x hx hX
      · exact dis12 (I1.r1 x hx) (I2.r2 u w e2 _ hX)
      · exact dis13 (I1.r1 x hx) (I3.r2 u w e3 _ hX)
      · rw [hstar hz hs] at hX; exact ((SP z hz).2 _ hX).2.1 (I2.r1 x hx)
      · exact dis12 (I1.r2 u w e1 _ hX) (I2.r1 x hx)
      · exact I2.r4 u w e2 x hx hX
      · exact dis23 (I2.r1 x hx) (I3.r2 u w e3 _ hX)
      · rw [hstar hz hs] at hX; exact ((SP z hz).2 _ hX).2.2 (I3.r1 x hx)
      · exact dis13 (I1.r2 u w e1 _ hX) (I3.r1 x hx)
      · exact dis23 (I2.r2 u w e2 _ hX) (I3.r1 x hx)
      · exact I3.r4 u w e3 x hx hX
    · -- r5
      intro x hx0 y hy0 hxy
      rcases RT.vs_nd.1 hx0 with rfl | hx | hx | hx <;>
        rcases RT.vs_nd.1 hy0 with rfl | hy | hy | hy
      · rfl
      · rw [hpv] at hxy; have h := I1.r1 y hy; rw [← hxy] at h; exact absurd h nV1
      · rw [hpv] at hxy; have h := I2.r1 y hy; rw [← hxy] at h; exact absurd h nV2
      · rw [hpv] at hxy; have h := I3.r1 y hy; rw [← hxy] at h; exact absurd h nV3
      · rw [hpv] at hxy; have h := I1.r1 x hx; rw [hxy] at h; exact absurd h nV1
      · exact I1.r5 x hx y hy hxy
      · have h := I2.r1 y hy; rw [← hxy] at h; exact (dis12 (I1.r1 x hx) h).elim
      · have h := I3.r1 y hy; rw [← hxy] at h; exact (dis13 (I1.r1 x hx) h).elim
      · rw [hpv] at hxy; have h := I2.r1 x hx; rw [hxy] at h; exact absurd h nV2
      · have h := I1.r1 y hy; rw [← hxy] at h; exact (dis12 h (I2.r1 x hx)).elim
      · exact I2.r5 x hx y hy hxy
      · have h := I3.r1 y hy; rw [← hxy] at h; exact (dis23 (I2.r1 x hx) h).elim
      · rw [hpv] at hxy; have h := I3.r1 x hx; rw [hxy] at h; exact absurd h nV3
      · have h := I1.r1 y hy; rw [← hxy] at h; exact (dis13 h (I3.r1 x hx)).elim
      · have h := I2.r1 y hy; rw [← hxy] at h; exact (dis23 h (I3.r1 x hx)).elim
      · exact I3.r5 x hx y hy hxy

theorem tri_cases {a b c u w : V} (h : (tri a b c).Adj u w) :
    s(u, w) = s(a, b) ∨ s(u, w) = s(b, c) ∨ s(u, w) = s(a, c) := by
  rw [tri_adj] at h
  obtain ⟨_, h⟩ := h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inl Sym2.eq_swap
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inl Sym2.eq_swap)
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inr Sym2.eq_swap)

/-- Q1: an Apollonian region-tree graph covering all vertices is planar. -/
theorem planar_GT {T : RT V} {a b c : V} (hwf : T.wf a b c)
    (hcov : ∀ u, u ∈ T.vs ∨ In3 a b c u) :
    RobertsonSeymour1986.GM5.IsPlanar (GT T a b c) := by
  obtain ⟨hab, hbc, hac⟩ := RT.wf_ne hwf
  obtain ⟨oa, ob, oc⟩ := RT.wf_out hwf
  set A : ℝ × ℝ := (0, 0) with hA
  set B : ℝ × ℝ := (1, 0) with hB
  set C : ℝ × ℝ := (0, 1) with hC
  have h0 : 0 < orient A B C := by simp only [hA, hB, hC, orient]; norm_num
  let p : V → ℝ × ℝ := fun u =>
    if u = a then A else if u = b then B else if u = c then C else T.pl A B C u
  have hpa : p a = A := by simp [p]
  have hpb : p b = B := by simp [p, Ne.symm hab]
  have hpc : p c = C := by simp [p, Ne.symm hac, Ne.symm hbc]
  have hpl : ∀ u ∈ T.vs, p u = T.pl A B C u := by
    intro u hu
    have h1 : u ≠ a := fun e => oa (e ▸ hu)
    have h2 : u ≠ b := fun e => ob (e ▸ hu)
    have h3 : u ≠ c := fun e => oc (e ▸ hu)
    simp [p, h1, h2, h3]
  have R := reg_ok T a b c A B C p hwf h0 hpa hpb hpc hpl
  have hcor := fun (z : V) (hz : In3 a b c z) => cor_of_in3 hpa hpb hpc hz
  obtain ⟨nAB, nBC, nAC⟩ := cor_ne h0
  -- open sides of the outer triangle
  have hside : ∀ {u w : V}, (tri a b c).Adj u w →
      (OP (p u) (p w) = OP A B ∨ OP (p u) (p w) = OP B C ∨ OP (p u) (p w) = OP A C) := by
    intro u w h
    rcases tri_cases h with hs | hs | hs
    · left; rw [OP_of_sym2 p hs, hpa, hpb]
    · right; left; rw [OP_of_sym2 p hs, hpb, hpc]
    · right; right; rw [OP_of_sym2 p hs, hpa, hpc]
  have side_out : ∀ {u w : V}, (tri a b c).Adj u w → ∀ X ∈ OP (p u) (p w), ¬ Ins A B C X := by
    intro u w h X hX hI
    rcases hside h with e | e | e <;> rw [e] at hX
    · have := side_AB hX; have := hI.1; linarith
    · have := side_BC hX; have := hI.2.1; linarith
    · have := side_CA hX; have := hI.2.2; linarith
  apply planar_of_straight (GT T a b c) p
  · -- injectivity
    intro x y hxy
    rcases hcov x with hx | hx <;> rcases hcov y with hy | hy
    · exact R.r5 x hx y hy hxy
    · have h := R.r1 x hx; rw [hxy] at h; exact absurd h (not_ins_cor (hcor _ hy))
    · have h := R.r1 y hy; rw [← hxy] at h; exact absurd h (not_ins_cor (hcor _ hx))
    · exact in3_inj h0 hpa hpb hpc hx hy hxy
  · -- disjoint open edges
    intro u w x y he hf hne X hX hX'
    simp only [GT, SimpleGraph.sup_adj] at he hf
    rcases he with he | he <;> rcases hf with hf | hf
    · -- two sides
      have hAB : ∀ Y ∈ OP A B, Y ∉ OP B C := by
        intro Y h1 h2
        obtain ⟨t, t0, _, rfl⟩ := h2
        have := side_AB h1
        rw [orient_seg, orient_abb] at this
        have := mul_pos t0 h0; linarith
      have hAC : ∀ Y ∈ OP A B, Y ∉ OP A C := by
        intro Y h1 h2
        obtain ⟨t, t0, _, rfl⟩ := h2
        have := side_AB h1
        rw [orient_seg, orient_aba] at this
        have := mul_pos t0 h0; linarith
      have hBC : ∀ Y ∈ OP B C, Y ∉ OP A C := by
        intro Y h1 h2
        obtain ⟨t, _, t1, rfl⟩ := h2
        have := side_BC h1
        rw [orient_seg, orient_abb, orient_cyc] at this
        have := mul_pos (sub_pos.2 t1) h0; linarith
      rcases tri_cases he with s1 | s1 | s1 <;> rcases tri_cases hf with s2 | s2 | s2
      all_goals first
        | exact hne (s1.trans s2.symm)
        | skip
      all_goals rw [OP_of_sym2 p s1] at hX; rw [OP_of_sym2 p s2] at hX'
      all_goals simp only [hpa, hpb, hpc] at hX hX'
      · exact hAB X hX hX'
      · exact hAC X hX hX'
      · exact hAB X hX' hX
      · exact hBC X hX hX'
      · exact hAC X hX' hX
      · exact hBC X hX' hX
    · exact side_out he X hX (R.r2 x y hf X hX')
    · exact side_out hf X hX' (R.r2 u w he X hX)
    · exact R.r3 u w x y he hf hne X hX hX'
  · -- open edges avoid vertices
    intro u w he x hX
    simp only [GT, SimpleGraph.sup_adj] at he
    rcases he with he | he
    · rcases hcov x with hx | hx
      · exact side_out he _ hX (R.r1 x hx)
      · -- a corner on an open side
        rcases tri_cases he with s1 | s1 | s1 <;> rw [OP_of_sym2 p s1] at hX <;>
          simp only [hpa, hpb, hpc] at hX <;>
          rcases hx with rfl | rfl | rfl <;> simp only [hpa, hpb, hpc] at hX
        all_goals obtain ⟨t, t0, t1, ht⟩ := hX
        · have := segP_inj nAB (ht.symm.trans (segP_zero A B).symm); linarith
        · have := segP_inj nAB (ht.symm.trans (segP_one A B).symm); linarith
        · have e := congrArg (orient A B) ht
          rw [orient_seg, orient_aba, orient_abb] at e; linarith
        · have e := congrArg (orient B C) ht
          rw [orient_seg, orient_abb, orient_aba, orient_cyc] at e; linarith
        · have := segP_inj nBC (ht.symm.trans (segP_zero B C).symm); linarith
        · have := segP_inj nBC (ht.symm.trans (segP_one B C).symm); linarith
        · have := segP_inj nAC (ht.symm.trans (segP_zero A C).symm); linarith
        · have e := congrArg (orient C A) ht
          rw [orient_seg, orient_abb, orient_aba, orient_cyc, orient_cyc] at e; linarith
        · have := segP_inj nAC (ht.symm.trans (segP_one A C).symm); linarith
    · rcases hcov x with hx | hx
      · exact R.r4 u w he x hx hX
      · exact not_ins_cor (hcor _ hx) (R.r2 u w he _ hX)

end SLrt

end PQL5

/-! Q2 (8100c3d9): treewidth ≤ 3 and no `K₃,₃` minor imply planarity
(KV completion `childC2_holds` + `rt_of_TT` + the centroid drawing `planar_GT`). -/

namespace PQL5

section Q2

theorem isPlanar_mono {W : Type} {G H : SimpleGraph W} (hle : G ≤ H)
    (hH : RobertsonSeymour1986.GM5.IsPlanar H) : RobertsonSeymour1986.GM5.IsPlanar G := by
  obtain ⟨D⟩ := hH
  exact ⟨{ vertex := D.vertex
           vertex_injective := D.vertex_injective
           arc := fun h => D.arc (hle h)
           arc_injective := fun h => D.arc_injective (hle h)
           arc_reverse := fun h => D.arc_reverse (hle h)
           arc_avoids_vertices := fun h => D.arc_avoids_vertices (hle h)
           arcs_meet_only_at_endpoints := fun h k => D.arcs_meet_only_at_endpoints (hle h) (hle k) }⟩

theorem planar_small {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    (hc : Fintype.card W ≤ 2) : RobertsonSeymour1986.GM5.IsPlanar G := by
  let e := Fintype.equivFin W
  let p : W → ℝ × ℝ := fun v => (((e v : ℕ) : ℝ), 0)
  have hinj : Function.Injective p := by
    intro v w h
    have h1 := congrArg Prod.fst h
    simp only [p, Nat.cast_inj] at h1
    exact e.injective (Fin.ext h1)
  have two : ∀ u w z : W, u ≠ w → z = u ∨ z = w := by
    intro u w z huw
    by_contra hz
    push_neg at hz
    have h3 : ({u, w, z} : Finset W).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hz.2)]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨huw, fun h => hz.1 h.symm⟩
    have := Finset.card_le_univ ({u, w, z} : Finset W)
    omega
  apply planar_of_straight G p hinj
  · intro u w x y h k hne
    exfalso
    apply hne
    have huw := G.ne_of_adj h
    have hxy := G.ne_of_adj k
    have hx' := two u w x huw
    have hy' := two u w y huw
    rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
    · exact absurd rfl hxy
    · rfl
    · exact Sym2.eq_swap
    · exact absurd rfl hxy
  · intro u w h x hx
    have huw : p u ≠ p w := fun e' => G.ne_of_adj h (hinj e')
    obtain ⟨t, t0, t1, ht⟩ := hx
    rcases two u w x (G.ne_of_adj h) with rfl | rfl
    · have := segP_inj huw (ht.symm.trans (segP_zero _ _).symm); linarith
    · have := segP_inj huw (ht.symm.trans (segP_one _ _).symm); linarith

/-- Q2: a graph of treewidth at most three with no `K₃,₃` minor is planar. -/
theorem planar_of_tw3_noK33 {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    (htw : RobertsonSeymour1986.GM5.TreewidthLE G 3)
    (hK : ¬ RobertsonSeymour1986.GM5.IsMinor (completeBipartiteGraph (Fin 3) (Fin 3)) G) :
    RobertsonSeymour1986.GM5.IsPlanar G := by
  by_cases hc : Fintype.card W ≤ 2
  · exact planar_small G hc
  · obtain ⟨H, hle, hT, hC⟩ := childC2_holds Finset.univ G
      (fun _ _ _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩)
      (by rw [Finset.card_univ]; omega) htw hK
    obtain ⟨x, y, z, T, hw, hH, hcov⟩ := rt_of_TT hT hC
    apply isPlanar_mono hle
    rw [hH]
    exact planar_GT hw hcov

end Q2

end PQL5

open PlanarQueue.Planar in
theorem solution {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    (htw : RobertsonSeymour1986.GM5.TreewidthLE G 3)
    (hK : ¬ RobertsonSeymour1986.GM5.IsMinor (completeBipartiteGraph (Fin 3) (Fin 3)) G) :
    IsPlanar G := by
  exact PQL5.planar_of_tw3_noK33 G htw hK
