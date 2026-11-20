-- Prove2me | solution 1 for OPG37271.suppress_deg2_bridgeless_cubic
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T06:16:21.900864+00:00
-- url     : https://prove2.me/submissions/60b2acd6-8520-444c-b049-763fe805aad6

import Definitions.Def_opg37271_star_edge_coloring
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card

set_option autoImplicit false

open OPG37271

universe u

private lemma enat_two_ne_three : (2 : ℕ∞) ≠ 3 := by decide

/-- The simple graph on degree-3 vertices `V₃ := {v : V // (G.neighborSet v).encard = 3}` obtained
by suppressing all degree-2 vertices of `G`. -/
private def suppressedGraph {V : Type u} (G : SimpleGraph V) :
    SimpleGraph {v : V // (G.neighborSet v).encard = 3} where
  Adj u w := u ≠ w ∧
    (G.Adj u.1 w.1 ∨ ∃ z : V, (G.neighborSet z).encard = 2 ∧ G.Adj u.1 z ∧ G.Adj w.1 z)
  symm := ⟨by
    intro u w ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with hg | ⟨z, hz2, huz, hwz⟩
    · exact Or.inl hg.symm
    · exact Or.inr ⟨z, hz2, hwz, huz⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

/-- Helper: given `(G.neighborSet z).encard = 2` and `G.Adj u z`, there is a unique other neighbor
`w ≠ u` of `z` in `G`. -/
private lemma deg2_other_neighbor {V : Type u} {G : SimpleGraph V} {u z : V}
    (hz2 : (G.neighborSet z).encard = 2) (huz : G.Adj u z) :
    ∃ w : V, G.Adj z w ∧ w ≠ u ∧ ∀ y : V, G.Adj z y → (y = u ∨ y = w) := by
  rw [Set.encard_eq_two] at hz2
  obtain ⟨a, b, hab, hset⟩ := hz2
  have hmem : ∀ y : V, G.Adj z y ↔ y = a ∨ y = b := by
    intro y
    change y ∈ G.neighborSet z ↔ y = a ∨ y = b
    rw [hset]
    simp
  rcases (hmem u).mp huz.symm with rfl | rfl
  · refine ⟨b, (hmem b).mpr (Or.inr rfl), hab.symm, fun y hy => (hmem y).mp hy⟩
  · refine ⟨a, (hmem a).mpr (Or.inl rfl), hab, fun y hy => ?_⟩
    rcases (hmem y).mp hy with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- Helper translating a simple path `p` in a subgraph `G_sub ≤ G` between degree-3 vertices
into reachability in `(suppressedGraph G).deleteEdges {s(u, w)}`. -/
private lemma suppressed_reachable_of_path
    {V : Type u} {G G_sub : SimpleGraph V} (hsub : G_sub ≤ G)
    (hdeg : ∀ v : V, (G.neighborSet v).encard = 2 ∨ (G.neighborSet v).encard = 3)
    (hnoadj2 : ∀ u v : V, G.Adj u v → ¬ ((G.neighborSet u).encard ≤ 2 ∧ (G.neighborSet v).encard ≤ 2))
    (u w : {v : V // (G.neighborSet v).encard = 3})
    {x y : V} (hx3 : (G.neighborSet x).encard = 3) (hy3 : (G.neighborSet y).encard = 3)
    (p : G_sub.Walk x y) (hp : p.IsPath)
    (hno_direct : ∀ a b : V, G_sub.Adj a b →
      (G.neighborSet a).encard = 3 → (G.neighborSet b).encard = 3 →
      s(a, b) ≠ s(u.1, w.1))
    (hno_via2 : ∀ a z b : V, z ∈ p.support →
      (G.neighborSet z).encard = 2 → G.Adj a z → G.Adj z b → a ≠ b →
      s(a, b) ≠ s(u.1, w.1)) :
    ((suppressedGraph G).deleteEdges {s(u, w)}).Reachable ⟨x, hx3⟩ ⟨y, hy3⟩ := by
  -- Strong induction on walk length `n = p.length`
  suffices hlen : ∀ (n : ℕ) {x : V} (hx3 : (G.neighborSet x).encard = 3)
      (p : G_sub.Walk x y), p.length = n → p.IsPath →
      (∀ a z b : V, z ∈ p.support →
        (G.neighborSet z).encard = 2 → G.Adj a z → G.Adj z b → a ≠ b →
        s(a, b) ≠ s(u.1, w.1)) →
      ((suppressedGraph G).deleteEdges {s(u, w)}).Reachable ⟨x, hx3⟩ ⟨y, hy3⟩ from
    hlen p.length hx3 p rfl hp hno_via2
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro x hx3 p hplen hp hvia
    cases p with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons _ v₁ _ hxv1 p₁ =>
      have hsup_nd : (x :: p₁.support).Nodup := by
        simpa [SimpleGraph.Walk.support_cons] using hp.support_nodup
      have hx_not_mem : x ∉ p₁.support := (List.nodup_cons.mp hsup_nd).1
      have hp1_path : p₁.IsPath := SimpleGraph.Walk.IsPath.mk' (List.nodup_cons.mp hsup_nd).2
      have hxv1_G : G.Adj x v₁ := hsub hxv1
      have hvia1 : ∀ a z b : V, z ∈ p₁.support →
          (G.neighborSet z).encard = 2 → G.Adj a z → G.Adj z b → a ≠ b →
          s(a, b) ≠ s(u.1, w.1) := by
        intro a z b hz hz2 haz hzb hab
        exact hvia a z b (by simp [SimpleGraph.Walk.support_cons, hz]) hz2 haz hzb hab
      rcases hdeg v₁ with hv1_2 | hv1_3
      · -- `v₁` has degree 2: `p₁` cannot be `nil` since `y` has degree 3!
        cases p₁ with
        | nil =>
          exact absurd (hv1_2.symm.trans hy3) enat_two_ne_three
        | @cons _ v₂ _ hv12 p₂ =>
          have hv12_G : G.Adj v₁ v₂ := hsub hv12
          have hv2_3 : (G.neighborSet v₂).encard = 3 := by
            rcases hdeg v₂ with hv2_2 | hv2_3
            · exfalso
              exact hnoadj2 v₁ v₂ hv12_G ⟨le_of_eq hv1_2, le_of_eq hv2_2⟩
            · exact hv2_3
          have hxv2_ne : x ≠ v₂ := by
            intro heq
            subst heq
            exact hx_not_mem (by simp [SimpleGraph.Walk.support_cons])
          have hadj_supp : (suppressedGraph G).Adj ⟨x, hx3⟩ ⟨v₂, hv2_3⟩ :=
            ⟨fun h => hxv2_ne (congrArg Subtype.val h),
             Or.inr ⟨v₁, hv1_2, hxv1_G, hv12_G.symm⟩⟩
          have hne_uw : s((⟨x, hx3⟩ : {v : V // (G.neighborSet v).encard = 3}), ⟨v₂, hv2_3⟩) ≠ s(u, w) := by
            intro hsym
            have hsym_val : s(x, v₂) = s(u.1, w.1) := by
              rw [Sym2.eq_iff] at hsym ⊢
              rcases hsym with ⟨hA, hB⟩ | ⟨hA, hB⟩
              · exact Or.inl ⟨congrArg Subtype.val hA, congrArg Subtype.val hB⟩
              · exact Or.inr ⟨congrArg Subtype.val hA, congrArg Subtype.val hB⟩
            exact hvia x v₁ v₂ (by simp [SimpleGraph.Walk.support_cons])
              hv1_2 hxv1_G hv12_G hxv2_ne hsym_val
          have hadj_del : ((suppressedGraph G).deleteEdges {s(u, w)}).Adj ⟨x, hx3⟩ ⟨v₂, hv2_3⟩ := by
            rw [SimpleGraph.deleteEdges_adj]
            exact ⟨hadj_supp, by simp [hne_uw]⟩
          have hp2_path : p₂.IsPath := by
            have hnd2 : (v₁ :: p₂.support).Nodup := by
              simpa [SimpleGraph.Walk.support_cons] using hp1_path.support_nodup
            exact SimpleGraph.Walk.IsPath.mk' (List.nodup_cons.mp hnd2).2
          have hvia2 : ∀ a z b : V, z ∈ p₂.support →
              (G.neighborSet z).encard = 2 → G.Adj a z → G.Adj z b → a ≠ b →
              s(a, b) ≠ s(u.1, w.1) := by
            intro a z b hz hz2 haz hzb hab
            exact hvia1 a z b (by simp [SimpleGraph.Walk.support_cons, hz]) hz2 haz hzb hab
          have hlen_lt : p₂.length < n := by
            simp only [SimpleGraph.Walk.length_cons] at hplen
            omega
          exact SimpleGraph.Adj.reachable hadj_del |>.trans
            (ih p₂.length hlen_lt hv2_3 p₂ rfl hp2_path hvia2)
      · -- `v₁` has degree 3: direct step `(x, v₁)` in `suppressedGraph G`!
        have hadj_supp : (suppressedGraph G).Adj ⟨x, hx3⟩ ⟨v₁, hv1_3⟩ :=
          ⟨fun h => hxv1_G.ne (congrArg Subtype.val h), Or.inl hxv1_G⟩
        have hne_uw : s((⟨x, hx3⟩ : {v : V // (G.neighborSet v).encard = 3}), ⟨v₁, hv1_3⟩) ≠ s(u, w) := by
          intro hsym
          have hsym_val : s(x, v₁) = s(u.1, w.1) := by
            rw [Sym2.eq_iff] at hsym ⊢
            rcases hsym with ⟨hA, hB⟩ | ⟨hA, hB⟩
            · exact Or.inl ⟨congrArg Subtype.val hA, congrArg Subtype.val hB⟩
            · exact Or.inr ⟨congrArg Subtype.val hA, congrArg Subtype.val hB⟩
          exact hno_direct x v₁ hxv1 hx3 hv1_3 hsym_val
        have hadj_del : ((suppressedGraph G).deleteEdges {s(u, w)}).Adj ⟨x, hx3⟩ ⟨v₁, hv1_3⟩ := by
          rw [SimpleGraph.deleteEdges_adj]
          exact ⟨hadj_supp, by simp [hne_uw]⟩
        have hlen_lt : p₁.length < n := by
          simp only [SimpleGraph.Walk.length_cons] at hplen
          omega
        exact SimpleGraph.Adj.reachable hadj_del |>.trans
          (ih p₁.length hlen_lt hv1_3 p₁ rfl hp1_path hvia1)

/-- **DMS Theorem 4.1(a), Degree-2 Suppression Theorem (`suppress_deg2_bridgeless_cubic`)**:
Suppressing all degree-2 vertices in a finite bridgeless `{2, 3}`-graph `G` with no adjacent
degree-2 vertices, no triangle containing a degree-2 vertex, and no 4-cycle with opposite
degree-2 vertices produces a **3-regular**, **bridgeless** simple graph `suppressedGraph G`
on `V₃ := {v : V // (G.neighborSet v).encard = 3}`. -/
private theorem suppress_deg2_bridgeless_cubic_priv
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hdeg : ∀ v : V, (G.neighborSet v).encard = 2 ∨ (G.neighborSet v).encard = 3)
    (hbridge : ∀ u v : V, G.Adj u v → (G.deleteEdges {s(u, v)}).Reachable u v)
    (hnoadj2 : ∀ u v : V, G.Adj u v →
      ¬ ((G.neighborSet u).encard ≤ 2 ∧ (G.neighborSet v).encard ≤ 2))
    (hnotri2 : ∀ x y z : V, G.Adj x z → G.Adj y z → G.Adj x y →
      ¬ (G.neighborSet z).encard ≤ 2)
    (hno4cyc2 : ∀ z₁ z₂ x y : V, z₁ ≠ z₂ → x ≠ y →
      (G.neighborSet z₁).encard = 2 → (G.neighborSet z₂).encard = 2 →
      G.Adj x z₁ → G.Adj y z₁ → G.Adj x z₂ → G.Adj y z₂ → False) :
    (∀ u : {v : V // (G.neighborSet v).encard = 3},
      ((suppressedGraph G).neighborSet u).encard = 3) ∧
    (∀ u w : {v : V // (G.neighborSet v).encard = 3},
      (suppressedGraph G).Adj u w →
      ((suppressedGraph G).deleteEdges {s(u, w)}).Reachable u w) := by
  classical
  let V₃ := {v : V // (G.neighborSet v).encard = 3}
  let G' := suppressedGraph G
  refine ⟨?_, ?_⟩
  · -- Part (A): `G'` is 3-regular via an explicit bijection `G.neighborSet u.1 ≃ G'.neighborSet u`.
    intro u
    -- Map each `y ∈ G.neighborSet u.1` to `y` if `deg(y) = 3`, else to `z`'s other neighbor in `G`.
    have hmap_exists : ∀ y : G.neighborSet u.1, ∃ w : G'.neighborSet u,
        (((G.neighborSet y.1).encard = 3 ∧ w.1.1 = y.1) ∨
         ((G.neighborSet y.1).encard = 2 ∧ G.Adj w.1.1 y.1)) := by
      intro ⟨y, hy⟩
      change G.Adj u.1 y at hy
      rcases hdeg y with hy2 | hy3
      · obtain ⟨w_val, hyw, hwu, _⟩ := deg2_other_neighbor hy2 hy
        have hw3 : (G.neighborSet w_val).encard = 3 := by
          rcases hdeg w_val with hw2 | hw3
          · exfalso
            exact hnoadj2 y w_val hyw ⟨le_of_eq hy2, le_of_eq hw2⟩
          · exact hw3
        let w : V₃ := ⟨w_val, hw3⟩
        have huw_adj : G'.Adj u w :=
          ⟨fun h => hwu (congrArg Subtype.val h).symm, Or.inr ⟨y, hy2, hy, hyw.symm⟩⟩
        exact ⟨⟨w, huw_adj⟩, Or.inr ⟨hy2, hyw.symm⟩⟩
      · let w : V₃ := ⟨y, hy3⟩
        have huw_adj : G'.Adj u w :=
          ⟨fun h => hy.ne (congrArg Subtype.val h), Or.inl hy⟩
        exact ⟨⟨w, huw_adj⟩, Or.inl ⟨hy3, rfl⟩⟩
    let φ : G.neighborSet u.1 → G'.neighborSet u := fun y => Classical.choose (hmap_exists y)
    have hφ_spec : ∀ y : G.neighborSet u.1,
        (((G.neighborSet y.1).encard = 3 ∧ (φ y).1.1 = y.1) ∨
         ((G.neighborSet y.1).encard = 2 ∧ G.Adj (φ y).1.1 y.1)) :=
      fun y => Classical.choose_spec (hmap_exists y)
    have hφ_inj : Function.Injective φ := by
      intro ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩ heq
      change G.Adj u.1 y₁ at hy₁
      change G.Adj u.1 y₂ at hy₂
      let w : V₃ := (φ ⟨y₁, hy₁⟩).1
      have hw_ne_u : u.1 ≠ w.1 := fun h => (φ ⟨y₁, hy₁⟩).2.1 (Subtype.ext h)
      have hs1 := hφ_spec ⟨y₁, hy₁⟩
      have hs2 := hφ_spec ⟨y₂, hy₂⟩
      rw [← heq] at hs2
      apply Subtype.ext
      rcases hs1 with ⟨_, hw1⟩ | ⟨hy1_2, hwy1⟩ <;>
        rcases hs2 with ⟨_, hw2⟩ | ⟨hy2_2, hwy2⟩
      · exact hw1.symm.trans hw2
      · exfalso
        have htri : G.Adj u.1 w.1 := by
          change w.1 = y₁ at hw1
          rwa [hw1]
        exact hnotri2 u.1 w.1 y₂ hy₂ hwy2 htri (le_of_eq hy2_2)
      · exfalso
        have htri : G.Adj u.1 w.1 := by
          change w.1 = y₂ at hw2
          rwa [hw2]
        exact hnotri2 u.1 w.1 y₁ hy₁ hwy1 htri (le_of_eq hy1_2)
      · by_contra hne_y
        exact hno4cyc2 y₁ y₂ u.1 w.1 hne_y hw_ne_u hy1_2 hy2_2 hy₁ hwy1 hy₂ hwy2
    have hφ_surj : Function.Surjective φ := by
      rintro ⟨w, huw_ne, hdirect | ⟨z, hz2, huz, hwz⟩⟩
      · refine ⟨⟨w.1, hdirect⟩, Subtype.ext (Subtype.ext ?_)⟩
        rcases hφ_spec ⟨w.1, hdirect⟩ with ⟨_, h1⟩ | ⟨hz2', _⟩
        · exact h1
        · exact absurd (hz2'.symm.trans w.2) enat_two_ne_three
      · refine ⟨⟨z, huz⟩, Subtype.ext (Subtype.ext ?_)⟩
        rcases hφ_spec ⟨z, huz⟩ with ⟨hz3, _⟩ | ⟨_, hφz⟩
        · exact absurd (hz2.symm.trans hz3) enat_two_ne_three
        · obtain ⟨w', hzw', hw'u, huniq⟩ := deg2_other_neighbor hz2 huz
          have h1 : (φ ⟨z, huz⟩).1.1 = w' := by
            rcases huniq _ hφz.symm with h_eq_u | h_eq_w'
            · exact absurd (Subtype.ext h_eq_u.symm) (φ ⟨z, huz⟩).2.1
            · exact h_eq_w'
          have h2 : w.1 = w' := by
            rcases huniq w.1 hwz.symm with h_eq_u | h_eq_w'
            · exact absurd (Subtype.ext h_eq_u.symm) huw_ne
            · exact h_eq_w'
          exact h1.trans h2.symm
    have heqv : G.neighborSet u.1 ≃ G'.neighborSet u :=
      Equiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩
    rw [← Set.encard_congr heqv]
    exact u.2
  · -- Part (B): `G'` is bridgeless!
    intro u w ⟨huw_ne, hkind⟩
    have huw_val_ne : u.1 ≠ w.1 := fun h => huw_ne (Subtype.ext h)
    by_cases hdirect : G.Adj u.1 w.1
    · -- Mechanism 1: `G.Adj u.1 w.1`. Take a simple path in `G.deleteEdges {s(u.1, w.1)}`.
      refine (hbridge u.1 w.1 hdirect).elim_path (fun ⟨p, hp⟩ => ?_)
      apply suppressed_reachable_of_path
        (SimpleGraph.deleteEdges_le {s(u.1, w.1)}) hdeg hnoadj2 u w u.2 w.2 p hp
      · intro a b hab _ _
        rw [SimpleGraph.deleteEdges_adj] at hab
        simpa using hab.2
      · intro a z b _ hz2 haz hzb _ hsym
        rw [Sym2.eq_iff] at hsym
        rcases hsym with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hnotri2 u.1 w.1 z haz hzb.symm hdirect (le_of_eq hz2)
        · exact hnotri2 u.1 w.1 z hzb.symm haz hdirect (le_of_eq hz2)
    · -- Mechanism 2: `¬ G.Adj u.1 w.1`, so `∃ z₀` of degree 2 with `G.Adj u.1 z₀` and `G.Adj w.1 z₀`.
      rcases hkind with hg | ⟨z₀, hz₀_2, huz₀, hwz₀⟩
      · exact absurd hg hdirect
      -- Take a simple path `q` in `G.deleteEdges {s(z₀, u.1)}` FROM `z₀` TO `u.1`!
      have hreach_z0_u : (G.deleteEdges {s(z₀, u.1)}).Reachable z₀ u.1 := by
        simpa [Sym2.eq_swap] using (hbridge u.1 z₀ huz₀).symm
      refine hreach_z0_u.elim_path (fun ⟨q, hq⟩ => ?_)
      cases q with
      | nil =>
        exact absurd (hz₀_2.symm.trans u.2) enat_two_ne_three
      | @cons _ v₁ _ hz0_v1 q_tail =>
        rw [SimpleGraph.deleteEdges_adj] at hz0_v1
        obtain ⟨hz0_v1_G, hnot_zu⟩ := hz0_v1
        have hv1_ne_u : v₁ ≠ u.1 := by
          intro rfl
          exact hnot_zu (Set.mem_singleton _)
        -- Since `z₀` has degree 2 and neighbors `u.1, w.1`, `v₁ ≠ u.1` forces `v₁ = w.1`!
        obtain ⟨w', _, _, huniq⟩ := deg2_other_neighbor hz₀_2 huz₀
        have hw'_eq : w.1 = w' := by
          rcases huniq w.1 hwz₀.symm with h_eq_u | h_eq_w'
          · exact absurd h_eq_u.symm huw_val_ne
          · exact h_eq_w'
        have hv1_eq_w : v₁ = w.1 := by
          rcases huniq v₁ hz0_v1_G with h_eq_u | h_eq_w'
          · exact absurd h_eq_u hv1_ne_u
          · exact h_eq_w'.trans hw'_eq.symm
        subst hv1_eq_w
        -- `q_tail` is a simple path from `w.1` to `u.1` whose support does NOT contain `z₀`!
        have hsup_nd : (z₀ :: q_tail.support).Nodup := by
          simpa [SimpleGraph.Walk.support_cons] using hq.support_nodup
        have hz0_not_mem : z₀ ∉ q_tail.support := (List.nodup_cons.mp hsup_nd).1
        have hq_tail_path : q_tail.IsPath :=
          SimpleGraph.Walk.IsPath.mk' (List.nodup_cons.mp hsup_nd).2
        have hreach_wu : ((suppressedGraph G).deleteEdges {s(u, w)}).Reachable w u := by
          have hreach' := suppressed_reachable_of_path
            (SimpleGraph.deleteEdges_le {s(z₀, u.1)}) hdeg hnoadj2 w u w.2 u.2 q_tail hq_tail_path
            (by
              intro a b hab _ _ hsym
              have hab_G : G.Adj a b := (SimpleGraph.deleteEdges_adj.mp hab).1
              rw [Sym2.eq_iff] at hsym
              rcases hsym with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact hdirect hab_G.symm
              · exact hdirect hab_G)
            (by
              intro a z b hz_mem hz2 haz hzb _ hsym
              have hz_ne_z0 : z₀ ≠ z := fun h => hz0_not_mem (h ▸ hz_mem)
              rw [Sym2.eq_iff] at hsym
              rcases hsym with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact hno4cyc2 z₀ z u.1 w.1 hz_ne_z0 huw_val_ne hz₀_2 hz2
                  huz₀ hwz₀ hzb.symm haz
              · exact hno4cyc2 z₀ z u.1 w.1 hz_ne_z0 huw_val_ne hz₀_2 hz2
                  huz₀ hwz₀ haz hzb.symm)
          simpa [Sym2.eq_swap] using hreach'
        exact hreach_wu.symm


theorem solution
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hdeg : ∀ v : V, (G.neighborSet v).encard = 2 ∨ (G.neighborSet v).encard = 3)
    (hbridge : ∀ u v : V, G.Adj u v → (G.deleteEdges {s(u, v)}).Reachable u v)
    (hnoadj2 : ∀ u v : V, G.Adj u v →
      ¬ ((G.neighborSet u).encard ≤ 2 ∧ (G.neighborSet v).encard ≤ 2))
    (hnotri2 : ∀ x y z : V, G.Adj x z → G.Adj y z → G.Adj x y →
      ¬ (G.neighborSet z).encard ≤ 2)
    (hno4cyc2 : ∀ z₁ z₂ x y : V, z₁ ≠ z₂ → x ≠ y →
      (G.neighborSet z₁).encard = 2 → (G.neighborSet z₂).encard = 2 →
      G.Adj x z₁ → G.Adj y z₁ → G.Adj x z₂ → G.Adj y z₂ → False) :
    ∃ G' : SimpleGraph {v : V // (G.neighborSet v).encard = 3},
      (∀ u w : {v : V // (G.neighborSet v).encard = 3},
        G'.Adj u w ↔ u ≠ w ∧
          (G.Adj u.1 w.1 ∨ ∃ z : V, (G.neighborSet z).encard = 2 ∧ G.Adj u.1 z ∧ G.Adj w.1 z)) ∧
      (∀ u : {v : V // (G.neighborSet v).encard = 3},
        (G'.neighborSet u).encard = 3) ∧
      (∀ u w : {v : V // (G.neighborSet v).encard = 3},
        G'.Adj u w → (G'.deleteEdges {s(u, w)}).Reachable u w) :=
  ⟨suppressedGraph G, fun _ _ => Iff.rfl,
    suppress_deg2_bridgeless_cubic_priv G hdeg hbridge hnoadj2 hnotri2 hno4cyc2⟩

