-- Prove2me | solution 1 for TaitTobin.Outerplanar.subgraph_fan_of_universal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T16:10:07.741596+00:00
-- url     : https://prove2.me/submissions/e1028219-d620-4551-8407-0806d7bd10cc

import Mathlib
import Definitions.Def_TaitTobin_Outerplanar_Setting
import Theorems.Thm_TaitTobin_Outerplanar_outerplanar_facts

set_option autoImplicit false

section ofhelpers

open RobertsonSeymour1986.GM5 TaitTobin.Outerplanar

/-- the drawing of `G.comap g` obtained from a drawing of `G` (injective `g`) -/
def ofComapDraw {V W : Type} {G : SimpleGraph W} (g : V → W) (hg : Function.Injective g)
    (D : PlaneDrawing G) : PlaneDrawing (G.comap g) where
  vertex v := D.vertex (g v)
  vertex_injective := D.vertex_injective.comp hg
  arc h := D.arc h
  arc_injective h := D.arc_injective h
  arc_reverse h := D.arc_reverse h
  arc_avoids_vertices := by
    intro v w h t x hx
    rcases D.arc_avoids_vertices h t (g x) hx with h1 | h1
    · exact Or.inl (hg h1)
    · exact Or.inr (hg h1)
  arcs_meet_only_at_endpoints := by
    intro v w x y h k s t hst
    rcases D.arcs_meet_only_at_endpoints h k s t hst with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h1
    · exact Or.inl ⟨hg h1, hg h2⟩
    · exact Or.inr (Or.inl ⟨hg h1, hg h2⟩)
    · exact Or.inr (Or.inr h1)

theorem of_comap_img {V W : Type} {G : SimpleGraph W} (g : V → W) (hg : Function.Injective g)
    (D : PlaneDrawing G) : drawingImage (ofComapDraw g hg D) ⊆ drawingImage D := by
  intro z hz
  rcases hz with ⟨v, rfl⟩ | hz
  · exact Or.inl ⟨g v, rfl⟩
  · simp only [Set.mem_iUnion, Set.mem_range] at hz
    obtain ⟨a, b, h, t, rfl⟩ := hz
    refine Or.inr ?_
    simp only [Set.mem_iUnion, Set.mem_range]
    exact ⟨g a, g b, h, t, rfl⟩

/-- outerplanarity pulls back along an injective map of vertices -/
theorem of_comap {V W : Type} (G : SimpleGraph W) (g : V → W)
    (hg : Function.Injective g) (hG : IsOuterplanar G) : IsOuterplanar (G.comap g) := by
  obtain ⟨D, hD⟩ := hG
  refine ⟨ofComapDraw g hg D, fun v => ?_⟩
  have hsub := of_comap_img g hg D
  have hface : outerFace D ⊆ outerFace (ofComapDraw g hg D) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := hp
    refine ⟨fun h => hp1 (hsub h), fun hb => hp2 ?_⟩
    exact hb.subset (connectedComponentIn_mono p (Set.compl_subset_compl.2 hsub))
  exact closure_mono hface (hD (g v))

theorem of_inj5 {n : ℕ} (p q a b c : Fin n) (hpq : p ≠ q) (hap : a ≠ p) (haq : a ≠ q)
    (hbp : b ≠ p) (hbq : b ≠ q) (hcp : c ≠ p) (hcq : c ≠ q) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    Function.Injective (Sum.elim ![p, q] ![a, b, c] : Fin 2 ⊕ Fin 3 → Fin n) := by
  intro s t h
  rcases s with i | j <;> rcases t with k | l <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
  · fin_cases i <;> fin_cases k <;> simp_all [eq_comm]
  · fin_cases i <;> fin_cases l <;> simp_all [eq_comm]
  · fin_cases j <;> fin_cases k <;> simp_all [eq_comm]
  · fin_cases j <;> fin_cases l <;> simp_all [eq_comm]

open Classical in
/-- two distinct vertices of an outerplanar graph have at most two common neighbours -/
theorem of_common_le {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsOuterplanar G)
    (p q : Fin n) (hpq : p ≠ q) :
    (Finset.univ.filter (fun y : Fin n => G.Adj p y ∧ G.Adj q y)).card ≤ 2 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 hcon
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hc
  have hn : 2 ≤ n := by
    have h1 := p.isLt
    have h2 := q.isLt
    have h3 : p.val ≠ q.val := fun h => hpq (Fin.ext h)
    omega
  have hf := of_inj5 p q a b c hpq (G.ne_of_adj ha.1).symm (G.ne_of_adj ha.2).symm
    (G.ne_of_adj hb.1).symm (G.ne_of_adj hb.2).symm (G.ne_of_adj hc.1).symm
    (G.ne_of_adj hc.2).symm hab hac hbc
  have hadj : ∀ i : Fin 2, ∀ j : Fin 3, G.Adj (![p, q] i) (![a, b, c] j) := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact ha.1
    · exact hb.1
    · exact hc.1
    · exact ha.2
    · exact hb.2
    · exact hc.2
  apply (TaitTobin.Outerplanar.outerplanar_facts hn G hG).2
  refine ⟨⟨⟨Sum.elim ![p, q] ![a, b, c], ?_⟩, hf⟩⟩
  intro s t h
  rcases s with i | j <;> rcases t with k | l
  · simp at h
  · exact hadj i l
  · exact (hadj k j).symm
  · simp at h

open Classical in
/-- with a universal vertex `x`, every other vertex has at most two neighbours other than `x` -/
theorem of_deg_le {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsOuterplanar G)
    (x : Fin n) (hx : ∀ y : Fin n, y ≠ x → G.Adj x y) (u : Fin n) (hux : u ≠ x) :
    (Finset.univ.filter (fun y : Fin n => y ≠ x ∧ y ≠ x ∧ G.Adj u y)).card ≤ 2 := by
  refine le_trans (Finset.card_le_card ?_) (of_common_le G hG u x hux)
  intro y hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  exact ⟨hy.2.2, hx y hy.1⟩

open Classical in
/-- every nonempty set of non-hub vertices contains a vertex with at most one neighbour in it -/
theorem of_exists_low {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsOuterplanar G)
    (x : Fin n) (hx : ∀ y : Fin n, y ≠ x → G.Adj x y) (S : Finset (Fin n)) (hS : S.Nonempty)
    (hSx : ∀ y ∈ S, y ≠ x ∧ y ≠ x) :
    ∃ v ∈ S, (S.filter (fun y => G.Adj v y)).card ≤ 1 := by
  by_contra hcon
  push Not at hcon
  have hxS : x ∉ S := fun h => (hSx x h).1 rfl
  obtain ⟨T, hT⟩ : ∃ T : Finset (Fin n), T = insert x S := ⟨_, rfl⟩
  have hTc : T.card = S.card + 1 := by
    rw [hT, Finset.card_insert_of_notMem hxS]
  have hS1 : 1 ≤ S.card := Finset.card_pos.2 hS
  let g : Fin T.card → Fin n := fun i => T.orderEmbOfFin rfl i
  have hg : Function.Injective g := (T.orderEmbOfFin rfl).injective
  have hrange : ∀ y, y ∈ T ↔ ∃ i, g i = y := by
    intro y
    have := Finset.range_orderEmbOfFin T (rfl : T.card = T.card)
    constructor
    · intro hy
      have : y ∈ Set.range (T.orderEmbOfFin rfl) := by rw [this]; exact hy
      exact this
    · rintro ⟨i, rfl⟩
      exact Finset.orderEmbOfFin_mem T rfl i
  have houter := of_comap G g hg hG
  obtain ⟨hE, -⟩ := TaitTobin.Outerplanar.outerplanar_facts (by omega : 2 ≤ T.card)
    (G.comap g) houter
  have himg : T = Finset.univ.image g := by
    ext y; simp only [Finset.mem_image, Finset.mem_univ, true_and]; exact hrange y
  set d : Fin n → ℕ := fun y => (T.filter (fun z => G.Adj y z)).card with hd
  have hdeg : ∀ i, (G.comap g).degree i = d (g i) := by
    intro i
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
    simp only [hd]
    refine Finset.card_bij (fun j _ => g j) ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.comap_adj] at hj
      exact Finset.mem_filter.2 ⟨(hrange _).2 ⟨j, rfl⟩, hj⟩
    · intro j _ k _ h; exact hg h
    · intro y hy
      obtain ⟨hyT, hy2⟩ := Finset.mem_filter.1 hy
      obtain ⟨j, rfl⟩ := (hrange y).1 hyT
      exact ⟨j, by simpa using hy2, rfl⟩
  have hsum : ∑ i, (G.comap g).degree i = ∑ y ∈ T, d y := by
    calc ∑ i, (G.comap g).degree i = ∑ i, d (g i) := Finset.sum_congr rfl (fun i _ => hdeg i)
      _ = ∑ y ∈ Finset.univ.image g, d y := (Finset.sum_image (fun a _ b _ h => hg h)).symm
      _ = ∑ y ∈ T, d y := congrArg (fun s => ∑ y ∈ s, d y) himg.symm
  have hdx : T.card - 1 ≤ d x := by
    have hxT' : x ∈ T := by rw [hT]; simp
    have : T.erase x ⊆ T.filter (fun z => G.Adj x z) := by
      intro y hy
      obtain ⟨h1, h2⟩ := Finset.mem_erase.1 hy
      exact Finset.mem_filter.2 ⟨h2, hx y h1⟩
    have := Finset.card_le_card this
    rw [Finset.card_erase_of_mem hxT'] at this
    exact this
  have hdS : ∀ y ∈ S, 3 ≤ d y := by
    intro y hy
    have hyx := (hSx y hy).1
    have hsub : insert x (S.filter (fun z => G.Adj y z)) ⊆ T.filter (fun z => G.Adj y z) := by
      intro z hz
      rw [Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · exact Finset.mem_filter.2 ⟨by rw [hT]; simp, (hx y hyx).symm⟩
      · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hz
        exact Finset.mem_filter.2 ⟨by rw [hT]; simp [h1], h2⟩
    have hc := Finset.card_le_card hsub
    have hxn : x ∉ S.filter (fun z => G.Adj y z) := fun h => hxS (Finset.mem_filter.1 h).1
    rw [Finset.card_insert_of_notMem hxn] at hc
    have := hcon y hy
    simp only [hd]
    omega
  have hsplit : ∑ y ∈ T, d y = d x + ∑ y ∈ S, d y := by
    rw [hT, Finset.sum_insert hxS]
  have hSsum : 3 * S.card ≤ ∑ y ∈ S, d y := by
    have := Finset.card_nsmul_le_sum S d 3 hdS
    simpa [mul_comm] using this
  have hhand := SimpleGraph.sum_degrees_eq_twice_card_edges (G.comap g)
  have hE' : (G.comap g).edgeFinset.card ≤ 2 * T.card - 3 := by convert hE
  omega

open Classical in
theorem sb_peel {n : ℕ} (G : SimpleGraph (Fin n)) (x w : Fin n)
    (hdeg : ∀ u : Fin n, u ≠ x → u ≠ w →
      (Finset.univ.filter (fun y : Fin n => y ≠ x ∧ y ≠ w ∧ G.Adj u y)).card ≤ 2)
    (hlow : ∀ S : Finset (Fin n), S.Nonempty → (∀ y ∈ S, y ≠ x ∧ y ≠ w) →
      ∃ v ∈ S, (S.filter (fun y => G.Adj v y)).card ≤ 1) :
    ∀ k : ℕ, ∀ S : Finset (Fin n), S.card = k → (∀ y ∈ S, y ≠ x ∧ y ≠ w) →
      ∃ f : Fin n → ℕ, Set.InjOn f S ∧ (∀ y ∈ S, f y < S.card) ∧
        ∀ a ∈ S, ∀ b ∈ S, G.Adj a b → f a = f b + 1 ∨ f b = f a + 1 := by
  intro k
  induction k with
  | zero =>
    intro S hS _
    rw [Finset.card_eq_zero] at hS
    subst hS
    exact ⟨fun _ => 0, by simp, by simp, by simp⟩
  | succ k ih =>
    intro S hS hSxw
    have hne : S.Nonempty := by rw [← Finset.card_pos]; omega
    obtain ⟨v, hvS, hv⟩ := hlow S hne hSxw
    have hS0c : (S.erase v).card = k := by rw [Finset.card_erase_of_mem hvS]; omega
    obtain ⟨f₀, hinj, hbd, hed⟩ :=
      ih (S.erase v) hS0c (fun y hy => hSxw y (Finset.mem_of_mem_erase hy))
    have hbd' : ∀ y ∈ S.erase v, f₀ y < k := fun y hy => by have := hbd y hy; omega
    have hcases : ∀ y ∈ S, y = v ∨ y ∈ S.erase v := by
      intro y hy
      by_cases h : y = v
      · exact Or.inl h
      · exact Or.inr (Finset.mem_erase.2 ⟨h, hy⟩)
    have hmem : ∀ y, y ≠ v → y ∈ S → y ∈ S.erase v := fun y h1 h2 => Finset.mem_erase.2 ⟨h1, h2⟩
    by_cases hnb : ∃ u ∈ S.erase v, G.Adj v u
    · obtain ⟨u, hu, hvu⟩ := hnb
      have huS : u ∈ S := Finset.mem_of_mem_erase hu
      have huv : u ≠ v := Finset.ne_of_mem_erase hu
      have huniq : ∀ b ∈ S.erase v, G.Adj v b → b = u := by
        intro b hb hvb
        by_contra hbu
        have hsub : ({u, b} : Finset (Fin n)) ⊆ S.filter (fun y => G.Adj v y) := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact Finset.mem_filter.2 ⟨huS, hvu⟩
          · exact Finset.mem_filter.2 ⟨Finset.mem_of_mem_erase hb, hvb⟩
        have := Finset.card_le_card hsub
        rw [Finset.card_pair (Ne.symm hbu)] at this
        omega
      have hu1 : ∀ a ∈ S.erase v, ∀ b ∈ S.erase v, G.Adj u a → G.Adj u b → a = b := by
        intro a ha b hb hua hub
        by_contra hab
        have haS := Finset.mem_of_mem_erase ha
        have hbS := Finset.mem_of_mem_erase hb
        have hav := Finset.ne_of_mem_erase ha
        have hbv := Finset.ne_of_mem_erase hb
        have hsub : ({a, b, v} : Finset (Fin n)) ⊆
            Finset.univ.filter (fun y : Fin n => y ≠ x ∧ y ≠ w ∧ G.Adj u y) := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rcases hz with rfl | rfl | rfl
          · exact ⟨(hSxw _ haS).1, (hSxw _ haS).2, hua⟩
          · exact ⟨(hSxw _ hbS).1, (hSxw _ hbS).2, hub⟩
          · exact ⟨(hSxw _ hvS).1, (hSxw _ hvS).2, hvu.symm⟩
        have h3 : ({a, b, v} : Finset (Fin n)).card = 3 :=
          Finset.card_eq_three.2 ⟨a, b, v, hab, hav, hbv, rfl⟩
        have := Finset.card_le_card hsub
        have := hdeg u (hSxw u huS).1 (hSxw u huS).2
        omega
      set p := f₀ u with hp
      have hpk : p < k := hbd' u hu
      by_cases hB : ∃ b0 ∈ S.erase v, G.Adj u b0 ∧ f₀ b0 = p + 1
      · obtain ⟨b0, hb0, hub0, hfb0⟩ := hB
        have hnp : ∀ a ∈ S.erase v, G.Adj u a → f₀ a + 1 ≠ p := by
          intro a ha hua h
          have := hu1 a ha b0 hb0 hua hub0
          subst this
          omega
        refine ⟨fun y => if y = v then p else if p ≤ f₀ y then f₀ y + 1 else f₀ y, ?_, ?_, ?_⟩
        · intro a ha b hb hab
          by_cases hav : a = v <;> by_cases hbv : b = v
          · rw [hav, hbv]
          · exfalso
            have hb' := hmem b hbv hb
            simp only [hav, hbv, if_true, if_false] at hab
            split_ifs at hab <;> omega
          · exfalso
            have ha' := hmem a hav ha
            simp only [hav, hbv, if_true, if_false] at hab
            split_ifs at hab <;> omega
          · have ha' := hmem a hav ha
            have hb' := hmem b hbv hb
            simp only [hav, hbv, if_false] at hab
            apply hinj ha' hb'
            split_ifs at hab <;> omega
        · intro y hy
          rcases hcases y hy with rfl | hy'
          · simp only [if_true]; omega
          · have := hbd' y hy'
            have hyv := Finset.ne_of_mem_erase hy'
            simp only [hyv, if_false]
            split_ifs <;> omega
        · have edge1 : ∀ a ∈ S.erase v, ∀ b ∈ S.erase v, G.Adj a b → f₀ a = f₀ b + 1 →
              (if a = v then p else if p ≤ f₀ a then f₀ a + 1 else f₀ a) =
                (if b = v then p else if p ≤ f₀ b then f₀ b + 1 else f₀ b) + 1 := by
            intro a ha b hb hab h
            have hav := Finset.ne_of_mem_erase ha
            have hbv := Finset.ne_of_mem_erase hb
            simp only [hav, hbv, if_false]
            by_cases hfa : f₀ a = p
            · have hau : a = u := hinj ha hu hfa
              subst hau
              exfalso
              exact hnp b hb hab (by omega)
            · split_ifs <;> omega
          intro a ha b hb hab
          rcases hcases a ha with rfl | ha'
          · rcases hcases b hb with rfl | hb'
            · exact absurd hab (G.loopless.irrefl _)
            · have := huniq b hb' hab
              subst this
              right
              have hbv := Finset.ne_of_mem_erase hb'
              simp only [hbv, if_true, if_false]
              split_ifs <;> omega
          · rcases hcases b hb with rfl | hb'
            · have := huniq a ha' hab.symm
              subst this
              left
              have hav := Finset.ne_of_mem_erase ha'
              simp only [hav, if_true, if_false]
              split_ifs <;> omega
            · rcases hed a ha' b hb' hab with h | h
              · exact Or.inl (edge1 a ha' b hb' hab h)
              · exact Or.inr (edge1 b hb' a ha' hab.symm h)
      · push Not at hB
        have hns : ∀ b ∈ S.erase v, G.Adj u b → f₀ b ≠ p + 1 := fun b hb hub => hB b hb hub
        refine ⟨fun y => if y = v then p + 1 else if p < f₀ y then f₀ y + 1 else f₀ y, ?_, ?_, ?_⟩
        · intro a ha b hb hab
          by_cases hav : a = v <;> by_cases hbv : b = v
          · rw [hav, hbv]
          · exfalso
            have hb' := hmem b hbv hb
            simp only [hav, hbv, if_true, if_false] at hab
            split_ifs at hab <;> omega
          · exfalso
            have ha' := hmem a hav ha
            simp only [hav, hbv, if_true, if_false] at hab
            split_ifs at hab <;> omega
          · have ha' := hmem a hav ha
            have hb' := hmem b hbv hb
            simp only [hav, hbv, if_false] at hab
            apply hinj ha' hb'
            split_ifs at hab <;> omega
        · intro y hy
          rcases hcases y hy with rfl | hy'
          · simp only [if_true]; omega
          · have := hbd' y hy'
            have hyv := Finset.ne_of_mem_erase hy'
            simp only [hyv, if_false]
            split_ifs <;> omega
        · have edge1 : ∀ a ∈ S.erase v, ∀ b ∈ S.erase v, G.Adj a b → f₀ a = f₀ b + 1 →
              (if a = v then p + 1 else if p < f₀ a then f₀ a + 1 else f₀ a) =
                (if b = v then p + 1 else if p < f₀ b then f₀ b + 1 else f₀ b) + 1 := by
            intro a ha b hb hab h
            have hav := Finset.ne_of_mem_erase ha
            have hbv := Finset.ne_of_mem_erase hb
            simp only [hav, hbv, if_false]
            by_cases hfb : f₀ b = p
            · have hbu : b = u := hinj hb hu hfb
              subst hbu
              exfalso
              exact hns a ha hab.symm (by omega)
            · split_ifs <;> omega
          intro a ha b hb hab
          rcases hcases a ha with rfl | ha'
          · rcases hcases b hb with rfl | hb'
            · exact absurd hab (G.loopless.irrefl _)
            · have := huniq b hb' hab
              subst this
              left
              have hbv := Finset.ne_of_mem_erase hb'
              simp only [hbv, if_true, if_false]
              split_ifs <;> omega
          · rcases hcases b hb with rfl | hb'
            · have := huniq a ha' hab.symm
              subst this
              right
              have hav := Finset.ne_of_mem_erase ha'
              simp only [hav, if_true, if_false]
              split_ifs <;> omega
            · rcases hed a ha' b hb' hab with h | h
              · exact Or.inl (edge1 a ha' b hb' hab h)
              · exact Or.inr (edge1 b hb' a ha' hab.symm h)
    · push Not at hnb
      refine ⟨fun y => if y = v then k else f₀ y, ?_, ?_, ?_⟩
      · intro a ha b hb hab
        by_cases hav : a = v <;> by_cases hbv : b = v
        · rw [hav, hbv]
        · exfalso
          have hb' := hmem b hbv hb
          simp only [hav, hbv, if_true, if_false] at hab
          have := hbd' b hb'
          omega
        · exfalso
          have ha' := hmem a hav ha
          simp only [hav, hbv, if_true, if_false] at hab
          have := hbd' a ha'
          omega
        · have ha' := hmem a hav ha
          have hb' := hmem b hbv hb
          simp only [hav, hbv, if_false] at hab
          exact hinj ha' hb' hab
      · intro y hy
        rcases hcases y hy with rfl | hy'
        · simp only [if_true]; omega
        · have := hbd' y hy'
          have hyv := Finset.ne_of_mem_erase hy'
          simp only [hyv, if_false]
          omega
      · intro a ha b hb hab
        rcases hcases a ha with rfl | ha'
        · rcases hcases b hb with rfl | hb'
          · exact absurd hab (G.loopless.irrefl _)
          · exact absurd hab (hnb b hb')
        · rcases hcases b hb with rfl | hb'
          · exact absurd hab.symm (hnb a ha')
          · have hav := Finset.ne_of_mem_erase ha'
            have hbv := Finset.ne_of_mem_erase hb'
            simp only [hav, hbv, if_false]
            exact hed a ha' b hb' hab


open TaitTobin.Outerplanar in
theorem of_fan_ll {n : ℕ} (i j : Fin 1) :
    (fan n).Adj (Sum.inl i) (Sum.inl j) ↔ i ≠ j := Iff.rfl

open TaitTobin.Outerplanar in
theorem of_fan_lr {n : ℕ} (i : Fin 1) (j : Fin (n - 1)) :
    (fan n).Adj (Sum.inl i) (Sum.inr j) ↔ True := Iff.rfl

open TaitTobin.Outerplanar in
theorem of_fan_rl {n : ℕ} (i : Fin 1) (j : Fin (n - 1)) :
    (fan n).Adj (Sum.inr j) (Sum.inl i) ↔ True := Iff.rfl

open TaitTobin.Outerplanar in
theorem of_fan_rr {n : ℕ} (i j : Fin (n - 1)) :
    (fan n).Adj (Sum.inr i) (Sum.inr j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val :=
  SimpleGraph.pathGraph_adj

open Classical TaitTobin.Outerplanar in
theorem of_main {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsOuterplanar G)
    (x : Fin n) (hx : ∀ y : Fin n, y ≠ x → G.Adj x y) :
    ∃ e : Fin n ≃ (Fin 1 ⊕ Fin (n - 1)),
      ∀ a b : Fin n, G.Adj a b → (fan n).Adj (e a) (e b) := by
  have hdeg : ∀ u : Fin n, u ≠ x → u ≠ x →
      (Finset.univ.filter (fun y : Fin n => y ≠ x ∧ y ≠ x ∧ G.Adj u y)).card ≤ 2 :=
    fun u h1 _ => of_deg_le G hG x hx u h1
  have hlow : ∀ S : Finset (Fin n), S.Nonempty → (∀ y ∈ S, y ≠ x ∧ y ≠ x) →
      ∃ v ∈ S, (S.filter (fun y => G.Adj v y)).card ≤ 1 :=
    fun S hS hSx => of_exists_low G hG x hx S hS hSx
  set V' : Finset (Fin n) := Finset.univ.filter (fun y => y ≠ x ∧ y ≠ x) with hV'
  have hV'mem : ∀ y, y ∈ V' ↔ y ≠ x ∧ y ≠ x := by intro y; simp [hV']
  have hn1 : 1 ≤ n := by have := x.isLt; omega
  have hcard : V'.card = n - 1 := by
    have : V' = Finset.univ.erase x := by
      ext y; simp [hV'mem]
    rw [this, Finset.card_erase_of_mem (Finset.mem_univ x)]
    simp
  obtain ⟨f, hinj, hbd, hed⟩ := sb_peel G x x hdeg hlow V'.card V' rfl
    (fun y hy => (hV'mem y).1 hy)
  have hb : ∀ y, y ≠ x → f y < n - 1 := by
    intro y h1
    have := hbd y ((hV'mem y).2 ⟨h1, h1⟩)
    omega
  let e0 : Fin n → Fin 1 ⊕ Fin (n - 1) := fun y =>
    if h : y = x then Sum.inl 0 else Sum.inr ⟨f y, hb y h⟩
  have he0x : e0 x = Sum.inl 0 := by simp only [e0, dif_pos rfl]
  have he0o : ∀ (y : Fin n) (h1 : y ≠ x), e0 y = Sum.inr ⟨f y, hb y h1⟩ := by
    intro y h1; simp only [e0, dif_neg h1]
  have hinj0 : Function.Injective e0 := by
    intro a b hab
    by_cases ha : a = x <;> by_cases hb' : b = x
    · rw [ha, hb']
    · rw [ha, he0x, he0o b hb'] at hab; cases hab
    · rw [hb', he0x, he0o a ha] at hab; cases hab
    · rw [he0o a ha, he0o b hb'] at hab
      have := Sum.inr.inj hab
      exact hinj ((hV'mem a).2 ⟨ha, ha⟩) ((hV'mem b).2 ⟨hb', hb'⟩) (congrArg Fin.val this)
  have hbij : Function.Bijective e0 :=
    (Fintype.bijective_iff_injective_and_card e0).2 ⟨hinj0, by simp; omega⟩
  refine ⟨Equiv.ofBijective e0 hbij, fun a b hab => ?_⟩
  show (fan n).Adj (e0 a) (e0 b)
  by_cases ha : a = x <;> by_cases hb' : b = x
  · rw [ha, hb'] at hab; exact absurd hab (G.loopless.irrefl _)
  · rw [ha, he0x, he0o b hb']; exact (of_fan_lr _ _).2 trivial
  · rw [hb', he0x, he0o a ha]; exact (of_fan_rl _ _).2 trivial
  · rw [he0o a ha, he0o b hb']
    have h := hed a ((hV'mem a).2 ⟨ha, ha⟩) b ((hV'mem b).2 ⟨hb', hb'⟩) hab
    exact (of_fan_rr _ _).2 (by show f a + 1 = f b ∨ f b + 1 = f a; omega)

end ofhelpers

open Classical WangKangXue.SpectralTuran TaitTobin.Outerplanar in
theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsOuterplanar G)
    (x : Fin n) (hx : ∀ y : Fin n, y ≠ x → G.Adj x y) :
    ∃ e : Fin n ≃ (Fin 1 ⊕ Fin (n - 1)),
      ∀ a b : Fin n, G.Adj a b → (fan n).Adj (e a) (e b) :=
  of_main G hG x hx
