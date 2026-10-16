-- Prove2me | solution 1 for TaitTobin.Planar.subgraph_bookPath_of_universal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T11:41:15.330345+00:00
-- url     : https://prove2.me/submissions/42d0cfce-4f5c-46cc-9fbe-e629aeb5a0a2

import Mathlib
import Definitions.Def_TaitTobin_Planar_Setting
import Theorems.Thm_TaitTobin_Planar_planar_facts

set_option autoImplicit false

section sbhelpers

open RobertsonSeymour1986.GM5

/-- planarity pulls back along an injective map of vertices -/
theorem sb_planar_comap {V W : Type} (G : SimpleGraph W) (g : V → W)
    (hg : Function.Injective g) (hG : IsPlanar G) : IsPlanar (G.comap g) := by
  obtain ⟨D⟩ := hG
  refine ⟨⟨fun v => D.vertex (g v), D.vertex_injective.comp hg,
    fun {v w} h => D.arc h, fun {v w} h => D.arc_injective h,
    fun {v w} h => D.arc_reverse h, ?_, ?_⟩⟩
  · intro v w h t x hx
    rcases D.arc_avoids_vertices h t (g x) hx with h1 | h1
    · exact Or.inl (hg h1)
    · exact Or.inr (hg h1)
  · intro v w x y h k s t hst
    rcases D.arcs_meet_only_at_endpoints h k s t hst with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h1
    · exact Or.inl ⟨hg h1, hg h2⟩
    · exact Or.inr (Or.inl ⟨hg h1, hg h2⟩)
    · exact Or.inr (Or.inr h1)

open Classical in
/-- in a planar graph with two universal vertices the other vertices have at most two
neighbours among the other vertices -/
theorem sb_deg_le {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsPlanar G)
    (x w : Fin n) (hxw : x ≠ w) (hx : ∀ y : Fin n, y ≠ x → G.Adj x y)
    (hw : ∀ y : Fin n, y ≠ w → G.Adj w y) (u : Fin n) (hux : u ≠ x) (huw : u ≠ w) :
    (Finset.univ.filter (fun y : Fin n => y ≠ x ∧ y ≠ w ∧ G.Adj u y)).card ≤ 2 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 hcon
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hc
  have hax : a ≠ u := (G.ne_of_adj ha.2.2).symm
  have hbx : b ≠ u := (G.ne_of_adj hb.2.2).symm
  have hcx : c ≠ u := (G.ne_of_adj hc.2.2).symm
  have hwu : w ≠ u := fun h => huw h.symm
  have hxu : x ≠ u := fun h => hux h.symm
  let f : Fin 3 ⊕ Fin 3 → Fin n := Sum.elim ![x, w, u] ![a, b, c]
  have hf : Function.Injective f := by
    intro s t h
    rcases s with i | j <;> rcases t with k | l <;> simp only [f, Sum.elim_inl, Sum.elim_inr] at h
    · fin_cases i <;> fin_cases k <;> simp_all [eq_comm]
    · fin_cases i <;> fin_cases l <;> simp_all [eq_comm]
    · fin_cases j <;> fin_cases k <;> simp_all [eq_comm]
    · fin_cases j <;> fin_cases l <;> simp_all [eq_comm]
  have hn : 3 ≤ n := by
    have := Fintype.card_le_of_injective f hf
    simp at this
    omega
  have hAx : ∀ j : Fin 3, G.Adj x (![a, b, c] j) := by
    intro j; fin_cases j
    · exact hx a ha.1
    · exact hx b hb.1
    · exact hx c hc.1
  have hAw : ∀ j : Fin 3, G.Adj w (![a, b, c] j) := by
    intro j; fin_cases j
    · exact hw a ha.2.1
    · exact hw b hb.2.1
    · exact hw c hc.2.1
  have hAu : ∀ j : Fin 3, G.Adj u (![a, b, c] j) := by
    intro j; fin_cases j
    · exact ha.2.2
    · exact hb.2.2
    · exact hc.2.2
  have hadj : ∀ i j : Fin 3, G.Adj (![x, w, u] i) (![a, b, c] j) := by
    intro i j; fin_cases i
    · exact hAx j
    · exact hAw j
    · exact hAu j
  have hfree := (TaitTobin.Planar.planar_facts hn G hG).1
  apply hfree
  refine ⟨⟨⟨f, ?_⟩, hf⟩⟩
  intro s t h
  rcases s with i | j <;> rcases t with k | l
  · simp at h
  · exact hadj i l
  · exact (hadj k j).symm
  · simp at h

open Classical in
theorem sb_exists_low {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsPlanar G)
    (x w : Fin n) (hxw : x ≠ w) (hx : ∀ y : Fin n, y ≠ x → G.Adj x y)
    (hw : ∀ y : Fin n, y ≠ w → G.Adj w y) (S : Finset (Fin n)) (hS : S.Nonempty)
    (hSxw : ∀ y ∈ S, y ≠ x ∧ y ≠ w) :
    ∃ v ∈ S, (S.filter (fun y => G.Adj v y)).card ≤ 1 := by
  by_contra hcon
  push Not at hcon
  have hxS : x ∉ S := fun h => (hSxw x h).1 rfl
  have hwS : w ∉ S := fun h => (hSxw w h).2 rfl
  have hxT : x ∉ insert w S := by simp [hxw, hxS]
  obtain ⟨T, hT⟩ : ∃ T : Finset (Fin n), T = insert x (insert w S) := ⟨_, rfl⟩
  have hTc : T.card = S.card + 2 := by
    rw [hT, Finset.card_insert_of_notMem hxT, Finset.card_insert_of_notMem hwS]
  obtain ⟨v0, hv0⟩ := hS
  have hS3 : 3 ≤ S.card := by
    have h1 := hcon v0 hv0
    have h2 : (S.filter (fun y => G.Adj v0 y)).card ≤ S.card := Finset.card_le_card (Finset.filter_subset _ _)
    have h3 : (S.filter (fun y => G.Adj v0 y)).card ≤ (S.erase v0).card := by
      apply Finset.card_le_card
      intro y hy
      simp only [Finset.mem_filter] at hy
      exact Finset.mem_erase.2 ⟨(G.ne_of_adj hy.2).symm, hy.1⟩
    have h4 := Finset.card_erase_of_mem hv0
    omega
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
  have hplanar := sb_planar_comap G g hg hG
  obtain ⟨-, hE, -⟩ := TaitTobin.Planar.planar_facts (by omega : 3 ≤ T.card) (G.comap g) hplanar
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
  have hdw : T.card - 1 ≤ d w := by
    have hwT' : w ∈ T := by rw [hT]; simp
    have : T.erase w ⊆ T.filter (fun z => G.Adj w z) := by
      intro y hy
      obtain ⟨h1, h2⟩ := Finset.mem_erase.1 hy
      exact Finset.mem_filter.2 ⟨h2, hw y h1⟩
    have := Finset.card_le_card this
    rw [Finset.card_erase_of_mem hwT'] at this
    exact this
  have hdS : ∀ y ∈ S, 4 ≤ d y := by
    intro y hy
    obtain ⟨hyx, hyw⟩ := hSxw y hy
    have hsub : insert x (insert w (S.filter (fun z => G.Adj y z))) ⊆ T.filter (fun z => G.Adj y z) := by
      intro z hz
      rw [Finset.mem_insert, Finset.mem_insert] at hz
      rcases hz with rfl | rfl | hz
      · exact Finset.mem_filter.2 ⟨by rw [hT]; simp, (hx y hyx).symm⟩
      · exact Finset.mem_filter.2 ⟨by rw [hT]; simp, (hw y hyw).symm⟩
      · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hz
        exact Finset.mem_filter.2 ⟨by rw [hT]; simp [h1], h2⟩
    have hc := Finset.card_le_card hsub
    have hxn : x ∉ insert w (S.filter (fun z => G.Adj y z)) := by
      simp only [Finset.mem_insert, Finset.mem_filter, not_or]
      exact ⟨hxw, fun h => hxS h.1⟩
    have hwn : w ∉ S.filter (fun z => G.Adj y z) := fun h => hwS (Finset.mem_filter.1 h).1
    rw [Finset.card_insert_of_notMem hxn, Finset.card_insert_of_notMem hwn] at hc
    have := hcon y hy
    simp only [hd]
    omega
  have hxT' : x ∈ T := by rw [hT]; simp
  have hwT' : w ∈ T.erase x := Finset.mem_erase.2 ⟨fun h => hxw h.symm, by rw [hT]; simp⟩
  have hsplit : ∑ y ∈ T, d y = d x + (d w + ∑ y ∈ S, d y) := by
    rw [hT, Finset.sum_insert hxT, Finset.sum_insert hwS]
  have hSsum : 4 * S.card ≤ ∑ y ∈ S, d y := by
    have := Finset.card_nsmul_le_sum S d 4 hdS
    simpa [mul_comm] using this
  have hhand := SimpleGraph.sum_degrees_eq_twice_card_edges (G.comap g)
  have hE' : (G.comap g).edgeFinset.card ≤ 3 * T.card - 6 := by convert hE
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

open TaitTobin.Planar in
theorem sb_bp_ll {n : ℕ} (i j : Fin 2) :
    (bookPath n).Adj (Sum.inl i) (Sum.inl j) ↔ i ≠ j := Iff.rfl

open TaitTobin.Planar in
theorem sb_bp_lr {n : ℕ} (i : Fin 2) (j : Fin (n - 2)) :
    (bookPath n).Adj (Sum.inl i) (Sum.inr j) ↔ True := Iff.rfl

open TaitTobin.Planar in
theorem sb_bp_rl {n : ℕ} (i : Fin 2) (j : Fin (n - 2)) :
    (bookPath n).Adj (Sum.inr j) (Sum.inl i) ↔ True := Iff.rfl

open TaitTobin.Planar in
theorem sb_bp_rr {n : ℕ} (i j : Fin (n - 2)) :
    (bookPath n).Adj (Sum.inr i) (Sum.inr j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val :=
  SimpleGraph.pathGraph_adj

open Classical TaitTobin.Planar in
theorem sb_main {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsPlanar G)
    (x w : Fin n) (hxw : x ≠ w) (hx : ∀ y : Fin n, y ≠ x → G.Adj x y)
    (hw : ∀ y : Fin n, y ≠ w → G.Adj w y) :
    ∃ e : Fin n ≃ (Fin 2 ⊕ Fin (n - 2)),
      ∀ a b : Fin n, G.Adj a b → (bookPath n).Adj (e a) (e b) := by
  have hdeg : ∀ u : Fin n, u ≠ x → u ≠ w →
      (Finset.univ.filter (fun y : Fin n => y ≠ x ∧ y ≠ w ∧ G.Adj u y)).card ≤ 2 :=
    fun u h1 h2 => sb_deg_le G hG x w hxw hx hw u h1 h2
  have hlow : ∀ S : Finset (Fin n), S.Nonempty → (∀ y ∈ S, y ≠ x ∧ y ≠ w) →
      ∃ v ∈ S, (S.filter (fun y => G.Adj v y)).card ≤ 1 :=
    fun S hS hSxw => sb_exists_low G hG x w hxw hx hw S hS hSxw
  set V' : Finset (Fin n) := Finset.univ.filter (fun y => y ≠ x ∧ y ≠ w) with hV'
  have hV'mem : ∀ y, y ∈ V' ↔ y ≠ x ∧ y ≠ w := by intro y; simp [hV']
  have hxw' : x.val ≠ w.val := fun h => hxw (Fin.ext h)
  have hn2 : 2 ≤ n := by have := x.isLt; have := w.isLt; omega
  have hcard : V'.card = n - 2 := by
    have : V' = (Finset.univ.erase x).erase w := by
      ext y; simp [hV'mem, and_comm]
    rw [this, Finset.card_erase_of_mem (by simp [Ne.symm hxw]), Finset.card_erase_of_mem (by simp)]
    simp
    omega
  obtain ⟨f, hinj, hbd, hed⟩ := sb_peel G x w hdeg hlow V'.card V' rfl (fun y hy => (hV'mem y).1 hy)
  have hb : ∀ y, y ≠ x → y ≠ w → f y < n - 2 := by
    intro y h1 h2
    have := hbd y ((hV'mem y).2 ⟨h1, h2⟩)
    omega
  let e0 : Fin n → Fin 2 ⊕ Fin (n - 2) := fun y =>
    if h : y = x then Sum.inl 0 else if h2 : y = w then Sum.inl 1 else Sum.inr ⟨f y, hb y h h2⟩
  have he0x : e0 x = Sum.inl 0 := by simp only [e0, dif_pos rfl]
  have he0w : e0 w = Sum.inl 1 := by simp [e0, Ne.symm hxw]
  have he0o : ∀ (y : Fin n) (h1 : y ≠ x) (h2 : y ≠ w),
      e0 y = Sum.inr ⟨f y, hb y h1 h2⟩ := by
    intro y h1 h2; simp only [e0, dif_neg h1, dif_neg h2]
  have hcls : ∀ y : Fin n, y = x ∨ y = w ∨ (y ≠ x ∧ y ≠ w) := by
    intro y
    by_cases h1 : y = x
    · exact Or.inl h1
    · by_cases h2 : y = w
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr ⟨h1, h2⟩)
  have hinj0 : Function.Injective e0 := by
    intro a b hab
    rcases hcls a with ha | ha | ⟨ha1, ha2⟩ <;> rcases hcls b with hb' | hb' | ⟨hb1, hb2⟩
    · rw [ha, hb']
    · rw [ha, hb', he0x, he0w] at hab; exact absurd (Sum.inl.inj hab) (by decide)
    · rw [ha, he0x, he0o b hb1 hb2] at hab; cases hab
    · rw [ha, hb', he0x, he0w] at hab; exact absurd (Sum.inl.inj hab).symm (by decide)
    · rw [ha, hb']
    · rw [ha, he0w, he0o b hb1 hb2] at hab; cases hab
    · rw [hb', he0x, he0o a ha1 ha2] at hab; cases hab
    · rw [hb', he0w, he0o a ha1 ha2] at hab; cases hab
    · rw [he0o a ha1 ha2, he0o b hb1 hb2] at hab
      have := Sum.inr.inj hab
      exact hinj ((hV'mem a).2 ⟨ha1, ha2⟩) ((hV'mem b).2 ⟨hb1, hb2⟩) (congrArg Fin.val this)
  have hbij : Function.Bijective e0 :=
    (Fintype.bijective_iff_injective_and_card e0).2 ⟨hinj0, by simp; omega⟩
  refine ⟨Equiv.ofBijective e0 hbij, fun a b hab => ?_⟩
  show (bookPath n).Adj (e0 a) (e0 b)
  rcases hcls a with ha | ha | ⟨ha1, ha2⟩ <;> rcases hcls b with hb' | hb' | ⟨hb1, hb2⟩
  · rw [ha, hb'] at hab; exact absurd hab (G.loopless.irrefl _)
  · rw [ha, hb', he0x, he0w]; exact (sb_bp_ll _ _).2 (by decide)
  · rw [ha, he0x, he0o b hb1 hb2]; exact (sb_bp_lr _ _).2 trivial
  · rw [ha, hb', he0x, he0w]; exact (sb_bp_ll _ _).2 (by decide)
  · rw [ha, hb'] at hab; exact absurd hab (G.loopless.irrefl _)
  · rw [ha, he0w, he0o b hb1 hb2]; exact (sb_bp_lr _ _).2 trivial
  · rw [hb', he0x, he0o a ha1 ha2]; exact (sb_bp_rl _ _).2 trivial
  · rw [hb', he0w, he0o a ha1 ha2]; exact (sb_bp_rl _ _).2 trivial
  · rw [he0o a ha1 ha2, he0o b hb1 hb2]
    have h := hed a ((hV'mem a).2 ⟨ha1, ha2⟩) b ((hV'mem b).2 ⟨hb1, hb2⟩) hab
    exact (sb_bp_rr _ _).2 (by show f a + 1 = f b ∨ f b + 1 = f a; omega)

end sbhelpers

open Classical RobertsonSeymour1986.GM5 TaitTobin.Planar in
theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsPlanar G)
    (x w : Fin n) (hxw : x ≠ w) (hx : ∀ y : Fin n, y ≠ x → G.Adj x y)
    (hw : ∀ y : Fin n, y ≠ w → G.Adj w y) :
    ∃ e : Fin n ≃ (Fin 2 ⊕ Fin (n - 2)),
      ∀ a b : Fin n, G.Adj a b → (bookPath n).Adj (e a) (e b) :=
  sb_main G hG x w hxw hx hw
