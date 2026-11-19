-- Prove2me | solution 1 for OPG37271.hasStarEdgeColoring_of_bridge
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T04:42:09.778166+00:00
-- url     : https://prove2.me/submissions/ac898777-f0e4-4412-884f-9c29e7eb76ca

import Definitions.Def_opg37271_star_edge_coloring
import Theorems.Thm_OPG37271_isStarEdgeColoring_insert_edge
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Finset.Card

set_option autoImplicit false

open OPG37271

universe u

private lemma card_neighborFinset_le_of_subcubic {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hsub : IsSubcubic G) (v : V) :
    (G.neighborFinset v).card ≤ 3 := by
  have h : ((G.neighborFinset v : Set V)).encard ≤ 3 := by
    convert hsub v using 1
    congr 1
    ext x
    simp
  rw [Set.encard_coe_eq_coe_finsetCard] at h
  exact Nat.cast_le.mp h

private lemma card_neighborFinset_delete_le_two {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hsub : IsSubcubic G)
    (u v : V) (huv : G.Adj u v) :
    ((G.deleteEdges {s(u, v)}).neighborFinset u).card ≤ 2 := by
  classical
  have hle : (G.deleteEdges {s(u, v)}).neighborFinset u ⊆ (G.neighborFinset u).erase v := by
    intro w hw
    rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset]
    rw [SimpleGraph.mem_neighborFinset, SimpleGraph.deleteEdges_adj] at hw
    refine ⟨?_, hw.1⟩
    intro hwu
    apply hw.2
    subst hwu
    simp
  have hcard := Finset.card_le_card hle
  have hv_mem : v ∈ G.neighborFinset u := (SimpleGraph.mem_neighborFinset G u v).mpr huv
  rw [Finset.card_erase_of_mem hv_mem] at hcard
  have h3 := card_neighborFinset_le_of_subcubic hsub u
  omega

theorem solution {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hsub : IsSubcubic G) (u v : V) (huv : G.Adj u v)
    (hbridge : ¬ (G.deleteEdges {s(u, v)}).Reachable u v)
    (hc' : HasStarEdgeColoring (G.deleteEdges {s(u, v)}) 7) :
    HasStarEdgeColoring G 7 := by
  classical
  let G' := G.deleteEdges {s(u, v)}
  have hG'le : G' ≤ G := SimpleGraph.deleteEdges_le {s(u, v)}
  have hsub' : IsSubcubic G' := fun w => le_trans (Set.encard_le_encard (SimpleGraph.neighborSet_mono hG'le w)) (hsub w)
  rcases hc' with ⟨c', hc'_star⟩
  let S (a : V) : Finset (Sym2 V) :=
    (G'.neighborFinset a).biUnion fun w => (G'.neighborFinset w).image fun z => s(w, z)
  have hS_bound : ∀ a : V, (G'.neighborFinset a).card ≤ 2 → (S a).card ≤ 6 := by
    intro a hdeg_a
    calc (S a).card
        ≤ ∑ w ∈ G'.neighborFinset a, ((G'.neighborFinset w).image fun z => s(w, z)).card := Finset.card_biUnion_le
      _ ≤ ∑ w ∈ G'.neighborFinset a, (G'.neighborFinset w).card := Finset.sum_le_sum fun w _ => Finset.card_image_le
      _ ≤ ∑ _w ∈ G'.neighborFinset a, 3 := Finset.sum_le_sum fun w _ => card_neighborFinset_le_of_subcubic hsub' w
      _ = (G'.neighborFinset a).card * 3 := by simp
      _ ≤ 2 * 3 := Nat.mul_le_mul_right 3 hdeg_a
      _ = 6 := rfl
  have hSu_card : (S u).card ≤ 6 := hS_bound u (card_neighborFinset_delete_le_two hsub u v huv)
  have hSv_card : (S v).card ≤ 6 := by
    have hdeg_v : (G'.neighborFinset v).card ≤ 2 := by
      have hle : G'.neighborFinset v ⊆ (G.deleteEdges {s(v, u)}).neighborFinset v := by
        intro w hw
        simpa [G', Sym2.eq_swap] using hw
      exact le_trans (Finset.card_le_card hle) (card_neighborFinset_delete_le_two hsub v u huv.symm)
    exact hS_bound v hdeg_v
  have pick_unused : ∀ (T : Finset (Sym2 V)), T.card ≤ 6 →
      ∃ col : Fin 7, ∀ e ∈ T, ∀ he : e ∈ G'.edgeSet, c' ⟨e, he⟩ ≠ col := by
    intro T hT
    let used : Finset (Fin 7) := T.attach.image fun e =>
      if he : e.1 ∈ G'.edgeSet then c' ⟨e.1, he⟩ else 0
    have hused : used.card < 7 := by
      calc used.card ≤ T.attach.card := Finset.card_image_le
        _ = T.card := Finset.card_attach
        _ ≤ 6 := hT
        _ < 7 := by omega
    have hex : ∃ col : Fin 7, col ∉ used := by
      by_contra hnone
      push Not at hnone
      have hle := Finset.card_le_card (s := Finset.univ) (fun x _ => hnone x)
      rw [Finset.card_fin] at hle
      omega
    rcases hex with ⟨col, hcol⟩
    refine ⟨col, fun e heT heG' heq => hcol ?_⟩
    refine Finset.mem_image.mpr ⟨⟨e, heT⟩, Finset.mem_attach _ _, ?_⟩
    simp only [dif_pos heG', heq]
  rcases pick_unused (S u) hSu_card with ⟨col_u, hcol_u⟩
  rcases pick_unused (S v) hSv_card with ⟨col_v, hcol_v⟩
  let inU (e : Sym2 V) : Prop := ∃ a ∈ e, G'.Reachable u a
  let c'' : EdgeColoring G' (Fin 7) := fun e =>
    if inU e.1 then c' e else Equiv.swap col_u col_v (c' e)
  have hc''_get_U : ∀ x y (hxy : G'.Adj x y), G'.Reachable u x →
      c''.get x y hxy = c'.get x y hxy := by
    intro x y hxy hrx
    have hin : inU s(x, y) := ⟨x, Sym2.mem_mk_left x y, hrx⟩
    simp only [SimpleGraph.EdgeLabeling.get, c'', if_pos hin]
  have hc''_get_nU : ∀ x y (hxy : G'.Adj x y), ¬ G'.Reachable u x →
      c''.get x y hxy = Equiv.swap col_u col_v (c'.get x y hxy) := by
    intro x y hxy hnrx
    have hnin : ¬ inU s(x, y) := by
      rintro ⟨a, ha, hra⟩
      rw [Sym2.mem_iff] at ha
      rcases ha with rfl | rfl
      · exact hnrx hra
      · exact hnrx (hra.trans (SimpleGraph.Adj.reachable hxy).symm)
    simp only [SimpleGraph.EdgeLabeling.get, c'', if_neg hnin]
  have hc''_star : IsStarEdgeColoring c'' := by
    rcases hc'_star with ⟨hp, hpa, hcy⟩
    refine ⟨?_, ?_, ?_⟩
    · intro a b d hab had hbd
      by_cases hra : G'.Reachable u a
      · rw [hc''_get_U a b hab hra, hc''_get_U a d had hra]
        exact hp a b d hab had hbd
      · rw [hc''_get_nU a b hab hra, hc''_get_nU a d had hra]
        intro heq
        exact hp a b d hab had hbd ((Equiv.swap col_u col_v).injective heq)
    · rintro ⟨v₀, v₁, v₂, v₃, v₄, hnd, h01, h12, h23, h34, hc1, hc2⟩
      by_cases hr0 : G'.Reachable u v₀
      · have hr1 : G'.Reachable u v₁ := hr0.trans (SimpleGraph.Adj.reachable h01)
        have hr2 : G'.Reachable u v₂ := hr1.trans (SimpleGraph.Adj.reachable h12)
        have hr3 : G'.Reachable u v₃ := hr2.trans (SimpleGraph.Adj.reachable h23)
        rw [hc''_get_U v₀ v₁ h01 hr0, hc''_get_U v₂ v₃ h23 hr2] at hc1
        rw [hc''_get_U v₁ v₂ h12 hr1, hc''_get_U v₃ v₄ h34 hr3] at hc2
        exact hpa ⟨v₀, v₁, v₂, v₃, v₄, hnd, h01, h12, h23, h34, hc1, hc2⟩
      · have hr1 : ¬ G'.Reachable u v₁ := fun h => hr0 (h.trans (SimpleGraph.Adj.reachable h01).symm)
        have hr2 : ¬ G'.Reachable u v₂ := fun h => hr1 (h.trans (SimpleGraph.Adj.reachable h12).symm)
        have hr3 : ¬ G'.Reachable u v₃ := fun h => hr2 (h.trans (SimpleGraph.Adj.reachable h23).symm)
        rw [hc''_get_nU v₀ v₁ h01 hr0, hc''_get_nU v₂ v₃ h23 hr2] at hc1
        rw [hc''_get_nU v₁ v₂ h12 hr1, hc''_get_nU v₃ v₄ h34 hr3] at hc2
        exact hpa ⟨v₀, v₁, v₂, v₃, v₄, hnd, h01, h12, h23, h34,
          (Equiv.swap col_u col_v).injective hc1, (Equiv.swap col_u col_v).injective hc2⟩
    · rintro ⟨v₀, v₁, v₂, v₃, hnd, h01, h12, h23, h30, hc1, hc2⟩
      by_cases hr0 : G'.Reachable u v₀
      · have hr1 : G'.Reachable u v₁ := hr0.trans (SimpleGraph.Adj.reachable h01)
        have hr2 : G'.Reachable u v₂ := hr1.trans (SimpleGraph.Adj.reachable h12)
        have hr3 : G'.Reachable u v₃ := hr2.trans (SimpleGraph.Adj.reachable h23)
        rw [hc''_get_U v₀ v₁ h01 hr0, hc''_get_U v₂ v₃ h23 hr2] at hc1
        rw [hc''_get_U v₁ v₂ h12 hr1, hc''_get_U v₃ v₀ h30 hr3] at hc2
        exact hcy ⟨v₀, v₁, v₂, v₃, hnd, h01, h12, h23, h30, hc1, hc2⟩
      · have hr1 : ¬ G'.Reachable u v₁ := fun h => hr0 (h.trans (SimpleGraph.Adj.reachable h01).symm)
        have hr2 : ¬ G'.Reachable u v₂ := fun h => hr1 (h.trans (SimpleGraph.Adj.reachable h12).symm)
        have hr3 : ¬ G'.Reachable u v₃ := fun h => hr2 (h.trans (SimpleGraph.Adj.reachable h23).symm)
        rw [hc''_get_nU v₀ v₁ h01 hr0, hc''_get_nU v₂ v₃ h23 hr2] at hc1
        rw [hc''_get_nU v₁ v₂ h12 hr1, hc''_get_nU v₃ v₀ h30 hr3] at hc2
        exact hcy ⟨v₀, v₁, v₂, v₃, hnd, h01, h12, h23, h30,
          (Equiv.swap col_u col_v).injective hc1, (Equiv.swap col_u col_v).injective hc2⟩
  let c : EdgeColoring G (Fin 7) := fun e =>
    if he : e.1 = s(u, v) then col_u
    else c'' ⟨e.1, by
      rcases e with ⟨⟨x, y⟩, hxy⟩
      exact SimpleGraph.deleteEdges_adj.mpr ⟨hxy, he⟩⟩
  refine ⟨c, OPG37271.isStarEdgeColoring_insert_edge u v huv c ?_ ?_⟩
  · have heq : (fun e => c ⟨e.1, SimpleGraph.edgeSet_mono (SimpleGraph.deleteEdges_le {s(u, v)}) e.2⟩ :
        EdgeColoring G' (Fin 7)) = c'' := by
      funext ⟨e, he⟩
      have hne : e ≠ s(u, v) := by
        rcases e with ⟨x, y⟩
        exact (SimpleGraph.deleteEdges_adj.mp he).2
      simp only [c, dif_neg hne]
    rw [heq]
    exact hc''_star
  · intro x y hxy hne hdist
    have hxy' : G'.Adj x y := SimpleGraph.deleteEdges_adj.mpr ⟨hxy, hne⟩
    have hc_xy : c.get x y hxy = c''.get x y hxy' := by
      simp only [SimpleGraph.EdgeLabeling.get, c, dif_neg hne]
    have hc_uv : c.get u v huv = col_u := by
      simp only [SimpleGraph.EdgeLabeling.get, c, dif_pos rfl]
    rw [hc_xy, hc_uv]
    have hmem_S : ∀ a : V, (x = a ∨ y = a ∨ G'.Adj a x ∨ G'.Adj a y) → s(x, y) ∈ S a := by
      intro a ha
      rw [Finset.mem_biUnion]
      rcases ha with rfl | rfl | hax | hay
      · refine ⟨y, (SimpleGraph.mem_neighborFinset G' x y).mpr hxy', Finset.mem_image.mpr ⟨x, (SimpleGraph.mem_neighborFinset G' y x).mpr hxy'.symm, ?_⟩⟩
        exact Sym2.eq_swap
      · refine ⟨x, (SimpleGraph.mem_neighborFinset G' y x).mpr hxy'.symm, Finset.mem_image.mpr ⟨y, (SimpleGraph.mem_neighborFinset G' x y).mpr hxy', rfl⟩⟩
      · refine ⟨x, (SimpleGraph.mem_neighborFinset G' a x).mpr hax, Finset.mem_image.mpr ⟨y, (SimpleGraph.mem_neighborFinset G' x y).mpr hxy', rfl⟩⟩
      · refine ⟨y, (SimpleGraph.mem_neighborFinset G' a y).mpr hay, Finset.mem_image.mpr ⟨x, (SimpleGraph.mem_neighborFinset G' y x).mpr hxy'.symm, ?_⟩⟩
        exact Sym2.eq_swap
    by_cases hrx : G'.Reachable u x
    · rw [hc''_get_U x y hxy' hrx]
      have hry : G'.Reachable u y := hrx.trans (SimpleGraph.Adj.reachable hxy')
      have hdist_u : x = u ∨ y = u ∨ G'.Adj u x ∨ G'.Adj u y := by
        by_cases hxu : x = u; · exact Or.inl hxu
        by_cases hyu : y = u; · exact Or.inr (Or.inl hyu)
        rcases hdist with rfl | rfl | rfl | rfl | hux | hvx | huy | hvy
        · exact absurd rfl hxu
        · exact absurd hrx hbridge
        · exact absurd rfl hyu
        · exact absurd hry hbridge
        · exact Or.inr (Or.inr (Or.inl (SimpleGraph.deleteEdges_adj.mpr ⟨hux, by
            intro heq; rw [Set.mem_singleton_iff, Sym2.eq_iff] at heq
            rcases heq with ⟨_, h2⟩ | ⟨h1, _⟩
            · rw [h2] at hrx; exact hbridge hrx
            · exact huv.ne h1⟩)))
        · exact absurd (hrx.trans (SimpleGraph.Adj.reachable (SimpleGraph.deleteEdges_adj.mpr ⟨hvx, by
            intro heq; rw [Set.mem_singleton_iff, Sym2.eq_iff] at heq
            rcases heq with ⟨h1, _⟩ | ⟨_, h2⟩
            · exact huv.ne h1.symm
            · exact hxu h2⟩)).symm) hbridge
        · exact Or.inr (Or.inr (Or.inr (SimpleGraph.deleteEdges_adj.mpr ⟨huy, by
            intro heq; rw [Set.mem_singleton_iff, Sym2.eq_iff] at heq
            rcases heq with ⟨_, h2⟩ | ⟨h1, _⟩
            · rw [h2] at hry; exact hbridge hry
            · exact huv.ne h1⟩)))
        · exact absurd (hry.trans (SimpleGraph.Adj.reachable (SimpleGraph.deleteEdges_adj.mpr ⟨hvy, by
            intro heq; rw [Set.mem_singleton_iff, Sym2.eq_iff] at heq
            rcases heq with ⟨h1, _⟩ | ⟨_, h2⟩
            · exact huv.ne h1.symm
            · exact hyu h2⟩)).symm) hbridge
      exact hcol_u (s(x, y)) (hmem_S u hdist_u) hxy'
    · rw [hc''_get_nU x y hxy' hrx]
      have hnry : ¬ G'.Reachable u y := fun h => hrx (h.trans (SimpleGraph.Adj.reachable hxy').symm)
      have hdist_v : x = v ∨ y = v ∨ G'.Adj v x ∨ G'.Adj v y := by
        by_cases hxv : x = v; · exact Or.inl hxv
        by_cases hyv : y = v; · exact Or.inr (Or.inl hyv)
        rcases hdist with rfl | rfl | rfl | rfl | hux | hvx | huy | hvy
        · exact absurd SimpleGraph.Reachable.rfl hrx
        · exact absurd rfl hxv
        · exact absurd SimpleGraph.Reachable.rfl hnry
        · exact absurd rfl hyv
        · exact absurd (SimpleGraph.Adj.reachable (SimpleGraph.deleteEdges_adj.mpr ⟨hux, by
            intro heq; rw [Set.mem_singleton_iff, Sym2.eq_iff] at heq
            rcases heq with ⟨_, h2⟩ | ⟨h1, _⟩
            · exact hxv h2
            · exact huv.ne h1⟩)) hrx
        · exact Or.inr (Or.inr (Or.inl (SimpleGraph.deleteEdges_adj.mpr ⟨hvx, by
            intro heq; rw [Set.mem_singleton_iff, Sym2.eq_iff] at heq
            rcases heq with ⟨h1, _⟩ | ⟨_, h2⟩
            · exact huv.ne h1.symm
            · exact hrx (h2 ▸ SimpleGraph.Reachable.rfl)⟩)))
        · exact absurd (SimpleGraph.Adj.reachable (SimpleGraph.deleteEdges_adj.mpr ⟨huy, by
            intro heq; rw [Set.mem_singleton_iff, Sym2.eq_iff] at heq
            rcases heq with ⟨_, h2⟩ | ⟨h1, _⟩
            · exact hyv h2
            · exact huv.ne h1⟩)) hnry
        · exact Or.inr (Or.inr (Or.inr (SimpleGraph.deleteEdges_adj.mpr ⟨hvy, by
            intro heq; rw [Set.mem_singleton_iff, Sym2.eq_iff] at heq
            rcases heq with ⟨h1, _⟩ | ⟨_, h2⟩
            · exact huv.ne h1.symm
            · exact hnry (h2 ▸ SimpleGraph.Reachable.rfl)⟩)))
      have hne_v := hcol_v (s(x, y)) (hmem_S v hdist_v) hxy'
      intro heq
      apply hne_v
      have heq' := congrArg (Equiv.swap col_u col_v) heq
      change c'.get x y hxy' = col_v
      simpa using heq'
