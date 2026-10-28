-- Prove2me | solution 1 for WilliamsonShmoys.edge_upper_bound_from_connected_case
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T06:54:27.273067+00:00
-- url     : https://prove2.me/submissions/ea32663e-28b7-4055-9977-8a0d41d6993c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

namespace S81Conn

variable {V : Type} [Fintype V] [LinearOrder V]

theorem draw_induce (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) (S : Set V) [Fintype S] :
    HasPlanarDrawingOn (G.induce S) := by
  obtain ⟨p, arc, hp, h1, h2⟩ := hG
  refine ⟨fun x => p x.1, fun x y => arc x.1 y.1, hp.comp Subtype.val_injective, ?_, ?_⟩
  · intro u v huv hadj
    obtain ⟨a, b, c, d, e⟩ := h1 u.1 v.1 huv hadj
    exact ⟨a, b, c, d, fun t ht w => e t ht w.1⟩
  · intro u v x y huv hxy ha hb hne t ht s hs heq
    refine h2 u.1 v.1 x.1 y.1 huv hxy ha hb ?_ t ht s hs heq
    intro h
    apply hne
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨Subtype.ext h.1, Subtype.ext h.2⟩

/-- edges of `G` inside `S` -/
def E (G : SimpleGraph V) (S : Set V) : Set (Sym2 V) := G.edgeSet ∩ {e | ∀ v ∈ e, v ∈ S}

theorem ncard_induce (G : SimpleGraph V) (S : Set V) :
    (G.induce S).edgeSet.ncard = (E G S).ncard := by
  have hinj : Function.Injective (Sym2.map (Subtype.val : S → V)) :=
    Sym2.map.injective Subtype.val_injective
  rw [← Set.ncard_image_of_injective _ hinj]
  congr 1
  ext e
  constructor
  · rintro ⟨f, hf, rfl⟩
    induction f using Sym2.ind with
    | _ x y =>
    simp only [Sym2.map_pair_eq, E, Set.mem_inter_iff, SimpleGraph.mem_edgeSet, Set.mem_setOf_eq,
      Sym2.mem_iff] at hf ⊢
    refine ⟨by simpa using hf, ?_⟩
    rintro v (rfl | rfl)
    · exact x.2
    · exact y.2
  · induction e using Sym2.ind with
    | _ a b =>
    rintro ⟨h1, h2⟩
    have ha : a ∈ S := h2 a (Sym2.mem_mk_left a b)
    have hb : b ∈ S := h2 b (Sym2.mem_mk_right a b)
    exact ⟨s(⟨a, ha⟩, ⟨b, hb⟩), by simpa using h1, by simp⟩


theorem E_union (G : SimpleGraph V) (S C : Finset V) (hCS : C ⊆ S)
    (hcl : ∀ u w, u ∈ C → w ∈ S → G.Adj u w → w ∈ C) :
    (E G (S : Set V)).ncard = (E G (C : Set V)).ncard + (E G ((S \ C : Finset V) : Set V)).ncard := by
  have hcl' : ∀ u w, u ∈ S \ C → w ∈ S → G.Adj u w → w ∈ S \ C := by
    intro u w hu hw hadj
    rw [Finset.mem_sdiff] at hu ⊢
    refine ⟨hw, fun hwC => hu.2 (hcl w u hwC hu.1 hadj.symm)⟩
  have hU : E G (S : Set V) = E G (C : Set V) ∪ E G ((S \ C : Finset V) : Set V) := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
    simp only [E, Set.mem_union, Set.mem_inter_iff, SimpleGraph.mem_edgeSet, Set.mem_setOf_eq,
      Sym2.mem_iff, Finset.mem_coe]
    constructor
    · rintro ⟨hab, h⟩
      have ha := h a (Or.inl rfl)
      have hb := h b (Or.inr rfl)
      by_cases haC : a ∈ C
      · left
        have hbC := hcl a b haC hb hab
        exact ⟨hab, by rintro v (rfl | rfl) <;> assumption⟩
      · right
        have ha' : a ∈ S \ C := Finset.mem_sdiff.mpr ⟨ha, haC⟩
        have hb' := hcl' a b ha' hb hab
        exact ⟨hab, by rintro v (rfl | rfl) <;> assumption⟩
    · rintro (⟨hab, h⟩ | ⟨hab, h⟩)
      · exact ⟨hab, fun v hv => hCS (h v hv)⟩
      · exact ⟨hab, fun v hv => (Finset.mem_sdiff.mp (h v hv)).1⟩
  have hD : Disjoint (E G (C : Set V)) (E G ((S \ C : Finset V) : Set V)) := by
    rw [Set.disjoint_left]
    intro e h1 h2
    induction e using Sym2.ind with
    | _ a b =>
    have := h1.2 a (Sym2.mem_mk_left a b)
    have := (Finset.mem_sdiff.mp (h2.2 a (Sym2.mem_mk_left a b))).2
    contradiction
  rw [hU, Set.ncard_union_eq hD (Set.toFinite _) (Set.toFinite _)]

theorem small (G : SimpleGraph V) (S : Finset V) :
    (E G (S : Set V)).ncard ≤ S.card.choose 2 := by
  classical
  rw [← ncard_induce, ← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  have := SimpleGraph.card_edgeFinset_le_card_choose_two (G := G.induce (S : Set V))
  simpa using this

theorem key (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hConnected : ∀ {W : Type} [Fintype W] [LinearOrder W]
      (H : SimpleGraph W), H.Connected → HasPlanarDrawingOn H →
      3 <= Fintype.card W →
      (H.edgeSet.ncard : Int) <= 3 * (Fintype.card W : Int) - 6) :
    ∀ n, ∀ S : Finset V, S.card = n → S.Nonempty →
      (E G (S : Set V)).ncard + 3 ≤ 3 * S.card ∧
      (¬ (G.induce (S : Set V)).Connected → (E G (S : Set V)).ncard + 6 ≤ 3 * S.card) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hSn hSne
  obtain ⟨v, hv⟩ := hSne
  set C : Finset V := S.filter (fun w => ∃ hw : w ∈ S,
    (G.induce (S : Set V)).Reachable ⟨v, hv⟩ ⟨w, hw⟩) with hCdef
  have hCS : C ⊆ S := Finset.filter_subset _ _
  have hvC : v ∈ C := Finset.mem_filter.mpr ⟨hv, hv, SimpleGraph.Reachable.refl _⟩
  have hcl : ∀ u w, u ∈ C → w ∈ S → G.Adj u w → w ∈ C := by
    intro u w hu hw hadj
    obtain ⟨hu1, hu2, hr⟩ := Finset.mem_filter.mp hu
    refine Finset.mem_filter.mpr ⟨hw, hw, hr.trans ?_⟩
    exact SimpleGraph.Adj.reachable (G := G.induce (S : Set V)) (u := ⟨u, hu2⟩) (v := ⟨w, hw⟩)
      (by simpa using hadj)
  -- the split case
  have split : C ≠ S → (E G (S : Set V)).ncard + 6 ≤ 3 * S.card := by
    intro hne
    have hDne : (S \ C).Nonempty := by
      rw [Finset.sdiff_nonempty]
      intro h; exact hne (Finset.Subset.antisymm hCS h)
    have hcardS : S.card = C.card + (S \ C).card := by
      rw [Finset.card_sdiff_of_subset hCS]; have := Finset.card_le_card hCS; omega
    have hC1 : 0 < (S \ C).card := Finset.card_pos.mpr hDne
    have hC2 : 0 < C.card := Finset.card_pos.mpr ⟨v, hvC⟩
    have h1 := (ih C.card (by omega) C rfl ⟨v, hvC⟩).1
    have h2 := (ih (S \ C).card (by omega) (S \ C) rfl hDne).1
    rw [E_union G S C hCS hcl]
    omega
  constructor
  · by_cases hCS' : C = S
    · by_cases h3 : 3 ≤ S.card
      · have hconn : (G.induce (S : Set V)).Connected := by
          have hpre : (G.induce (S : Set V)).Preconnected := by
            intro a b
            have ha : a.1 ∈ C := by rw [hCS']; exact Finset.mem_coe.mp a.2
            have hb : b.1 ∈ C := by rw [hCS']; exact Finset.mem_coe.mp b.2
            obtain ⟨_, _, hra⟩ := Finset.mem_filter.mp ha
            obtain ⟨_, _, hrb⟩ := Finset.mem_filter.mp hb
            exact hra.symm.trans hrb
          haveI : Nonempty (↑(S : Set V)) := ⟨⟨v, hv⟩⟩; exact ⟨hpre⟩
        have := hConnected (G.induce (S : Set V)) hconn (draw_induce G hG _) (by simpa using h3)
        rw [ncard_induce] at this
        have hc : Fintype.card (↑(S : Set V)) = S.card := by simp
        rw [hc] at this
        omega
      · have hs := small G S
        have hpos : 0 < S.card := Finset.card_pos.mpr ⟨v, hv⟩
        interval_cases h : S.card
        · rw [show Nat.choose 1 2 = 0 from rfl] at hs; omega
        · rw [show Nat.choose 2 2 = 1 from rfl] at hs; omega
    · have := split hCS'; omega
  · intro hnc
    apply split
    intro hCS'
    apply hnc
    have hpre : (G.induce (S : Set V)).Preconnected := by
      intro a b
      have ha : a.1 ∈ C := by rw [hCS']; exact Finset.mem_coe.mp a.2
      have hb : b.1 ∈ C := by rw [hCS']; exact Finset.mem_coe.mp b.2
      obtain ⟨_, _, hra⟩ := Finset.mem_filter.mp ha
      obtain ⟨_, _, hrb⟩ := Finset.mem_filter.mp hb
      exact hra.symm.trans hrb
    haveI : Nonempty (↑(S : Set V)) := ⟨⟨v, hv⟩⟩; exact ⟨hpre⟩

end S81Conn

open S81Conn in
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hCard : 3 <= Fintype.card V)
    (hConnected : ∀ {W : Type} [Fintype W] [LinearOrder W]
      (H : SimpleGraph W), H.Connected → HasPlanarDrawingOn H →
      3 <= Fintype.card W →
      (H.edgeSet.ncard : Int) <= 3 * (Fintype.card W : Int) - 6) :
    (G.edgeSet.ncard : Int) <= 3 * (Fintype.card V : Int) - 6 := by
  classical
  have hE : E G ((Finset.univ : Finset V) : Set V) = G.edgeSet := by
    ext e; simp [E]
  have hne : (Finset.univ : Finset V).Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by omega))
  have hk := key G hG hConnected _ Finset.univ rfl hne
  rw [hE, Finset.card_univ] at hk
  by_cases hc : (G.induce ((Finset.univ : Finset V) : Set V)).Connected
  · have := hConnected _ hc (draw_induce G hG _) (by simpa using hCard)
    rw [ncard_induce, hE] at this
    have hc' : Fintype.card (↑((Finset.univ : Finset V) : Set V)) = Fintype.card V := by simp
    rw [hc'] at this
    exact this
  · have := hk.2 hc
    omega
