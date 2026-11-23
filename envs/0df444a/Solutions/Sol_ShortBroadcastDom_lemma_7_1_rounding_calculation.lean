-- Prove2me | solution 1 for ShortBroadcastDom.lemma_7_1_rounding_calculation
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:28:11.735579+00:00
-- url     : https://prove2.me/submissions/bc779153-cb23-4783-a636-dc3c28bb3520

import Definitions.Def_ShortBroadcastDom_SubgraphDensityLE
import Definitions.Def_ShortBroadcastDom_RoundingData

open ShortBroadcastDom

namespace Aux_7_1

lemma mem_closedNbhd_comm {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    u ∈ closedNbhd G v ↔ v ∈ closedNbhd G u := by
  simp only [closedNbhd, Finset.mem_insert, SimpleGraph.mem_neighborFinset]
  exact ⟨fun h => h.elim (fun huv => Or.inl huv.symm) (fun hadj => Or.inr hadj.symm),
         fun h => h.elim (fun hvu => Or.inl hvu.symm) (fun hadj => Or.inr hadj.symm)⟩

lemma self_mem_closedNbhd {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    v ∈ closedNbhd G v := by
  simp [closedNbhd]

end Aux_7_1

theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : RoundingData V) (hset : IsRoundingSetting G d) (hdens : SubgraphDensityLE d.a G)
    (hH : ∀ v ∈ d.H G, d.c v = d.b) (hO : ∀ v ∈ d.O G, (d.h G v : ℝ) ≤ d.c v) :
    DominatesSet G d.R0 (d.D G) ∧
    ∑ v ∈ d.H G, ((d.h G v : ℝ) - d.b) + (d.a + 1) * ((d.H G \ d.R G).card : ℝ) ≤
      d.a * (d.ell G : ℝ) ∧
    ((d.U G).card : ℝ) ≤ ∑ v ∈ d.O G, (d.h G v : ℝ) * d.x v ∧
    ((d.wCard : ℝ) + (d.ell G : ℝ)) / (d.a + 1) + d.P G ≤ d.cost - ((d.D G).card : ℝ) := by
  classical
  let _ := hO
  rcases hset with ⟨ha, hR0C, _hc, hx_feas⟩
  rcases hx_feas with ⟨hx_bounds, hx_cov⟩
  let W : Finset V := d.W
  let R : Finset V := d.R G
  let H : Finset V := d.H G
  let U : Finset V := d.U G
  let D : Finset V := d.D G
  let O : Finset V := d.O G
  let L : Finset V := d.L G
  let Q : Finset V := H ∩ R

  -- 1. DominatesSet G d.R0 D
  have hdom : DominatesSet G d.R0 D := by
    intro r hr0
    by_cases hW_cov : ∃ w ∈ W, r ∈ closedNbhd G w
    · rcases hW_cov with ⟨w, hwW, hrw⟩
      exact ⟨w, Finset.mem_union_left _ (Finset.mem_union_left _ hwW), hrw⟩
    · have hW_none : ∀ w ∈ W, r ∉ closedNbhd G w := fun w hw hrw => hW_cov ⟨w, hw, hrw⟩
      have hrR : r ∈ R := Finset.mem_filter.mpr ⟨hr0, hW_none⟩
      by_cases hH_cov : ∃ v ∈ H, r ∈ closedNbhd G v
      · rcases hH_cov with ⟨v, hvH, hrv⟩
        exact ⟨v, Finset.mem_union_left _ (Finset.mem_union_right _ hvH), hrv⟩
      · have hH_none : ∀ v ∈ H, r ∉ closedNbhd G v := fun v hv hrv => hH_cov ⟨v, hv, hrv⟩
        have hrU : r ∈ U := Finset.mem_filter.mpr ⟨hrR, hH_none⟩
        exact ⟨r, Finset.mem_union_right _ hrU, Aux_7_1.self_mem_closedNbhd G r⟩

  -- Basic subset & disjointness relations
  have hW_sub_C : W ⊆ d.C := Finset.filter_subset _ _
  have hH_sub_CW : H ⊆ d.C \ W := Finset.filter_subset _ _
  have hO_sub_C : O ⊆ d.C := Finset.sdiff_subset
  have hR_sub_R0 : R ⊆ d.R0 := Finset.filter_subset _ _
  have hU_sub_R : U ⊆ R := Finset.filter_subset _ _
  have hdisj_WH : Disjoint W H := by
    rw [Finset.disjoint_left]
    intro v hvW hvH
    exact (Finset.mem_sdiff.mp (hH_sub_CW hvH)).2 hvW
  have hdisj_WR : Disjoint W R := by
    rw [Finset.disjoint_left]
    intro v hvW hvR
    exact (Finset.mem_filter.mp hvR).2 v hvW (Aux_7_1.self_mem_closedNbhd G v)
  have hdisj_WU : Disjoint W U := hdisj_WR.mono_right hU_sub_R
  have hdisj_HU : Disjoint H U := by
    rw [Finset.disjoint_left]
    intro v hvH hvU
    exact (Finset.mem_filter.mp hvU).2 v hvH (Aux_7_1.self_mem_closedNbhd G v)
  have hdisj_QU : Disjoint Q U := hdisj_HU.mono_left Finset.inter_subset_left
  have hdisj_HL : Disjoint H L := by
    rw [Finset.disjoint_left]
    intro v hvH hvL
    exact (Finset.mem_sdiff.mp hvL).2 (Finset.mem_union_left _ hvH)

  have hD_card : D.card = W.card + H.card + U.card := by
    change (W ∪ H ∪ U).card = W.card + H.card + U.card
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hdisj_WU, hdisj_HU⟩),
      Finset.card_union_of_disjoint hdisj_WH]
  have hH_card : H.card = Q.card + (H \ R).card :=
    (Finset.card_inter_add_card_sdiff H R).symm
  have hR_part : Q ∪ U ∪ L = R := by
    ext r
    change r ∈ (H ∩ R) ∪ U ∪ (R \ (H ∪ U)) ↔ r ∈ R
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · rintro ((⟨_, hrR⟩ | hrU) | ⟨hrR, _⟩)
      · exact hrR
      · exact hU_sub_R hrU
      · exact hrR
    · intro hrR
      by_cases hrHU : r ∈ H ∪ U
      · rw [Finset.mem_union] at hrHU
        rcases hrHU with hrH | hrU
        · exact Or.inl (Or.inl ⟨hrH, hrR⟩)
        · exact Or.inl (Or.inr hrU)
      · rw [Finset.mem_union] at hrHU
        exact Or.inr ⟨hrR, hrHU⟩
  have hdisj_QUL : Disjoint (Q ∪ U) L := by
    rw [Finset.disjoint_left]
    intro r hrQU hrL
    have hrHU : r ∈ H ∪ U := by
      rcases Finset.mem_union.mp hrQU with hrQ | hrU
      · exact Finset.mem_union_left _ (Finset.mem_inter.mp hrQ).1
      · exact Finset.mem_union_right _ hrU
    exact (Finset.mem_sdiff.mp hrL).2 hrHU
  have hR_card : R.card = Q.card + U.card + L.card := by
    rw [← hR_part, Finset.card_union_of_disjoint hdisj_QUL, Finset.card_union_of_disjoint hdisj_QU]
  have hD_real : (D.card : ℝ) = (d.wCard : ℝ) + (R.card : ℝ) - (d.ell G : ℝ) + ((H \ R).card : ℝ) := by
    have hw_eq : d.wCard = W.card := rfl
    have hell_eq : d.ell G = L.card := rfl
    have h1 : (D.card : ℝ) = (W.card : ℝ) + (H.card : ℝ) + (U.card : ℝ) := by exact_mod_cast hD_card
    have h2 : (H.card : ℝ) = (Q.card : ℝ) + ((H \ R).card : ℝ) := by exact_mod_cast hH_card
    have h3 : (R.card : ℝ) = (Q.card : ℝ) + (U.card : ℝ) + (L.card : ℝ) := by exact_mod_cast hR_card
    rw [hw_eq, hell_eq]
    linarith

  -- 2. Inequality (19)
  have hineq19 : ∑ v ∈ H, ((d.h G v : ℝ) - d.b) + (d.a + 1) * ((H \ R).card : ℝ) ≤
      d.a * (d.ell G : ℝ) := by
    have hh_eq : ∀ v ∈ H, d.h G v = (if v ∈ Q then 1 else 0) +
        (G.neighborFinset v ∩ (Q ∪ L)).card := by
      intro v hvH
      have hR_sub_QL : closedNbhd G v ∩ R = closedNbhd G v ∩ (Q ∪ L) := by
        ext u
        simp only [Finset.mem_inter]
        constructor
        · rintro ⟨huv, huR⟩
          refine ⟨huv, ?_⟩
          rw [← hR_part] at huR
          rcases Finset.mem_union.mp huR with huQU | huL
          · rcases Finset.mem_union.mp huQU with huQ | huU
            · exact Finset.mem_union_left _ huQ
            · exfalso
              exact (Finset.mem_filter.mp huU).2 v hvH huv
          · exact Finset.mem_union_right _ huL
        · rintro ⟨huv, huQL⟩
          refine ⟨huv, ?_⟩
          rcases Finset.mem_union.mp huQL with huQ | huL
          · exact (Finset.mem_inter.mp huQ).2
          · exact (Finset.mem_sdiff.mp huL).1
      change (closedNbhd G v ∩ R).card = _
      rw [hR_sub_QL]
      have hv_not_nbr : v ∉ G.neighborFinset v ∩ (Q ∪ L) :=
        fun h => G.notMem_neighborFinset_self v (Finset.mem_inter.mp h).1
      have hvQL_iff : v ∈ Q ∪ L ↔ v ∈ Q := by
        constructor
        · intro hvQL
          rcases Finset.mem_union.mp hvQL with hvQ | hvL
          · exact hvQ
          · exact False.elim (Finset.disjoint_left.mp hdisj_HL hvH hvL)
        · exact fun hvQ => Finset.mem_union_left _ hvQ
      by_cases hvQ : v ∈ Q
      · have hvQL : v ∈ Q ∪ L := hvQL_iff.mpr hvQ
        have hset_eq : closedNbhd G v ∩ (Q ∪ L) = insert v (G.neighborFinset v ∩ (Q ∪ L)) := by
          ext w
          simp only [closedNbhd, Finset.mem_inter, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hw, hwQL⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨hw, hwQL⟩
          · rintro (rfl | ⟨hw, hwQL⟩)
            · exact ⟨Or.inl rfl, hvQL⟩
            · exact ⟨Or.inr hw, hwQL⟩
        rw [hset_eq, Finset.card_insert_of_notMem hv_not_nbr]
        simp [hvQ, Nat.add_comm]
      · have hvQL : v ∉ Q ∪ L := fun h => hvQ (hvQL_iff.mp h)
        have hset_eq : closedNbhd G v ∩ (Q ∪ L) = G.neighborFinset v ∩ (Q ∪ L) := by
          ext w
          simp only [closedNbhd, Finset.mem_inter, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hw, hwQL⟩
            · exact False.elim (hvQL hwQL)
            · exact ⟨hw, hwQL⟩
          · rintro ⟨hw, hwQL⟩
            exact ⟨Or.inr hw, hwQL⟩
        rw [hset_eq]
        simp [hvQ]
    let P : Finset (V × V) := (H ×ˢ (Q ∪ L)).filter fun p => G.Adj p.1 p.2
    have hP_card : P.card = ∑ v ∈ H, (G.neighborFinset v ∩ (Q ∪ L)).card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro v _
      rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
      congr 1
      ext u
      simp [Finset.mem_inter, SimpleGraph.mem_neighborFinset, and_comm]
    let ord : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
    let P1 : Finset (V × V) := P.filter fun p =>
      ¬ (p.1 ∈ Q ∧ p.2 ∈ Q) ∨ (ord p.1).val < (ord p.2).val
    let P2 : Finset (V × V) := P.filter fun p =>
      (p.1 ∈ Q ∧ p.2 ∈ Q) ∧ (ord p.2).val < (ord p.1).val
    have hP_split : P.card = P1.card + P2.card := by
      have hdisj : Disjoint P1 P2 := by
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        rcases (Finset.mem_filter.mp hp1).2 with hnot | hlt1
        · exact hnot (Finset.mem_filter.mp hp2).2.1
        · have hlt2 := (Finset.mem_filter.mp hp2).2.2
          omega
      have hunion : P1 ∪ P2 = P := by
        ext p
        simp only [P1, P2, Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
        · intro hp
          have hadj : G.Adj p.1 p.2 := (Finset.mem_filter.mp hp).2
          have hne : (ord p.1).val ≠ (ord p.2).val := by
            intro heq
            exact G.ne_of_adj hadj (ord.injective (Fin.ext heq))
          by_cases hQQ : p.1 ∈ Q ∧ p.2 ∈ Q
          · rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
            · exact Or.inl ⟨hp, Or.inr hlt⟩
            · exact Or.inr ⟨hp, ⟨hQQ, hgt⟩⟩
          · exact Or.inl ⟨hp, Or.inl hQQ⟩
      rw [← hunion, Finset.card_union_of_disjoint hdisj]
    have hH_inter_QL : ∀ x, x ∈ H → x ∈ Q ∪ L → x ∈ Q := by
      intro x hxH hxQL
      rcases Finset.mem_union.mp hxQL with hxQ | hxL
      · exact hxQ
      · exact False.elim (Finset.disjoint_left.mp hdisj_HL hxH hxL)
    let eHL : Set (Sym2 V) := {e | e ∈ G.edgeSet ∧ ∀ w ∈ e, w ∈ H ∪ L}
    let eQ : Set (Sym2 V) := {e | e ∈ G.edgeSet ∧ ∀ w ∈ e, w ∈ Q}
    have hP1_le : P1.card ≤ eHL.ncard := by
      let f1 : P1 → Sym2 V := fun p => s(p.1.1, p.1.2)
      have hf1_inj : Function.Injective f1 := by
        intro a b hab
        rcases Finset.mem_filter.mp a.2 with ⟨haP, haCond⟩
        rcases Finset.mem_filter.mp b.2 with ⟨hbP, hbCond⟩
        rcases Finset.mem_filter.mp haP with ⟨haProd, _⟩
        rcases Finset.mem_filter.mp hbP with ⟨hbProd, _⟩
        rcases Finset.mem_product.mp haProd with ⟨ha1H, ha2QL⟩
        rcases Finset.mem_product.mp hbProd with ⟨hb1H, hb2QL⟩
        rcases Sym2.eq_iff.mp hab with ⟨h1, h2⟩ | ⟨h12, h21⟩
        · exact Subtype.ext (Prod.ext h1 h2)
        · have ha1Q : a.1.1 ∈ Q := hH_inter_QL a.1.1 ha1H (h12.symm ▸ hb2QL)
          have ha2Q : a.1.2 ∈ Q := hH_inter_QL a.1.2 (h21.symm ▸ hb1H) ha2QL
          have hb1Q : b.1.1 ∈ Q := h21 ▸ ha2Q
          have hb2Q : b.1.2 ∈ Q := h12 ▸ ha1Q
          have hlt1 : (ord a.1.1).val < (ord a.1.2).val :=
            haCond.resolve_left (not_not.mpr ⟨ha1Q, ha2Q⟩)
          have hlt2 : (ord b.1.1).val < (ord b.1.2).val :=
            hbCond.resolve_left (not_not.mpr ⟨hb1Q, hb2Q⟩)
          rw [← h21, ← h12] at hlt2
          omega
      let img1 : Finset (Sym2 V) := P1.attach.map ⟨f1, hf1_inj⟩
      have himg1_sub : (img1 : Set (Sym2 V)) ⊆ eHL := by
        intro e he
        rcases Finset.mem_map.mp (Finset.mem_coe.mp he) with ⟨p, -, rfl⟩
        rcases Finset.mem_filter.mp (Finset.mem_filter.mp p.2).1 with ⟨hpProd, hadj⟩
        rcases Finset.mem_product.mp hpProd with ⟨hp1H, hp2QL⟩
        refine ⟨G.mem_edgeSet.mpr hadj, fun w hw => ?_⟩
        rcases Sym2.mem_iff.mp hw with rfl | rfl
        · exact Finset.mem_union_left _ hp1H
        · rcases Finset.mem_union.mp hp2QL with hp2Q | hp2L
          · exact Finset.mem_union_left _ (Finset.mem_inter.mp hp2Q).1
          · exact Finset.mem_union_right _ hp2L
      have hle := Set.ncard_le_ncard himg1_sub (Set.toFinite eHL)
      rwa [Set.ncard_coe_finset, Finset.card_map, Finset.card_attach] at hle
    have hP2_le : P2.card ≤ eQ.ncard := by
      let f2 : P2 → Sym2 V := fun p => s(p.1.1, p.1.2)
      have hf2_inj : Function.Injective f2 := by
        intro a b hab
        rcases (Finset.mem_filter.mp a.2).2 with ⟨_, haLt⟩
        rcases (Finset.mem_filter.mp b.2).2 with ⟨_, hbLt⟩
        rcases Sym2.eq_iff.mp hab with ⟨h1, h2⟩ | ⟨h12, h21⟩
        · exact Subtype.ext (Prod.ext h1 h2)
        · rw [← h21, ← h12] at hbLt
          omega
      let img2 : Finset (Sym2 V) := P2.attach.map ⟨f2, hf2_inj⟩
      have himg2_sub : (img2 : Set (Sym2 V)) ⊆ eQ := by
        intro e he
        rcases Finset.mem_map.mp (Finset.mem_coe.mp he) with ⟨p, -, rfl⟩
        have hpP := (Finset.mem_filter.mp p.2).1
        have hpQQ := (Finset.mem_filter.mp p.2).2.1
        have hadj := (Finset.mem_filter.mp hpP).2
        refine ⟨G.mem_edgeSet.mpr hadj, fun w hw => ?_⟩
        rcases Sym2.mem_iff.mp hw with rfl | rfl
        · exact hpQQ.1
        · exact hpQQ.2
      have hle := Set.ncard_le_ncard himg2_sub (Set.toFinite eQ)
      rwa [Set.ncard_coe_finset, Finset.card_map, Finset.card_attach] at hle
    have hsum_h_nat : ∑ v ∈ H, d.h G v = Q.card + P1.card + P2.card := by
      have h1 : ∑ v ∈ H, d.h G v =
          (∑ v ∈ H, if v ∈ Q then 1 else 0) + ∑ v ∈ H, (G.neighborFinset v ∩ (Q ∪ L)).card := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl hh_eq
      have h2 : (∑ v ∈ H, if v ∈ Q then 1 else 0) = Q.card := by
        rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
        congr 1
        ext v
        simp only [Q, Finset.mem_filter, Finset.mem_inter]
        exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
      rw [h1, h2, ← hP_card, hP_split]
      omega
    have hHL_card : (H ∪ L).card = H.card + L.card := Finset.card_union_of_disjoint hdisj_HL
    have hd_eHL : (eHL.ncard : ℝ) ≤ d.a * ((H ∪ L).card : ℝ) := hdens (H ∪ L)
    have hd_eQ : (eQ.ncard : ℝ) ≤ d.a * (Q.card : ℝ) := hdens Q
    have hP1_r : (P1.card : ℝ) ≤ (eHL.ncard : ℝ) := by exact_mod_cast hP1_le
    have hP2_r : (P2.card : ℝ) ≤ (eQ.ncard : ℝ) := by exact_mod_cast hP2_le
    have hsum_h_r : (∑ v ∈ H, (d.h G v : ℝ)) = (Q.card : ℝ) + (P1.card : ℝ) + (P2.card : ℝ) := by
      exact_mod_cast hsum_h_nat
    have hHL_r : ((H ∪ L).card : ℝ) = (H.card : ℝ) + (d.ell G : ℝ) := by
      have hell_eq : d.ell G = L.card := rfl
      rw [hell_eq]
      exact_mod_cast hHL_card
    have hH_r : (H.card : ℝ) = (Q.card : ℝ) + ((H \ R).card : ℝ) := by exact_mod_cast hH_card
    have hsub_b : ∑ v ∈ H, ((d.h G v : ℝ) - d.b) =
        (∑ v ∈ H, (d.h G v : ℝ)) - (H.card : ℝ) * (2 * d.a + 1) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      rfl
    rw [hHL_r, hH_r] at hd_eHL
    rw [hH_r] at hsub_b
    nlinarith

  -- 3. Inequality (20)
  have hineq20 : ((U).card : ℝ) ≤ ∑ v ∈ O, (d.h G v : ℝ) * d.x v := by
    have hU_cov : ∀ u ∈ U, 1 ≤ ∑ v ∈ closedNbhd G u ∩ O, d.x v := by
      intro u huU
      have huR : u ∈ R := hU_sub_R huU
      have huR0 : u ∈ d.R0 := hR_sub_R0 huR
      have heq : closedNbhd G u ∩ d.C = closedNbhd G u ∩ O := by
        ext v
        change v ∈ closedNbhd G u ∩ d.C ↔ v ∈ closedNbhd G u ∩ (d.C \ (W ∪ H))
        simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨huv, hvC⟩
          refine ⟨huv, hvC, ?_⟩
          rintro (hvW | hvH)
          · exact (Finset.mem_filter.mp huR).2 v hvW ((Aux_7_1.mem_closedNbhd_comm G v u).mp huv)
          · exact (Finset.mem_filter.mp huU).2 v hvH ((Aux_7_1.mem_closedNbhd_comm G v u).mp huv)
        · rintro ⟨huv, hvC, _⟩
          exact ⟨huv, hvC⟩
      rw [← heq]
      exact hx_cov u huR0
    calc (U.card : ℝ) = ∑ _u ∈ U, (1 : ℝ) := by simp
      _ ≤ ∑ u ∈ U, ∑ v ∈ closedNbhd G u ∩ O, d.x v := Finset.sum_le_sum hU_cov
      _ = ∑ u ∈ U, ∑ v ∈ O, (if v ∈ closedNbhd G u then d.x v else 0) := by
          apply Finset.sum_congr rfl
          intro u _
          rw [← Finset.sum_filter]
          apply Finset.sum_congr _ (fun _ _ => rfl)
          ext v
          simp [Finset.mem_filter, Finset.mem_inter, and_comm]
      _ = ∑ v ∈ O, ∑ u ∈ U, (if v ∈ closedNbhd G u then d.x v else 0) := Finset.sum_comm
      _ = ∑ v ∈ O, ((closedNbhd G v ∩ U).card : ℝ) * d.x v := by
          apply Finset.sum_congr rfl
          intro v _
          have hc : ∑ u ∈ U, (if v ∈ closedNbhd G u then d.x v else 0) =
              ∑ u ∈ closedNbhd G v ∩ U, d.x v := by
            rw [← Finset.sum_filter]
            apply Finset.sum_congr _ (fun _ _ => rfl)
            ext u
            simp [Finset.mem_filter, Finset.mem_inter, Aux_7_1.mem_closedNbhd_comm G v u, and_comm]
          rw [hc, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ v ∈ O, (d.h G v : ℝ) * d.x v := by
          apply Finset.sum_le_sum
          intro v hvO
          have hx0 : 0 ≤ d.x v := (hx_bounds v (hO_sub_C hvO)).1
          have hsub : closedNbhd G v ∩ U ⊆ closedNbhd G v ∩ R :=
            Finset.inter_subset_inter_left hU_sub_R
          have hcard : ((closedNbhd G v ∩ U).card : ℝ) ≤ (d.h G v : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
          exact mul_le_mul_of_nonneg_right hcard hx0

  -- 4. Inequality (21)
  have hineq21 : ((d.wCard : ℝ) + (d.ell G : ℝ)) / (d.a + 1) + d.P G ≤
      d.cost - (D.card : ℝ) := by
    have hR_le : (R.card : ℝ) ≤ ∑ v ∈ d.C \ W, (d.h G v : ℝ) * d.x v := by
      have hR_cov : ∀ r ∈ R, 1 ≤ ∑ v ∈ closedNbhd G r ∩ (d.C \ W), d.x v := by
        intro r hrR
        have hrR0 : r ∈ d.R0 := hR_sub_R0 hrR
        have heq : closedNbhd G r ∩ d.C = closedNbhd G r ∩ (d.C \ W) := by
          ext v
          simp only [Finset.mem_inter, Finset.mem_sdiff]
          constructor
          · rintro ⟨hrv, hvC⟩
            refine ⟨hrv, hvC, fun hvW => ?_⟩
            exact (Finset.mem_filter.mp hrR).2 v hvW ((Aux_7_1.mem_closedNbhd_comm G v r).mp hrv)
          · rintro ⟨hrv, hvC, _⟩
            exact ⟨hrv, hvC⟩
        rw [← heq]
        exact hx_cov r hrR0
      calc (R.card : ℝ) = ∑ _r ∈ R, (1 : ℝ) := by simp
        _ ≤ ∑ r ∈ R, ∑ v ∈ closedNbhd G r ∩ (d.C \ W), d.x v := Finset.sum_le_sum hR_cov
        _ = ∑ r ∈ R, ∑ v ∈ d.C \ W, (if v ∈ closedNbhd G r then d.x v else 0) := by
            apply Finset.sum_congr rfl
            intro r _
            rw [← Finset.sum_filter]
            apply Finset.sum_congr _ (fun _ _ => rfl)
            ext v
            simp [Finset.mem_filter, Finset.mem_inter, and_comm]
        _ = ∑ v ∈ d.C \ W, ∑ r ∈ R, (if v ∈ closedNbhd G r then d.x v else 0) := Finset.sum_comm
        _ = ∑ v ∈ d.C \ W, (d.h G v : ℝ) * d.x v := by
            apply Finset.sum_congr rfl
            intro v _
            have hc : ∑ r ∈ R, (if v ∈ closedNbhd G r then d.x v else 0) =
                ∑ r ∈ closedNbhd G v ∩ R, d.x v := by
              rw [← Finset.sum_filter]
              apply Finset.sum_congr _ (fun _ _ => rfl)
              ext r
              simp [Finset.mem_filter, Finset.mem_inter, Aux_7_1.mem_closedNbhd_comm G v r, and_comm]
            rw [hc, Finset.sum_const, nsmul_eq_mul]
            rfl
    have hCW_part : H ∪ O = d.C \ W := by
      ext v
      change v ∈ H ∪ (d.C \ (W ∪ H)) ↔ v ∈ d.C \ W
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (hvH | ⟨hvC, hvWH⟩)
        · exact Finset.mem_sdiff.mp (hH_sub_CW hvH)
        · exact ⟨hvC, fun hvW => hvWH (Or.inl hvW)⟩
      · rintro ⟨hvC, hvW⟩
        by_cases hvH : v ∈ H
        · exact Or.inl hvH
        · exact Or.inr ⟨hvC, fun h => h.elim hvW hvH⟩
    have hdisj_HO : Disjoint H O := by
      rw [Finset.disjoint_left]
      intro v hvH hvO
      exact (Finset.mem_sdiff.mp hvO).2 (Finset.mem_union_right _ hvH)
    have hC_part : W ∪ (d.C \ W) = d.C := Finset.union_sdiff_of_subset hW_sub_C
    have hdisj_WCW : Disjoint W (d.C \ W) := Finset.disjoint_sdiff
    have hcost_split : d.cost = (∑ v ∈ W, d.c v * d.x v) +
        (∑ v ∈ H, d.c v * d.x v) + (∑ v ∈ O, d.c v * d.x v) := by
      change (∑ v ∈ d.C, d.c v * d.x v) = _
      rw [← hC_part, Finset.sum_union hdisj_WCW, ← hCW_part, Finset.sum_union hdisj_HO, add_assoc]
    have hW_sum : d.b * d.t * (d.wCard : ℝ) ≤ ∑ v ∈ W, d.c v * d.x v := by
      have hb_pos : 0 ≤ d.b := by change 0 ≤ 2 * d.a + 1; linarith
      have hw_eq : d.wCard = W.card := rfl
      calc d.b * d.t * (d.wCard : ℝ) = ∑ _v ∈ W, d.b * d.t := by
            rw [Finset.sum_const, nsmul_eq_mul, hw_eq]; ring
        _ ≤ ∑ v ∈ W, d.c v * d.x v := by
            apply Finset.sum_le_sum
            intro v hvW
            rcases (Finset.mem_filter.mp hvW).2 with ⟨hcv, htx⟩
            rw [hcv]
            exact mul_le_mul_of_nonneg_left (le_of_lt htx) hb_pos
    have hH_sum : (∑ v ∈ H, (d.h G v : ℝ) * d.x v) -
        d.t * (∑ v ∈ H, ((d.h G v : ℝ) - d.b)) ≤ ∑ v ∈ H, d.c v * d.x v := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_le_sum
      intro v hvH
      have hcv : d.c v = d.b := hH v hvH
      have hvCW : v ∈ d.C \ W := hH_sub_CW hvH
      have hvC : v ∈ d.C := (Finset.mem_sdiff.mp hvCW).1
      have hvNotW : v ∉ W := (Finset.mem_sdiff.mp hvCW).2
      have hxt : d.x v ≤ d.t := by
        by_contra hgt
        exact hvNotW (Finset.mem_filter.mpr ⟨hvC, hcv, lt_of_not_ge hgt⟩)
      have hhb : 0 ≤ (d.h G v : ℝ) - d.b := by
        have := (Finset.mem_filter.mp hvH).2
        linarith
      have hprod : ((d.h G v : ℝ) - d.b) * d.x v ≤ d.t * ((d.h G v : ℝ) - d.b) := by
        nlinarith
      rw [hcv]
      linarith
    have hO_sum : ∑ v ∈ O, d.c v * d.x v = (∑ v ∈ O, (d.h G v : ℝ) * d.x v) + d.P G := by
      change _ = _ + ∑ v ∈ O, (d.c v - (d.h G v : ℝ)) * d.x v
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro v _
      ring
    have hHO_h : (∑ v ∈ H, (d.h G v : ℝ) * d.x v) + (∑ v ∈ O, (d.h G v : ℝ) * d.x v) =
        ∑ v ∈ d.C \ W, (d.h G v : ℝ) * d.x v := by
      rw [← Finset.sum_union hdisj_HO, hCW_part]
    have ha1_pos : 0 < d.a + 1 := by linarith
    have ht_pos : 0 < d.t := by change 0 < 1 / (d.a + 1); positivity
    have ht_E : d.t * (∑ v ∈ H, ((d.h G v : ℝ) - d.b)) ≤
        d.t * (d.a * (d.ell G : ℝ) - (d.a + 1) * ((H \ R).card : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt ht_pos)
      linarith [hineq19]
    have ht_ident1 : d.t * (d.a + 1) = 1 := by
      change (1 / (d.a + 1)) * (d.a + 1) = 1
      field_simp
    have ht_ident2 : d.b * d.t - 1 = d.a / (d.a + 1) := by
      change (2 * d.a + 1) * (1 / (d.a + 1)) - 1 = d.a / (d.a + 1)
      field_simp
      ring
    have ht_ident3 : 1 - d.t * d.a = 1 / (d.a + 1) := by
      change 1 - (1 / (d.a + 1)) * d.a = 1 / (d.a + 1)
      field_simp
      ring
    have hw_nonneg : (0 : ℝ) ≤ (d.wCard : ℝ) := Nat.cast_nonneg _
    have hcoeff_w : (1 / (d.a + 1)) * (d.wCard : ℝ) ≤ (d.a / (d.a + 1)) * (d.wCard : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ hw_nonneg
      exact div_le_div_of_nonneg_right ha (le_of_lt ha1_pos)
    have hcost_lb : d.b * d.t * (d.wCard : ℝ) + (R.card : ℝ) + d.P G -
        d.t * (d.a * (d.ell G : ℝ) - (d.a + 1) * ((H \ R).card : ℝ)) ≤ d.cost := by
      linarith [hcost_split, hW_sum, hH_sum, hO_sum, hHO_h, hR_le, ht_E]
    have halg : d.b * d.t * (d.wCard : ℝ) + (R.card : ℝ) + d.P G -
        d.t * (d.a * (d.ell G : ℝ) - (d.a + 1) * ((H \ R).card : ℝ)) - (D.card : ℝ) =
        (d.b * d.t - 1) * (d.wCard : ℝ) + (1 - d.t * d.a) * (d.ell G : ℝ) +
          (d.t * (d.a + 1) - 1) * ((H \ R).card : ℝ) + d.P G := by
      rw [hD_real]
      ring
    have halg2 : ((d.wCard : ℝ) + (d.ell G : ℝ)) / (d.a + 1) =
        (1 / (d.a + 1)) * (d.wCard : ℝ) + (1 / (d.a + 1)) * (d.ell G : ℝ) := by ring
    rw [ht_ident1, ht_ident2, ht_ident3] at halg
    linarith [hcost_lb, halg, halg2, hcoeff_w]

  exact ⟨hdom, hineq19, hineq20, hineq21⟩
