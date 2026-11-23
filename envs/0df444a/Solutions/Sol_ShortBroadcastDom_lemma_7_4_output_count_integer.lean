-- Prove2me | solution 1 for ShortBroadcastDom.lemma_7_4_output_count_integer
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T05:00:57.241805+00:00
-- url     : https://prove2.me/submissions/4abb735b-1f6c-4946-a8c6-6a7bde7f24e8

import Definitions.Def_ShortBroadcastDom_InClassC
import Definitions.Def_ShortBroadcastDom_firstSel
import Theorems.Thm_ShortBroadcastDom_lemma_7_1_rounding_calculation
import Theorems.Thm_ShortBroadcastDom_lemma_7_3_first_selection

open ShortBroadcastDom

namespace Aux_7_4

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

lemma connected_singleton {V : Type} (G : SimpleGraph V) (v : V) :
    (G.induce ({v} : Set V)).Connected := by
  have : Nonempty {x : V // x ∈ ({v} : Set V)} := ⟨⟨v, Set.mem_singleton v⟩⟩
  refine ⟨?_⟩
  intro x y
  have hx : x.1 = v := Set.mem_singleton_iff.mp x.2
  have hy : y.1 = v := Set.mem_singleton_iff.mp y.2
  have hxy : x = y := Subtype.ext (hx.trans hy.symm)
  subst hxy
  exact SimpleGraph.Reachable.refl x

lemma subgraphDensity_of_inClassC {V : Type} [Fintype V] (a : ℝ) (G : SimpleGraph V)
    (hG : InClassC a G) : SubgraphDensityLE a G := by
  classical
  intro S
  let J : SimpleGraph {v : V // v ∈ S} := G.induce (S : Set V)
  have hMinor : RobertsonSeymour1986.GM5.IsMinor J G := by
    refine ⟨fun u => ({u.1} : Set V), ?_, ?_, ?_⟩
    · intro u
      exact ⟨Set.singleton_nonempty u.1, connected_singleton G u.1⟩
    · intro u1 u2 hne
      rw [Set.disjoint_singleton]
      exact fun heq => hne (Subtype.ext heq)
    · intro u1 u2 hadj
      exact ⟨u1.1, Set.mem_singleton u1.1, u2.1, Set.mem_singleton u2.1, hadj⟩
  have hJ := hG {v : V // v ∈ S} J hMinor
  have hcard_S : (Fintype.card {v : V // v ∈ S} : ℝ) = (S.card : ℝ) := by
    rw [Fintype.card_coe]
  let eS : Set (Sym2 V) := {e | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S}
  have heS_sub : eS ⊆ Sym2.map Subtype.val '' J.edgeSet := by
    intro e he
    rcases he with ⟨heG, hall⟩
    induction e using Sym2.ind with
    | _ x y =>
      have hadj : G.Adj x y := G.mem_edgeSet.mp heG
      have hxS : x ∈ S := hall x (Sym2.mem_mk_left x y)
      have hyS : y ∈ S := hall y (Sym2.mem_mk_right x y)
      refine ⟨s(⟨x, hxS⟩, ⟨y, hyS⟩), J.mem_edgeSet.mpr hadj, ?_⟩
      simp
  have hncard : eS.ncard ≤ J.edgeSet.ncard := by
    calc eS.ncard ≤ (Sym2.map Subtype.val '' J.edgeSet).ncard :=
          Set.ncard_le_ncard heS_sub (Set.toFinite _)
      _ ≤ J.edgeSet.ncard := Set.ncard_image_le (Set.toFinite _)
  have hncard_r : (eS.ncard : ℝ) ≤ (J.edgeSet.ncard : ℝ) := by exact_mod_cast hncard
  change (eS.ncard : ℝ) ≤ a * (S.card : ℝ)
  rw [← hcard_S]
  exact hncard_r.trans hJ

lemma walk_lift_comp {U V : Type} (G : SimpleGraph V) (P : U → V)
    (G' : SimpleGraph U) (hG' : ∀ x y, G'.Adj x y → G.Adj (P x) (P y))
    (r : U) :
    ∀ {x y : U}, G'.Walk x y → G'.Reachable r x →
      ∀ z : {v : V // ∃ u : U, P u = v ∧ G'.Reachable r u},
        z.1 = P x →
        ∃ z' : {v : V // ∃ u : U, P u = v ∧ G'.Reachable r u},
          z'.1 = P y ∧ (G.induce {v : V | ∃ u : U, P u = v ∧ G'.Reachable r u}).Reachable z z' := by
  intro x y p
  induction p with
  | nil =>
    intro _ z hz
    exact ⟨z, hz, SimpleGraph.Reachable.refl z⟩
  | @cons a b c hadj rest ih =>
    intro hra z hz
    have hrb : G'.Reachable r b := hra.trans hadj.reachable
    let zb : {v : V // ∃ u : U, P u = v ∧ G'.Reachable r u} := ⟨P b, ⟨b, rfl, hrb⟩⟩
    have hadj_ind : (G.induce {v : V | ∃ u : U, P u = v ∧ G'.Reachable r u}).Adj z zb := by
      change G.Adj z.1 zb.1
      rw [hz]
      exact hG' a b hadj
    rcases ih hrb zb rfl with ⟨zc, hzc, hreach_bc⟩
    exact ⟨zc, hzc, hadj_ind.reachable.trans hreach_bc⟩

abbrev BranchVK {V : Type} (A_rep : Finset V) (inMarked : V → Prop) : Type :=
  {r : V // r ∈ A_rep} ⊕ {v : V // ¬ inMarked v}

def branchBeta {V : Type} (A_rep : Finset V) (inMarked : V → Prop) (compOf : V → Set V) :
    BranchVK A_rep inMarked → Set V
  | Sum.inl r => compOf r.1
  | Sum.inr v => {v.1}

def branchGraph {V : Type} (G : SimpleGraph V) (A_rep : Finset V) (inMarked : V → Prop)
    (compOf : V → Set V) : SimpleGraph (BranchVK A_rep inMarked) where
  Adj z1 z2 := z1 ≠ z2 ∧ ∃ x1 ∈ branchBeta A_rep inMarked compOf z1,
    ∃ x2 ∈ branchBeta A_rep inMarked compOf z2, G.Adj x1 x2
  symm := ⟨fun _ _ ⟨hne, x1, hx1, x2, hx2, hadj⟩ =>
    ⟨hne.symm, x2, hx2, x1, hx1, hadj.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

noncomputable instance instDecAdjBranchGraph {V : Type} (G : SimpleGraph V)
    (A_rep : Finset V) (inMarked : V → Prop) (compOf : V → Set V) :
    DecidableRel (branchGraph G A_rep inMarked compOf).Adj :=
  Classical.decRel _

end Aux_7_4

theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 2 ≤ d) (hG : InClassC ((d : ℝ) / 2) G) (x : V → ℝ)
    (hx : IsFeasibleOn G (Finset.univ \ firstSel G d) (remDemands G d) x) :
    (((selRounding G d x).D G).card : ℝ) ≤
      ((d : ℝ) + 1) ^ 2 * (((selRounding G d x).wCard : ℝ) + ((selRounding G d x).ell G : ℝ)) +
        (d : ℝ) * ((d : ℝ) + 1) ^ 2 * (selRounding G d x).P G := by
  classical
  set rd : RoundingData V := selRounding G d x
  set F : Finset V := firstSel G d
  set B : Finset V := defects G d
  set R0 : Finset V := remDemands G d
  set W : Finset V := rd.W
  set R : Finset V := rd.R G
  set H : Finset V := rd.H G
  set U : Finset V := rd.U G
  set D : Finset V := rd.D G
  set O : Finset V := rd.O G
  set L : Finset V := rd.L G
  set Q : Finset V := H ∩ R

  have hd_real : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have ha_eq : rd.a = (d : ℝ) / 2 := rfl
  have hb_eq : rd.b = (d : ℝ) + 1 := by
    change 2 * ((d : ℝ) / 2) + 1 = (d : ℝ) + 1
    ring
  have ha_ge1 : 1 ≤ rd.a := by rw [ha_eq]; linarith
  have hdens : SubgraphDensityLE rd.a G := Aux_7_4.subgraphDensity_of_inClassC rd.a G hG
  have h73 := lemma_7_3_first_selection G d hd
  have hB_sub_R0 : B ⊆ R0 := h73.1
  have h73_cost := h73.2.1

  have hR_sub_R0 : R ⊆ R0 := Finset.filter_subset _ _
  have hU_sub_R : U ⊆ R := Finset.filter_subset _ _
  have hW_sub_C : W ⊆ rd.C := Finset.filter_subset _ _
  have hH_sub_CW : H ⊆ rd.C \ W := Finset.filter_subset _ _
  have hH_sub_C : H ⊆ rd.C := hH_sub_CW.trans Finset.sdiff_subset
  have hO_sub_C : O ⊆ rd.C := Finset.sdiff_subset
  have hR0_sub_C : R0 ⊆ rd.C := by
    intro r hrR0
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ r, fun hrF => ?_⟩
    exact (Finset.mem_filter.mp hrR0).2 r hrF (Aux_7_4.self_mem_closedNbhd G r)

  have hset : IsRoundingSetting G rd := by
    refine ⟨ha_ge1, hR0_sub_C, ?_, hx⟩
    intro v hvC
    have hvF : v ∉ F := (Finset.mem_sdiff.mp hvC).2
    have hcv_def : rd.c v = selCost G d v := rfl
    rcases h73_cost v hvF with ⟨_, hc1, hcb, _, _⟩
    rw [hb_eq, hcv_def]
    exact ⟨by linarith, hcb⟩

  have hh_le_R0 : ∀ v : V, (rd.h G v : ℝ) ≤ ((closedNbhd G v ∩ R0).card : ℝ) := by
    intro v
    have hsub : closedNbhd G v ∩ R ⊆ closedNbhd G v ∩ R0 :=
      Finset.inter_subset_inter_left hR_sub_R0
    exact_mod_cast Finset.card_le_card hsub

  have hH_cost : ∀ v ∈ H, rd.c v = rd.b := by
    intro v hvH
    have hvC : v ∈ rd.C := hH_sub_C hvH
    have hvF : v ∉ F := (Finset.mem_sdiff.mp hvC).2
    have hcv_def : rd.c v = selCost G d v := rfl
    rcases h73_cost v hvF with ⟨_, _, hcb, _, hlt_imp⟩
    have hbh : rd.b ≤ (rd.h G v : ℝ) := (Finset.mem_filter.mp hvH).2
    rw [hb_eq] at hbh ⊢
    rw [hcv_def]
    rcases lt_or_eq_of_le hcb with hlt | heq
    · have h1 := hlt_imp hlt
      have h2 := hh_le_R0 v
      linarith
    · exact heq

  have hO_props : ∀ v ∈ O, rd.h G v ≤ d ∧ 1 ≤ rd.c v - (rd.h G v : ℝ) := by
    intro v hvO
    have hvC : v ∈ rd.C := hO_sub_C hvO
    have hvF : v ∉ F := (Finset.mem_sdiff.mp hvC).2
    have hcv_def : rd.c v = selCost G d v := rfl
    rcases Finset.mem_sdiff.mp hvO with ⟨_, hvWH⟩
    have hvNotW : v ∉ W := fun h => hvWH (Finset.mem_union_left _ h)
    have hvNotH : v ∉ H := fun h => hvWH (Finset.mem_union_right _ h)
    have hvCW : v ∈ rd.C \ W := Finset.mem_sdiff.mpr ⟨hvC, hvNotW⟩
    have hh_lt_b : (rd.h G v : ℝ) < rd.b := by
      by_contra hge
      exact hvNotH (Finset.mem_filter.mpr ⟨hvCW, le_of_not_gt hge⟩)
    have hh_lt_d1 : (rd.h G v : ℝ) < (d : ℝ) + 1 := by rwa [hb_eq] at hh_lt_b
    have hh_nat_lt : rd.h G v < d + 1 := by exact_mod_cast hh_lt_d1
    have hh_le_d : rd.h G v ≤ d := Nat.lt_succ_iff.mp hh_nat_lt
    rcases h73_cost v hvF with ⟨_, _, hcb, _, hlt_imp⟩
    rw [hcv_def]
    rcases lt_or_eq_of_le hcb with hlt | heq
    · have h1 := hlt_imp hlt
      have h2 := hh_le_R0 v
      exact ⟨hh_le_d, by linarith⟩
    · have hh_r : (rd.h G v : ℝ) ≤ (d : ℝ) := by exact_mod_cast hh_le_d
      exact ⟨hh_le_d, by linarith [heq, hh_r]⟩

  have hO_cost : ∀ v ∈ O, (rd.h G v : ℝ) ≤ rd.c v := by
    intro v hvO
    linarith [(hO_props v hvO).2]

  have h71 := lemma_7_1_rounding_calculation G rd hset hdens hH_cost hO_cost
  have hineq19 := h71.2.1
  have hineq20 := h71.2.2.1

  -- |H \ R| ≤ ℓ
  have hHR_le_ell : ((H \ R).card : ℝ) ≤ (rd.ell G : ℝ) := by
    have hsum_nonneg : (0 : ℝ) ≤ ∑ v ∈ H, ((rd.h G v : ℝ) - rd.b) := by
      apply Finset.sum_nonneg
      intro v hvH
      have := (Finset.mem_filter.mp hvH).2
      linarith
    have h1 : (rd.a + 1) * ((H \ R).card : ℝ) ≤ rd.a * (rd.ell G : ℝ) := by
      linarith [hineq19, hsum_nonneg]
    have hell_nonneg : (0 : ℝ) ≤ (rd.ell G : ℝ) := Nat.cast_nonneg _
    have ha_lt : rd.a * (rd.ell G : ℝ) ≤ (rd.a + 1) * (rd.ell G : ℝ) := by nlinarith
    have ha1_pos : 0 < rd.a + 1 := by linarith
    exact le_of_mul_le_mul_left (h1.trans ha_lt) ha1_pos

  -- |U| ≤ d * P
  have hU_le_dP : (U.card : ℝ) ≤ (d : ℝ) * rd.P G := by
    calc (U.card : ℝ) ≤ ∑ v ∈ O, (rd.h G v : ℝ) * x v := hineq20
      _ ≤ ∑ v ∈ O, (d : ℝ) * ((rd.c v - (rd.h G v : ℝ)) * x v) := by
          apply Finset.sum_le_sum
          intro v hvO
          rcases hO_props v hvO with ⟨hhd, hch1⟩
          have hh_r : (rd.h G v : ℝ) ≤ (d : ℝ) := by exact_mod_cast hhd
          have hx0 : 0 ≤ x v := (hx.1 v (hO_sub_C hvO)).1
          have hstep1 : (rd.h G v : ℝ) * x v ≤ (d : ℝ) * x v :=
            mul_le_mul_of_nonneg_right hh_r hx0
          have hstep2 : (d : ℝ) * x v ≤ (d : ℝ) * ((rd.c v - (rd.h G v : ℝ)) * x v) := by
            have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
            have h1x : x v ≤ (rd.c v - (rd.h G v : ℝ)) * x v := by nlinarith
            exact mul_le_mul_of_nonneg_left h1x hd0
          exact hstep1.trans hstep2
      _ = (d : ℝ) * rd.P G := (Finset.mul_sum _ _ _).symm

  -- Disjointness & partition facts for R and H
  have hdisj_WR : Disjoint W R := by
    rw [Finset.disjoint_left]
    intro v hvW hvR
    exact (Finset.mem_filter.mp hvR).2 v hvW (Aux_7_4.self_mem_closedNbhd G v)
  have hdisj_HU : Disjoint H U := by
    rw [Finset.disjoint_left]
    intro v hvH hvU
    exact (Finset.mem_filter.mp hvU).2 v hvH (Aux_7_4.self_mem_closedNbhd G v)
  have hdisj_QU : Disjoint Q U := hdisj_HU.mono_left Finset.inter_subset_left
  have hdisj_HL : Disjoint H L := by
    rw [Finset.disjoint_left]
    intro v hvH hvL
    exact (Finset.mem_sdiff.mp hvL).2 (Finset.mem_union_left _ hvH)
  have hdisj_QL : Disjoint Q L := hdisj_HL.mono_left Finset.inter_subset_left
  have hdisj_UL : Disjoint U L := by
    rw [Finset.disjoint_left]
    intro v hvU hvL
    exact (Finset.mem_sdiff.mp hvL).2 (Finset.mem_union_right _ hvU)
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

  -- Construct the minor K by contracting components of G - R meeting W
  let G' : SimpleGraph {v : V // v ∉ R} := G.induce {v : V | v ∉ R}
  let ord : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  have hW_notR : ∀ w ∈ W, w ∉ R := fun w hwW hwR => Finset.disjoint_left.mp hdisj_WR hwW hwR
  let reachOutR : V → V → Prop := fun u v =>
    ∃ (hu : u ∉ R) (hv : v ∉ R), G'.Reachable ⟨u, hu⟩ ⟨v, hv⟩
  let A_rep : Finset V := W.filter fun w =>
    ∀ w' ∈ W, reachOutR w w' → (ord w).val ≤ (ord w').val
  have hA_le_w : A_rep.card ≤ rd.wCard := Finset.card_le_card (Finset.filter_subset _ _)

  have hreach_refl : ∀ u, u ∉ R → reachOutR u u :=
    fun u hu => ⟨hu, hu, SimpleGraph.Reachable.refl (⟨u, hu⟩ : {v : V // v ∉ R})⟩
  have hreach_symm : ∀ {u v}, reachOutR u v → reachOutR v u := by
    rintro u v ⟨hu, hv, hr⟩
    exact ⟨hv, hu, hr.symm⟩
  have hreach_trans : ∀ {u v z}, reachOutR u v → reachOutR v z → reachOutR u z := by
    rintro u v z ⟨hu, _, h1⟩ ⟨_, hz, h2⟩
    exact ⟨hu, hz, h1.trans h2⟩

  have hW_has_rep : ∀ w ∈ W, ∃ r ∈ A_rep, reachOutR r w := by
    intro w hwW
    let cand : Finset V := W.filter fun w' => reachOutR w w'
    have hcand_ne : cand.Nonempty := ⟨w, Finset.mem_filter.mpr ⟨hwW, hreach_refl w (hW_notR w hwW)⟩⟩
    let imgs : Finset (Fin (Fintype.card V)) := cand.image ord
    have himgs_ne : imgs.Nonempty := hcand_ne.image ord
    let m : Fin (Fintype.card V) := imgs.min' himgs_ne
    rcases Finset.mem_image.mp (Finset.min'_mem imgs himgs_ne) with ⟨r, hrcand, hr_eq⟩
    rcases Finset.mem_filter.mp hrcand with ⟨hrW, hwr⟩
    refine ⟨r, Finset.mem_filter.mpr ⟨hrW, ?_⟩, hreach_symm hwr⟩
    intro w' hw'W hrw'
    have hw'cand : w' ∈ cand := Finset.mem_filter.mpr ⟨hw'W, hreach_trans hwr hrw'⟩
    have hm_le : imgs.min' himgs_ne ≤ ord w' :=
      Finset.min'_le imgs (ord w') (Finset.mem_image_of_mem ord hw'cand)
    rw [← hr_eq] at hm_le
    exact hm_le

  let compOf : V → Set V := fun r => {v : V | reachOutR r v}
  have hcomp_disj : ∀ {r1 r2}, r1 ∈ A_rep → r2 ∈ A_rep → r1 ≠ r2 →
      Disjoint (compOf r1) (compOf r2) := by
    intro r1 r2 hr1 hr2 hne
    rw [Set.disjoint_left]
    intro v hv1 hv2
    have hr12 : reachOutR r1 r2 := hreach_trans hv1 (hreach_symm hv2)
    rcases Finset.mem_filter.mp hr1 with ⟨hr1W, hmin1⟩
    rcases Finset.mem_filter.mp hr2 with ⟨hr2W, hmin2⟩
    have hle1 : (ord r1).val ≤ (ord r2).val := hmin1 r2 hr2W hr12
    have hle2 : (ord r2).val ≤ (ord r1).val := hmin2 r1 hr1W (hreach_symm hr12)
    exact hne (ord.injective (Fin.ext (Nat.le_antisymm hle1 hle2)))

  let inMarked : V → Prop := fun v => ∃ r ∈ A_rep, v ∈ compOf r
  have hinMarked_iff_W : ∀ v, inMarked v ↔ ∃ w ∈ W, reachOutR w v := by
    intro v
    constructor
    · rintro ⟨r, hrA, hrv⟩
      exact ⟨r, (Finset.mem_filter.mp hrA).1, hrv⟩
    · rintro ⟨w, hwW, hwv⟩
      rcases hW_has_rep w hwW with ⟨r, hrA, hrw⟩
      exact ⟨r, hrA, hreach_trans hrw hwv⟩
  have hnot_inMarked_of_R : ∀ v ∈ R, ¬ inMarked v := by
    intro v hvR ⟨_, _, _, hvNotR, _⟩
    exact hvNotR hvR

  let VK : Type := Aux_7_4.BranchVK A_rep inMarked
  let β : VK → Set V := Aux_7_4.branchBeta A_rep inMarked compOf
  let K : SimpleGraph VK := Aux_7_4.branchGraph G A_rep inMarked compOf
  have inr_val_eq : ∀ {u1 u2 : {v : V // ¬ inMarked v}},
      (Sum.inr u1 : VK) = Sum.inr u2 → u1.1 = u2.1 :=
    fun h => congrArg Subtype.val (Sum.inr.inj h)

  -- K is a minor of G
  have hK_minor : RobertsonSeymour1986.GM5.IsMinor K G := by
    refine ⟨β, ?_, ?_, ?_⟩
    · intro z
      cases z with
      | inr v =>
        dsimp [β, Aux_7_4.branchBeta]
        exact ⟨Set.singleton_nonempty v.1, Aux_7_4.connected_singleton G v.1⟩
      | inl r =>
        dsimp [β, Aux_7_4.branchBeta]
        have hrW : r.1 ∈ W := (Finset.mem_filter.mp r.2).1
        have hrNotR : r.1 ∉ R := hW_notR r.1 hrW
        have hr_mem : r.1 ∈ compOf r.1 := hreach_refl r.1 hrNotR
        refine ⟨⟨r.1, hr_mem⟩, ?_⟩
        -- Connectedness of G.induce (compOf r.1)
        let r0 : {v : V // v ∉ R} := ⟨r.1, hrNotR⟩
        have hcomp_eq : compOf r.1 = {v : V | ∃ u : {v : V // v ∉ R}, u.1 = v ∧ G'.Reachable r0 u} := by
          ext v
          constructor
          · rintro ⟨_, hvNotR, hreach⟩
            exact ⟨⟨v, hvNotR⟩, rfl, hreach⟩
          · rintro ⟨⟨u, huNotR⟩, rfl, hreach⟩
            exact ⟨hrNotR, huNotR, hreach⟩
        change (G.induce (compOf r.1)).Connected
        rw [hcomp_eq]
        have : Nonempty {v : V // v ∈ {v : V | ∃ u : {v : V // v ∉ R}, u.1 = v ∧ G'.Reachable r0 u}} :=
          ⟨⟨r.1, ⟨r0, rfl, SimpleGraph.Reachable.refl r0⟩⟩⟩
        refine ⟨?_⟩
        intro x y
        rcases x.2 with ⟨ux, hux_eq, hrx⟩
        rcases y.2 with ⟨uy, huy_eq, hry⟩
        have hxy : G'.Reachable ux uy := hrx.symm.trans hry
        rcases hxy with ⟨p⟩
        rcases Aux_7_4.walk_lift_comp G Subtype.val G' (fun _ _ h => h) r0 p hrx x hux_eq.symm
          with ⟨z', hz'_eq, hreach_xz'⟩
        have hz'_y : z' = y := Subtype.ext (hz'_eq.trans huy_eq)
        rwa [hz'_y] at hreach_xz'
    · intro z1 z2 hne
      cases z1 with
      | inl r1 =>
        cases z2 with
        | inl r2 =>
          dsimp [β, Aux_7_4.branchBeta]
          have hr_ne : r1.1 ≠ r2.1 := fun h => hne (congrArg Sum.inl (Subtype.ext h))
          exact hcomp_disj r1.2 r2.2 hr_ne
        | inr v2 =>
          dsimp [β, Aux_7_4.branchBeta]
          rw [Set.disjoint_singleton_right]
          exact fun hv => v2.2 ⟨r1.1, r1.2, hv⟩
      | inr v1 =>
        cases z2 with
        | inl r2 =>
          dsimp [β, Aux_7_4.branchBeta]
          rw [Set.disjoint_singleton_left]
          exact fun hv => v1.2 ⟨r2.1, r2.2, hv⟩
        | inr v2 =>
          dsimp [β, Aux_7_4.branchBeta]
          rw [Set.disjoint_singleton]
          exact fun h => hne (congrArg Sum.inr (Subtype.ext h))
    · intro z1 z2 hadj
      exact hadj.2

  -- Minor density gives 2|E(K)| ≤ d|VK|
  have hK_dens : 2 * K.edgeFinset.card ≤ d * Fintype.card VK := by
    have h1 := hG VK K hK_minor
    have hcard_eq : K.edgeSet.ncard = K.edgeFinset.card := by
      rw [← SimpleGraph.coe_edgeFinset K, Set.ncard_coe_finset]
    rw [hcard_eq] at h1
    have h2 : (2 : ℝ) * (K.edgeFinset.card : ℝ) ≤ (d : ℝ) * (Fintype.card VK : ℝ) := by linarith
    exact_mod_cast h2
  have hK_sum_deg : ∑ z : VK, K.degree z ≤ d * Fintype.card VK := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges]
    exact hK_dens

  -- Define BQ and S_K ⊆ VK
  let BQ : Finset V := B ∩ Q
  let inVK_R : ∀ v ∈ R, VK := fun v hvR => Sum.inr ⟨v, hnot_inMarked_of_R v hvR⟩
  let S_K : Finset VK := Finset.univ.filter fun z =>
    match z with
    | Sum.inl _ => true
    | Sum.inr v => v.1 ∈ L ∪ U ∪ BQ

  -- Card of S_K
  have hSK_card : S_K.card = A_rep.card + L.card + U.card + BQ.card := by
    let S_left : Finset VK := (Finset.univ : Finset {r : V // r ∈ A_rep}).map
      ⟨Sum.inl, Sum.inl_injective⟩
    let LUBQ : Finset V := L ∪ U ∪ BQ
    have hLUBQ_sub_R : LUBQ ⊆ R := by
      intro v hv
      rcases Finset.mem_union.mp hv with hvLU | hvBQ
      · rcases Finset.mem_union.mp hvLU with hvL | hvU
        · exact (Finset.mem_sdiff.mp hvL).1
        · exact hU_sub_R hvU
      · exact (Finset.mem_inter.mp (Finset.mem_inter.mp hvBQ).2).2
    let embR : {v : V // v ∈ LUBQ} ↪ VK :=
      ⟨fun v => Sum.inr ⟨v.1, hnot_inMarked_of_R v.1 (hLUBQ_sub_R v.2)⟩,
       fun a b h => Subtype.ext (inr_val_eq h)⟩
    let S_right : Finset VK := LUBQ.attach.map embR
    have hSK_eq : S_K = S_left ∪ S_right := by
      ext z
      rw [Finset.mem_union]
      cases z with
      | inl r =>
        constructor
        · intro _
          exact Or.inl (Finset.mem_map.mpr ⟨r, Finset.mem_univ r, rfl⟩)
        · intro _
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
      | inr v =>
        constructor
        · intro hz
          have hv : v.1 ∈ LUBQ := (Finset.mem_filter.mp hz).2
          refine Or.inr (Finset.mem_map.mpr ⟨⟨v.1, hv⟩, Finset.mem_attach _ _, ?_⟩)
          exact congrArg Sum.inr (Subtype.ext rfl)
        · rintro (hL | hR)
          · rcases Finset.mem_map.mp hL with ⟨r, _, hcontr⟩
            exact False.elim (nomatch hcontr)
          · rcases Finset.mem_map.mp hR with ⟨⟨u, hu⟩, _, heq⟩
            have huv : v.1 = u := (inr_val_eq heq).symm
            have hvmem : v.1 ∈ L ∪ U ∪ BQ := by rwa [huv]
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvmem⟩
    have hdisj_LR : Disjoint S_left S_right := by
      rw [Finset.disjoint_left]
      intro z hzL hzR
      rcases Finset.mem_map.mp hzL with ⟨r, _, rfl⟩
      rcases Finset.mem_map.mp hzR with ⟨v, _, hv⟩
      exact (nomatch hv)
    have hdisj_L_BQ : Disjoint L BQ :=
      hdisj_QL.symm.mono_right Finset.inter_subset_right
    have hdisj_U_BQ : Disjoint U BQ :=
      hdisj_QU.symm.mono_right Finset.inter_subset_right
    have hLUBQ_card : LUBQ.card = L.card + U.card + BQ.card := by
      change (L ∪ U ∪ BQ).card = _
      rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hdisj_L_BQ, hdisj_U_BQ⟩),
        Finset.card_union_of_disjoint hdisj_UL.symm]
    rw [hSK_eq, Finset.card_union_of_disjoint hdisj_LR]
    have hc1 : S_left.card = A_rep.card := by simp [S_left]
    have hc2 : S_right.card = LUBQ.card := by simp [S_right]
    omega

  -- Helper: neighbors in G that are ¬inMarked give distinct neighbors in K
  have hdeg_from_unmarked : ∀ (v : V) (hv : ¬ inMarked v) (T : Finset V),
      T ⊆ G.neighborFinset v → (∀ u ∈ T, ¬ inMarked u) →
      T.card ≤ K.degree (Sum.inr ⟨v, hv⟩) := by
    intro v hv T hT_sub hT_unm
    let fT : {u : V // u ∈ T} ↪ VK :=
      ⟨fun u => Sum.inr ⟨u.1, hT_unm u.1 u.2⟩,
       fun a b h => Subtype.ext (inr_val_eq h)⟩
    have himg : T.attach.map fT ⊆ K.neighborFinset (Sum.inr ⟨v, hv⟩) := by
      intro z hz
      rcases Finset.mem_map.mp hz with ⟨u, _, rfl⟩
      rw [SimpleGraph.mem_neighborFinset]
      have hadj : G.Adj v u.1 := (G.mem_neighborFinset v u.1).mp (hT_sub u.2)
      have hne : (Sum.inr ⟨v, hv⟩ : VK) ≠ fT u := by
        intro heq
        exact G.ne_of_adj hadj (inr_val_eq heq)
      exact ⟨hne, v, Set.mem_singleton v, u.1, Set.mem_singleton u.1, hadj⟩
    have hle := Finset.card_le_card himg
    simpa using hle

  -- Every q ∈ Q has (G.neighborFinset q ∩ R).card ≥ d
  have hQ_Rnbrs : ∀ q ∈ Q, d ≤ (G.neighborFinset q ∩ R).card := by
    intro q hqQ
    rcases Finset.mem_inter.mp hqQ with ⟨hqH, hqR⟩
    have hbh : rd.b ≤ (rd.h G q : ℝ) := (Finset.mem_filter.mp hqH).2
    rw [hb_eq] at hbh
    have hdh : d + 1 ≤ rd.h G q := by exact_mod_cast hbh
    have hcl_eq : rd.h G q = 1 + (G.neighborFinset q ∩ R).card := by
      change (closedNbhd G q ∩ R).card = _
      have hset_eq : closedNbhd G q ∩ R = insert q (G.neighborFinset q ∩ R) := by
        ext u
        simp only [closedNbhd, Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hu, huR⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hu, huR⟩
        · rintro (rfl | ⟨hu, huR⟩)
          · exact ⟨Or.inl rfl, hqR⟩
          · exact ⟨Or.inr hu, huR⟩
      have hnot : q ∉ G.neighborFinset q ∩ R :=
        fun h => G.notMem_neighborFinset_self q (Finset.mem_inter.mp h).1
      rw [hset_eq, Finset.card_insert_of_notMem hnot, Nat.add_comm]
    omega

  -- Every z ∉ S_K has K.degree z ≥ d
  have hdeg_outside_SK : ∀ z : VK, z ∉ S_K → d ≤ K.degree z := by
    intro z hzNotSK
    cases z with
    | inl r =>
      exact False.elim (hzNotSK (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩))
    | inr v =>
      have hvNotLUBQ : v.1 ∉ L ∪ U ∪ BQ := by
        intro hmem
        exact hzNotSK (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hmem⟩)
      by_cases hvR : v.1 ∈ R
      · -- v.1 ∈ R \ (L ∪ U ∪ BQ) → v.1 ∈ Q
        have hvQ : v.1 ∈ Q := by
          have hvR' := hvR
          rw [← hR_part] at hvR'
          rcases Finset.mem_union.mp hvR' with hvQU | hvL
          · rcases Finset.mem_union.mp hvQU with hvQ | hvU
            · exact hvQ
            · exact False.elim (hvNotLUBQ (Finset.mem_union_left _ (Finset.mem_union_right _ hvU)))
          · exact False.elim (hvNotLUBQ (Finset.mem_union_left _ (Finset.mem_union_left _ hvL)))
        calc d ≤ (G.neighborFinset v.1 ∩ R).card := hQ_Rnbrs v.1 hvQ
          _ ≤ K.degree (Sum.inr v) :=
              hdeg_from_unmarked v.1 v.2 (G.neighborFinset v.1 ∩ R) Finset.inter_subset_left
                (fun u hu => hnot_inMarked_of_R u (Finset.mem_inter.mp hu).2)
      · -- v.1 ∉ R and ¬inMarked v.1
        have hvNotB : v.1 ∉ B := by
          intro hvB
          have hvR0 : v.1 ∈ R0 := hB_sub_R0 hvB
          have hexW : ∃ w ∈ W, v.1 ∈ closedNbhd G w := by
            by_contra hnone
            exact hvR (Finset.mem_filter.mpr ⟨hvR0, fun w hw hvw => hnone ⟨w, hw, hvw⟩⟩)
          rcases hexW with ⟨w, hwW, hvw⟩
          have hwNotR : w ∉ R := hW_notR w hwW
          have hrwv : reachOutR w v.1 := by
            simp only [closedNbhd, Finset.mem_insert, SimpleGraph.mem_neighborFinset] at hvw
            rcases hvw with heq | hadj
            · exact heq ▸ hreach_refl w hwNotR
            · exact ⟨hwNotR, hvR, SimpleGraph.Adj.reachable hadj⟩
          exact v.2 ((hinMarked_iff_W v.1).mpr ⟨w, hwW, hrwv⟩)
        have hdeg_d : G.degree v.1 = d := by
          by_contra hne
          exact hvNotB (Finset.mem_filter.mpr ⟨Finset.mem_univ v.1, hne⟩)
        have hn_unmarked : ∀ u ∈ G.neighborFinset v.1, ¬ inMarked u := by
          intro u hu hm
          have hadj : G.Adj v.1 u := (G.mem_neighborFinset v.1 u).mp hu
          rcases (hinMarked_iff_W u).mp hm with ⟨w, hwW, hwNotR, huNotR, hwu⟩
          have huv : G'.Reachable ⟨u, huNotR⟩ ⟨v.1, hvR⟩ :=
            SimpleGraph.Adj.reachable hadj.symm
          exact v.2 ((hinMarked_iff_W v.1).mpr ⟨w, hwW, hwNotR, hvR, hwu.trans huv⟩)
        calc d = (G.neighborFinset v.1).card := hdeg_d.symm
          _ ≤ K.degree (Sum.inr v) :=
              hdeg_from_unmarked v.1 v.2 (G.neighborFinset v.1) Finset.Subset.rfl hn_unmarked

  -- Bound ∑_{z ∈ S_K} K.degree z ≤ d * S_K.card
  have hsum_SK_deg : ∑ z ∈ S_K, K.degree z ≤ d * S_K.card := by
    have hsplit : (∑ z ∈ S_K, K.degree z) + (∑ z ∈ Finset.univ \ S_K, K.degree z) =
        ∑ z : VK, K.degree z :=
      Finset.sum_add_sum_compl S_K _
    have hout_lb : d * (Finset.univ \ S_K).card ≤ ∑ z ∈ Finset.univ \ S_K, K.degree z := by
      calc d * (Finset.univ \ S_K).card = ∑ _z ∈ Finset.univ \ S_K, d := by
            rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
        _ ≤ ∑ z ∈ Finset.univ \ S_K, K.degree z :=
            Finset.sum_le_sum (fun z hz => hdeg_outside_SK z (Finset.mem_sdiff.mp hz).2)
    have hcard_compl : S_K.card + (Finset.univ \ S_K).card = Fintype.card VK :=
      Finset.card_add_card_compl S_K
    have hmul_compl : d * S_K.card + d * (Finset.univ \ S_K).card = d * Fintype.card VK := by
      rw [← Nat.mul_add, hcard_compl]
    omega

  -- Every q ∈ BQ has K.degree (Sum.inr ⟨q, _⟩) ≥ d + 1
  have hBQ_deg : ∀ (q : V) (hqBQ : q ∈ BQ), d + 1 ≤
      K.degree (Sum.inr ⟨q, hnot_inMarked_of_R q (Finset.mem_inter.mp (Finset.mem_inter.mp hqBQ).2).2⟩) := by
    intro q hqBQ
    rcases Finset.mem_inter.mp hqBQ with ⟨hqB, hqQ⟩
    have hqR : q ∈ R := (Finset.mem_inter.mp hqQ).2
    have hqUnm : ¬ inMarked q := hnot_inMarked_of_R q hqR
    let zq : VK := Sum.inr ⟨q, hqUnm⟩
    have hRnbr_ge_d : d ≤ (G.neighborFinset q ∩ R).card := hQ_Rnbrs q hqQ
    have hdeg_ne_d : G.degree q ≠ d := (Finset.mem_filter.mp hqB).2
    have hdeg_ge_d : d ≤ G.degree q :=
      hRnbr_ge_d.trans (Finset.card_le_card Finset.inter_subset_left)
    have hdeg_ge_d1 : d + 1 ≤ G.degree q := by omega
    by_cases hR_ge_d1 : d + 1 ≤ (G.neighborFinset q ∩ R).card
    · calc d + 1 ≤ (G.neighborFinset q ∩ R).card := hR_ge_d1
        _ ≤ K.degree zq :=
            hdeg_from_unmarked q hqUnm (G.neighborFinset q ∩ R) Finset.inter_subset_left
              (fun u hu => hnot_inMarked_of_R u (Finset.mem_inter.mp hu).2)
    · have hex_outR : (G.neighborFinset q \ R).Nonempty := by
        apply Finset.card_pos.mp
        have hsdiff := Finset.card_inter_add_card_sdiff (G.neighborFinset q) R
        have hnbr_eq : (G.neighborFinset q).card = G.degree q := rfl
        omega
      rcases hex_outR with ⟨u0, hu0_sdiff⟩
      rcases Finset.mem_sdiff.mp hu0_sdiff with ⟨hu0_nbr, hu0NotR⟩
      have hadj_qu0 : G.Adj q u0 := (G.mem_neighborFinset q u0).mp hu0_nbr
      -- Construct the extra neighbor z_extra of zq in K
      have hex_extra : ∃ z_ex ∈ K.neighborFinset zq,
          ∀ (w : V) (hw : w ∈ G.neighborFinset q ∩ R),
            z_ex ≠ Sum.inr ⟨w, hnot_inMarked_of_R w (Finset.mem_inter.mp hw).2⟩ := by
        by_cases hm : inMarked u0
        · rcases hm with ⟨r, hrA, hu0_comp⟩
          refine ⟨Sum.inl ⟨r, hrA⟩, ?_, fun _ _ h => nomatch h⟩
          rw [SimpleGraph.mem_neighborFinset]
          exact ⟨(fun h => nomatch h), q, Set.mem_singleton q, u0, hu0_comp, hadj_qu0⟩
        · refine ⟨Sum.inr ⟨u0, hm⟩, ?_, ?_⟩
          · rw [SimpleGraph.mem_neighborFinset]
            have hne : zq ≠ Sum.inr ⟨u0, hm⟩ := by
              intro h
              have hqu0 : q = u0 := inr_val_eq h
              exact hu0NotR (hqu0 ▸ hqR)
            exact ⟨hne, q, Set.mem_singleton q, u0, Set.mem_singleton u0, hadj_qu0⟩
          · intro w hw heq
            have hwR : w ∈ R := (Finset.mem_inter.mp hw).2
            have hu0w : u0 = w := inr_val_eq heq
            exact hu0NotR (hu0w ▸ hwR)
      rcases hex_extra with ⟨z_ex, hz_ex_mem, hz_ex_fresh⟩
      let fR : {w : V // w ∈ G.neighborFinset q ∩ R} ↪ VK :=
        ⟨fun w => Sum.inr ⟨w.1, hnot_inMarked_of_R w.1 (Finset.mem_inter.mp w.2).2⟩,
         fun a b h => Subtype.ext (inr_val_eq h)⟩
      let TR : Finset VK := (G.neighborFinset q ∩ R).attach.map fR
      have hTR_sub : TR ⊆ K.neighborFinset zq := by
        intro z hz
        rcases Finset.mem_map.mp hz with ⟨w, _, rfl⟩
        rw [SimpleGraph.mem_neighborFinset]
        have hadj : G.Adj q w.1 := (G.mem_neighborFinset q w.1).mp (Finset.mem_inter.mp w.2).1
        have hne : zq ≠ fR w := fun h =>
          G.ne_of_adj hadj (inr_val_eq h)
        exact ⟨hne, q, Set.mem_singleton q, w.1, Set.mem_singleton w.1, hadj⟩
      have hz_not_TR : z_ex ∉ TR := by
        intro hmem
        rcases Finset.mem_map.mp hmem with ⟨w, _, hw_eq⟩
        exact hz_ex_fresh w.1 w.2 hw_eq.symm
      have hins_sub : insert z_ex TR ⊆ K.neighborFinset zq :=
        Finset.insert_subset hz_ex_mem hTR_sub
      have hcard_ins : (insert z_ex TR).card ≤ K.degree zq := Finset.card_le_card hins_sub
      rw [Finset.card_insert_of_notMem hz_not_TR] at hcard_ins
      have hTR_card : TR.card = (G.neighborFinset q ∩ R).card := by simp [TR]
      change d + 1 ≤ K.degree zq
      omega

  -- Bound BQ.card ≤ d * (A_rep.card + L.card + U.card)
  have hBQ_bound : BQ.card ≤ d * (A_rep.card + L.card + U.card) := by
    let embBQ : {q : V // q ∈ BQ} ↪ VK :=
      ⟨fun q => Sum.inr ⟨q.1, hnot_inMarked_of_R q.1
          (Finset.mem_inter.mp (Finset.mem_inter.mp q.2).2).2⟩,
       fun a b h => Subtype.ext (inr_val_eq h)⟩
    let SBQ : Finset VK := BQ.attach.map embBQ
    have hSBQ_sub_SK : SBQ ⊆ S_K := by
      intro z hz
      rcases Finset.mem_map.mp hz with ⟨q, _, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_union_right _ q.2⟩
    have hBQ_sum : (d + 1) * BQ.card ≤ ∑ z ∈ S_K, K.degree z := by
      calc (d + 1) * BQ.card = ∑ _q ∈ BQ.attach, (d + 1) := by
            rw [Finset.sum_const, Finset.card_attach, smul_eq_mul, Nat.mul_comm]
        _ ≤ ∑ q ∈ BQ.attach, K.degree (embBQ q) :=
            Finset.sum_le_sum (fun q _ => hBQ_deg q.1 q.2)
        _ = ∑ z ∈ SBQ, K.degree z :=
            (Finset.sum_map BQ.attach embBQ (fun z => K.degree z)).symm
        _ ≤ ∑ z ∈ S_K, K.degree z :=
            Finset.sum_le_sum_of_subset_of_nonneg hSBQ_sub_SK (fun _ _ _ => Nat.zero_le _)
    have h1 : (d + 1) * BQ.card ≤ d * S_K.card := hBQ_sum.trans hsum_SK_deg
    rw [hSK_card] at h1
    nlinarith

  -- Bound (Q \ BQ).card ≤ ∑_{z ∈ S_K} K.degree z
  have hQdiff_bound : (Q \ BQ).card ≤ ∑ z ∈ S_K, K.degree z := by
    -- Every q ∈ Q \ BQ has a neighbor in S_K
    have hex_SK_nbr : ∀ (q : V) (hqDiff : q ∈ Q \ BQ), ∃ z ∈ S_K,
        K.Adj z (Sum.inr ⟨q, hnot_inMarked_of_R q (Finset.mem_inter.mp (Finset.mem_sdiff.mp hqDiff).1).2⟩) := by
      intro q hqDiff
      rcases Finset.mem_sdiff.mp hqDiff with ⟨hqQ, hqNotBQ⟩
      rcases Finset.mem_inter.mp hqQ with ⟨hqH, hqR⟩
      have hqNotB : q ∉ B := fun hB => hqNotBQ (Finset.mem_inter.mpr ⟨hB, hqQ⟩)
      have hqdeg : G.degree q = d := by
        by_contra hne
        exact hqNotB (Finset.mem_filter.mpr ⟨Finset.mem_univ q, hne⟩)
      have hRnbr_eq : G.neighborFinset q ∩ R = G.neighborFinset q := by
        apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
        calc (G.neighborFinset q).card = d := hqdeg
          _ ≤ (G.neighborFinset q ∩ R).card := hQ_Rnbrs q hqQ
      have hqNotF : q ∉ F := (Finset.mem_sdiff.mp (hH_sub_C hqH)).2
      have hexB : ∃ u ∈ B, q ∈ closedNbhd G u := by
        by_contra hnone
        exact hqNotF (Finset.mem_filter.mpr ⟨Finset.mem_univ q, fun u hu hqu => hnone ⟨u, hu, hqu⟩⟩)
      rcases hexB with ⟨u, huB, hqu⟩
      have hadj_qu : G.Adj q u := by
        simp only [closedNbhd, Finset.mem_insert, SimpleGraph.mem_neighborFinset] at hqu
        rcases hqu with rfl | hadj
        · exact False.elim (hqNotB huB)
        · exact hadj.symm
      have hu_nbr : u ∈ G.neighborFinset q := (G.mem_neighborFinset q u).mpr hadj_qu
      have huR : u ∈ R := by
        rw [← hRnbr_eq] at hu_nbr
        exact (Finset.mem_inter.mp hu_nbr).2
      have huNotU : u ∉ U := by
        intro huU
        apply (Finset.mem_filter.mp huU).2 q hqH
        simp only [closedNbhd, Finset.mem_insert, SimpleGraph.mem_neighborFinset]
        exact Or.inr hadj_qu
      have huLUBQ : u ∈ L ∪ U ∪ BQ := by
        have huR' := huR
        rw [← hR_part] at huR'
        rcases Finset.mem_union.mp huR' with huQU | huL
        · rcases Finset.mem_union.mp huQU with huQ | huU
          · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨huB, huQ⟩)
          · exact False.elim (huNotU huU)
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ huL)
      let zu : VK := Sum.inr ⟨u, hnot_inMarked_of_R u huR⟩
      have hzu_SK : zu ∈ S_K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, huLUBQ⟩
      have hne_zu_q : zu ≠ Sum.inr ⟨q, hnot_inMarked_of_R q hqR⟩ :=
        fun h => G.ne_of_adj hadj_qu.symm (inr_val_eq h)
      exact ⟨zu, hzu_SK, hne_zu_q, u, Set.mem_singleton u, q, Set.mem_singleton q, hadj_qu.symm⟩
    let embQdiff : {q : V // q ∈ Q \ BQ} ↪ VK :=
      ⟨fun q => Sum.inr ⟨q.1, hnot_inMarked_of_R q.1
          (Finset.mem_inter.mp (Finset.mem_sdiff.mp q.2).1).2⟩,
       fun a b h => Subtype.ext (inr_val_eq h)⟩
    let SQdiff : Finset VK := (Q \ BQ).attach.map embQdiff
    calc (Q \ BQ).card = SQdiff.card := by simp [SQdiff]
      _ ≤ ∑ y ∈ SQdiff, (K.neighborFinset y ∩ S_K).card := by
          rw [Finset.card_eq_sum_ones]
          apply Finset.sum_le_sum
          intro y hy
          rcases Finset.mem_map.mp hy with ⟨q, _, rfl⟩
          rcases hex_SK_nbr q.1 q.2 with ⟨z, hzSK, hadj⟩
          exact Finset.card_pos.mpr ⟨z, Finset.mem_inter.mpr
            ⟨(K.mem_neighborFinset _ z).mpr hadj.symm, hzSK⟩⟩
      _ = ∑ y ∈ SQdiff, ∑ z ∈ S_K, (if K.Adj z y then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
          congr 1
          ext z
          simp [Finset.mem_inter, SimpleGraph.mem_neighborFinset, K.adj_comm, and_comm]
      _ = ∑ z ∈ S_K, ∑ y ∈ SQdiff, (if K.Adj z y then 1 else 0) := Finset.sum_comm
      _ ≤ ∑ z ∈ S_K, K.degree z := by
          apply Finset.sum_le_sum
          intro z _
          rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
          have hsub : SQdiff.filter (fun y => K.Adj z y) ⊆ K.neighborFinset z := by
            intro y hy
            exact (K.mem_neighborFinset z y).mpr (Finset.mem_filter.mp hy).2
          exact Finset.card_le_card hsub

  -- Combine Q.card ≤ d * (d + 2) * (w + ℓ + |U|)
  have hQ_bound_nat : Q.card ≤ d * (d + 2) * (rd.wCard + rd.ell G + U.card) := by
    have hQ_split : Q.card = BQ.card + (Q \ BQ).card := by
      have hsub : BQ ⊆ Q := Finset.inter_subset_right
      have h := Finset.card_sdiff_add_card_eq_card hsub
      omega
    have hSK_le : S_K.card ≤ (d + 1) * (A_rep.card + L.card + U.card) := by
      rw [hSK_card]
      nlinarith [hBQ_bound]
    have hQdiff_le : (Q \ BQ).card ≤ d * (d + 1) * (A_rep.card + L.card + U.card) := by
      calc (Q \ BQ).card ≤ ∑ z ∈ S_K, K.degree z := hQdiff_bound
        _ ≤ d * S_K.card := hsum_SK_deg
        _ ≤ d * ((d + 1) * (A_rep.card + L.card + U.card)) := Nat.mul_le_mul_left d hSK_le
        _ = d * (d + 1) * (A_rep.card + L.card + U.card) := (Nat.mul_assoc _ _ _).symm
    have hQ_le1 : Q.card ≤ d * (d + 2) * (A_rep.card + L.card + U.card) := by
      nlinarith [hQ_split, hBQ_bound, hQdiff_le]
    have hell_eq : rd.ell G = L.card := rfl
    rw [hell_eq]
    have hmono : A_rep.card + L.card + U.card ≤ rd.wCard + L.card + U.card := by omega
    exact hQ_le1.trans (Nat.mul_le_mul_left (d * (d + 2)) hmono)

  -- Final real combination for |D|
  have hD_card_nat : D.card ≤ rd.wCard + (H \ R).card + Q.card + U.card := by
    have hH_split : H.card = Q.card + (H \ R).card :=
      (Finset.card_inter_add_card_sdiff H R).symm
    have hD_le : D.card ≤ W.card + H.card + U.card := by
      change (W ∪ H ∪ U).card ≤ W.card + H.card + U.card
      exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    have hw_eq : rd.wCard = W.card := rfl
    omega
  have hD_card_r : (D.card : ℝ) ≤ (rd.wCard : ℝ) + ((H \ R).card : ℝ) + (Q.card : ℝ) + (U.card : ℝ) := by
    exact_mod_cast hD_card_nat
  have hQ_bound_r : (Q.card : ℝ) ≤
      (d : ℝ) * ((d : ℝ) + 2) * ((rd.wCard : ℝ) + (rd.ell G : ℝ) + (U.card : ℝ)) := by
    exact_mod_cast hQ_bound_nat
  have hw_nonneg : (0 : ℝ) ≤ (rd.wCard : ℝ) := Nat.cast_nonneg _
  have hU_nonneg : (0 : ℝ) ≤ (U.card : ℝ) := Nat.cast_nonneg _
  have hstep_mid : (D.card : ℝ) ≤
      ((d : ℝ) + 1) ^ 2 * ((rd.wCard : ℝ) + (rd.ell G : ℝ) + (U.card : ℝ)) := by
    nlinarith [hD_card_r, hHR_le_ell, hQ_bound_r, hw_nonneg, hU_nonneg]
  have hb2_nonneg : (0 : ℝ) ≤ ((d : ℝ) + 1) ^ 2 := sq_nonneg _
  calc (D.card : ℝ)
      ≤ ((d : ℝ) + 1) ^ 2 * ((rd.wCard : ℝ) + (rd.ell G : ℝ)) +
          ((d : ℝ) + 1) ^ 2 * (U.card : ℝ) := by linarith [hstep_mid]
    _ ≤ ((d : ℝ) + 1) ^ 2 * ((rd.wCard : ℝ) + (rd.ell G : ℝ)) +
          ((d : ℝ) + 1) ^ 2 * ((d : ℝ) * rd.P G) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hU_le_dP hb2_nonneg)
    _ = ((d : ℝ) + 1) ^ 2 * ((rd.wCard : ℝ) + (rd.ell G : ℝ)) +
          (d : ℝ) * ((d : ℝ) + 1) ^ 2 * rd.P G := by ring
