-- Prove2me | solution 1 for ShortBroadcastDom.lemma_7_3_first_selection
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:20:54.150218+00:00
-- url     : https://prove2.me/submissions/c7413df0-c22c-433f-9318-aca1e97687bf

import Definitions.Def_ShortBroadcastDom_firstSel
import Definitions.Def_ShortBroadcastDom_tauOn

open ShortBroadcastDom

namespace Aux_7_3

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

end Aux_7_3

theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 2 ≤ d) :
    defects G d ⊆ remDemands G d ∧
    (∀ v, v ∉ firstSel G d →
      (∃ z : ℤ, selCost G d v = z) ∧ 1 ≤ selCost G d v ∧ selCost G d v ≤ (d : ℝ) + 1 ∧
      (selCost G d v = (d : ℝ) + 1 ↔ v ∈ remDemands G d) ∧
      (selCost G d v < (d : ℝ) + 1 →
        ((closedNbhd G v ∩ remDemands G d).card : ℝ) ≤ selCost G d v - 1)) ∧
    ((firstSel G d).card : ℝ) +
        tauOn G (Finset.univ \ firstSel G d) (remDemands G d) (selCost G d) ≤
      ((d : ℝ) + 1) * fracDom G := by
  let _ := hd
  have hpart1 : defects G d ⊆ remDemands G d := by
    intro b hb
    rw [remDemands, Finset.mem_filter]
    refine ⟨Finset.mem_univ b, fun u hu hbu => ?_⟩
    rw [firstSel, Finset.mem_filter] at hu
    exact hu.2 b hb ((Aux_7_3.mem_closedNbhd_comm G b u).mp hbu)
  have hpart2 : ∀ v, v ∉ firstSel G d →
      (∃ z : ℤ, selCost G d v = z) ∧ 1 ≤ selCost G d v ∧ selCost G d v ≤ (d : ℝ) + 1 ∧
      (selCost G d v = (d : ℝ) + 1 ↔ v ∈ remDemands G d) ∧
      (selCost G d v < (d : ℝ) + 1 →
        ((closedNbhd G v ∩ remDemands G d).card : ℝ) ≤ selCost G d v - 1) := by
    intro v hvF
    set k : ℕ := (G.neighborFinset v ∩ firstSel G d).card
    have hcost_eq : selCost G d v = ((d : ℝ) + 1) - (k : ℝ) := rfl
    have hk_deg : 0 < k → G.degree v = d := by
      intro hk_pos
      rcases Finset.card_pos.mp hk_pos with ⟨u, hu⟩
      rcases Finset.mem_inter.mp hu with ⟨huv_nbr, huF⟩
      by_contra hdeg
      have hv_def : v ∈ defects G d := Finset.mem_filter.mpr ⟨Finset.mem_univ v, hdeg⟩
      have huv_cl : u ∈ closedNbhd G v := by
        rw [closedNbhd, Finset.mem_insert]
        exact Or.inr huv_nbr
      exact (Finset.mem_filter.mp huF).2 v hv_def huv_cl
    have hk_le_d : k ≤ d := by
      by_cases hk0 : k = 0
      · omega
      · have hdeg := hk_deg (Nat.pos_of_ne_zero hk0)
        have hsub : G.neighborFinset v ∩ firstSel G d ⊆ G.neighborFinset v := Finset.inter_subset_left
        calc k ≤ (G.neighborFinset v).card := Finset.card_le_card hsub
          _ = G.degree v := rfl
          _ = d := hdeg
    have h_int : ∃ z : ℤ, selCost G d v = z := by
      refine ⟨(d : ℤ) + 1 - (k : ℤ), ?_⟩
      rw [hcost_eq]
      push_cast
      ring
    have h_ge1 : 1 ≤ selCost G d v := by
      rw [hcost_eq]
      have hk_real : (k : ℝ) ≤ (d : ℝ) := by exact_mod_cast hk_le_d
      linarith
    have h_leb : selCost G d v ≤ (d : ℝ) + 1 := by
      rw [hcost_eq]
      have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have h_iff : selCost G d v = (d : ℝ) + 1 ↔ v ∈ remDemands G d := by
      rw [hcost_eq]
      have hk0_iff : ((d : ℝ) + 1) - (k : ℝ) = (d : ℝ) + 1 ↔ k = 0 := by
        constructor
        · intro h
          have hk0r : (k : ℝ) = 0 := by linarith
          exact Nat.cast_eq_zero.mp hk0r
        · intro hk0
          simp [hk0]
      rw [hk0_iff, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      simp only [remDemands, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      constructor
      · intro hno u huF hvu
        simp only [closedNbhd, Finset.mem_insert, SimpleGraph.mem_neighborFinset] at hvu
        rcases hvu with rfl | hadj
        · exact hvF huF
        · exact hno u ⟨hadj.symm, huF⟩
      · intro hrem u ⟨hadj, huF⟩
        apply hrem u huF
        simp only [closedNbhd, Finset.mem_insert, SimpleGraph.mem_neighborFinset]
        exact Or.inr hadj.symm
    have h_lt : selCost G d v < (d : ℝ) + 1 →
        ((closedNbhd G v ∩ remDemands G d).card : ℝ) ≤ selCost G d v - 1 := by
      intro hlt
      have hk_pos : 0 < k := by
        rw [hcost_eq] at hlt
        have hkr : (0 : ℝ) < (k : ℝ) := by linarith
        exact_mod_cast hkr
      have hdeg : G.degree v = d := hk_deg hk_pos
      have hv_not_rem : v ∉ remDemands G d := by
        intro hv_rem
        have heq := h_iff.mpr hv_rem
        linarith
      have hcl_eq : closedNbhd G v ∩ remDemands G d = G.neighborFinset v ∩ remDemands G d := by
        ext w
        simp only [closedNbhd, Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hw, hw_rem⟩
          · exact False.elim (hv_not_rem hw_rem)
          · exact ⟨hw, hw_rem⟩
        · rintro ⟨hw, hw_rem⟩
          exact ⟨Or.inr hw, hw_rem⟩
      have hdisj : Disjoint (G.neighborFinset v ∩ remDemands G d)
          (G.neighborFinset v ∩ firstSel G d) := by
        rw [Finset.disjoint_left]
        intro w hw1 hw2
        have hw_rem := (Finset.mem_inter.mp hw1).2
        have hw_F := (Finset.mem_inter.mp hw2).2
        exact (Finset.mem_filter.mp hw_rem).2 w hw_F (Aux_7_3.self_mem_closedNbhd G w)
      have hunion_sub : (G.neighborFinset v ∩ remDemands G d) ∪
          (G.neighborFinset v ∩ firstSel G d) ⊆ G.neighborFinset v :=
        Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
      have hcard_sum : (G.neighborFinset v ∩ remDemands G d).card + k ≤ d := by
        calc (G.neighborFinset v ∩ remDemands G d).card + k
            = ((G.neighborFinset v ∩ remDemands G d) ∪
                (G.neighborFinset v ∩ firstSel G d)).card :=
              (Finset.card_union_of_disjoint hdisj).symm
          _ ≤ (G.neighborFinset v).card := Finset.card_le_card hunion_sub
          _ = G.degree v := rfl
          _ = d := hdeg
      rw [hcl_eq, hcost_eq]
      have hcard_real : ((G.neighborFinset v ∩ remDemands G d).card : ℝ) + (k : ℝ) ≤ (d : ℝ) := by
        exact_mod_cast hcard_sum
      linarith
    exact ⟨h_int, h_ge1, h_leb, h_iff, h_lt⟩
  refine ⟨hpart1, hpart2, ?_⟩
  set F : Finset V := firstSel G d
  set C : Finset V := Finset.univ \ F
  set R0 : Finset V := remDemands G d
  set c : V → ℝ := selCost G d
  let S_G : Set ℝ := {s : ℝ | ∃ y : V → ℝ, (∀ v, 0 ≤ y v) ∧
    (∀ v, v ∉ (Finset.univ : Finset V) → y v = 0) ∧
    (∀ r ∈ (Finset.univ : Finset V), 1 ≤ ∑ v ∈ closedNbhd G r, y v) ∧
    s = ∑ v, (1 : ℝ) * y v}
  have hfrac_eq : fracDom G = sInf S_G := rfl
  have hSG_ne : S_G.Nonempty := by
    refine ⟨∑ _v : V, (1 : ℝ) * 1, fun _ => 1, fun _ => zero_le_one, fun _ hv => (hv (Finset.mem_univ _)).elim, ?_, rfl⟩
    intro r _
    have hmem : r ∈ closedNbhd G r := Aux_7_3.self_mem_closedNbhd G r
    calc (1 : ℝ) ≤ ∑ v ∈ ({r} : Finset V), (1 : ℝ) := by simp
      _ ≤ ∑ v ∈ closedNbhd G r, (1 : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.singleton_subset_iff.mpr hmem) (fun _ _ _ => zero_le_one)
  let S_rem : Set ℝ := {s : ℝ | ∃ x : V → ℝ, (∀ v, 0 ≤ x v) ∧ (∀ v, v ∉ C → x v = 0) ∧
    (∀ r ∈ R0, 1 ≤ ∑ v ∈ closedNbhd G r, x v) ∧ s = ∑ v, c v * x v}
  have htau_eq : tauOn G C R0 c = sInf S_rem := rfl
  have hSrem_bdd : BddBelow S_rem := by
    refine ⟨0, ?_⟩
    rintro s ⟨x, hx0, hxC, -, rfl⟩
    apply Finset.sum_nonneg
    intro v _
    by_cases hvC : v ∈ C
    · have hvF : v ∉ F := (Finset.mem_sdiff.mp hvC).2
      have hc1 : 0 ≤ c v := by linarith [(hpart2 v hvF).2.1]
      exact mul_nonneg hc1 (hx0 v)
    · simp [hxC v hvC]
  have hb_pos : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  rw [hfrac_eq, htau_eq]
  have hbound : ((F.card : ℝ) + sInf S_rem) / ((d : ℝ) + 1) ≤ sInf S_G := by
    apply le_csInf hSG_ne
    rintro s ⟨y, hy0, -, hycov, rfl⟩
    rw [div_le_iff₀ hb_pos]
    let y' : V → ℝ := fun v => if v ∈ C then y v else 0
    have hy'_mem : (∑ v, c v * y' v) ∈ S_rem := by
      refine ⟨y', fun v => by by_cases h : v ∈ C <;> simp [y', h, hy0 v],
        fun v hv => by simp [y', hv], ?_, rfl⟩
      intro r hrR0
      have hsub : closedNbhd G r ⊆ C := by
        intro v hvr
        rw [Finset.mem_sdiff]
        refine ⟨Finset.mem_univ v, fun hvF => ?_⟩
        exact (Finset.mem_filter.mp hrR0).2 v hvF ((Aux_7_3.mem_closedNbhd_comm G v r).mp hvr)
      have hsum_eq : ∑ v ∈ closedNbhd G r, y' v = ∑ v ∈ closedNbhd G r, y v := by
        apply Finset.sum_congr rfl
        intro v hv
        simp [y', hsub hv]
      rw [hsum_eq]
      exact hycov r (Finset.mem_univ r)
    have htau_le : sInf S_rem ≤ ∑ v ∈ C, c v * y v := by
      calc sInf S_rem ≤ ∑ v, c v * y' v := csInf_le hSrem_bdd hy'_mem
        _ = ∑ v ∈ C, c v * y v := by
          rw [← Finset.sum_subset (Finset.subset_univ C)]
          · apply Finset.sum_congr rfl
            intro v hv
            simp [y', hv]
          · intro v _ hvC
            simp [y', hvC]
    have hF_le : (F.card : ℝ) ≤ ∑ v : V, ((closedNbhd G v ∩ F).card : ℝ) * y v := by
      calc (F.card : ℝ) = ∑ u ∈ F, (1 : ℝ) := by simp
        _ ≤ ∑ u ∈ F, ∑ v ∈ closedNbhd G u, y v := by
          apply Finset.sum_le_sum
          intro u _
          exact hycov u (Finset.mem_univ u)
        _ = ∑ u ∈ F, ∑ v : V, (if v ∈ closedNbhd G u then y v else 0) := by
          apply Finset.sum_congr rfl
          intro u _
          rw [Finset.sum_ite_mem, Finset.univ_inter]
        _ = ∑ v : V, ∑ u ∈ F, (if v ∈ closedNbhd G u then y v else 0) := Finset.sum_comm
        _ = ∑ v : V, ((closedNbhd G v ∩ F).card : ℝ) * y v := by
          apply Finset.sum_congr rfl
          intro v _
          have hcongr : ∑ u ∈ F, (if v ∈ closedNbhd G u then y v else 0) =
              ∑ u ∈ closedNbhd G v ∩ F, y v := by
            rw [← Finset.sum_filter]
            apply Finset.sum_congr _ (fun _ _ => rfl)
            ext u
            simp [Finset.mem_filter, Finset.mem_inter, Aux_7_3.mem_closedNbhd_comm G v u, and_comm]
          rw [hcongr, Finset.sum_const, nsmul_eq_mul]
    have hC_sum : ∑ v ∈ C, c v * y v = ∑ v : V, (if v ∈ C then c v * y v else 0) := by
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    calc (F.card : ℝ) + sInf S_rem
        ≤ (∑ v : V, ((closedNbhd G v ∩ F).card : ℝ) * y v) + ∑ v ∈ C, c v * y v :=
          add_le_add hF_le htau_le
      _ = ∑ v : V, (((closedNbhd G v ∩ F).card : ℝ) * y v + (if v ∈ C then c v * y v else 0)) := by
          rw [hC_sum, ← Finset.sum_add_distrib]
      _ ≤ ∑ v : V, (((d : ℝ) + 1) * y v) := by
          apply Finset.sum_le_sum
          intro v _
          by_cases hvF : v ∈ F
          · have hvC : v ∉ C := fun h => (Finset.mem_sdiff.mp h).2 hvF
            simp only [hvC, ↓reduceIte, add_zero]
            have hv_not_def : v ∉ defects G d := by
              intro hdef
              exact (Finset.mem_filter.mp hvF).2 v hdef (Aux_7_3.self_mem_closedNbhd G v)
            have hdeg : G.degree v = d := by
              by_contra hne
              exact hv_not_def (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hne⟩)
            have hcl_card : (closedNbhd G v).card = d + 1 := by
              rw [closedNbhd, Finset.card_insert_of_notMem (G.notMem_neighborFinset_self v)]
              exact congrArg (· + 1) hdeg
            have hint_le : (closedNbhd G v ∩ F).card ≤ d + 1 := by
              calc (closedNbhd G v ∩ F).card ≤ (closedNbhd G v).card :=
                Finset.card_le_card Finset.inter_subset_left
                _ = d + 1 := hcl_card
            have hint_real : ((closedNbhd G v ∩ F).card : ℝ) ≤ (d : ℝ) + 1 := by
              exact_mod_cast hint_le
            exact mul_le_mul_of_nonneg_right hint_real (hy0 v)
          · have hvC : v ∈ C := Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hvF⟩
            simp only [hvC, ↓reduceIte]
            have hcl_eq : closedNbhd G v ∩ F = G.neighborFinset v ∩ F := by
              ext u
              simp only [closedNbhd, Finset.mem_inter, Finset.mem_insert]
              constructor
              · rintro ⟨rfl | hu, huF⟩
                · exact False.elim (hvF huF)
                · exact ⟨hu, huF⟩
              · rintro ⟨hu, huF⟩
                exact ⟨Or.inr hu, huF⟩
            have hcoeff : ((closedNbhd G v ∩ F).card : ℝ) + c v = (d : ℝ) + 1 := by
              rw [hcl_eq]
              dsimp [c, selCost]
              ring
            exact le_of_eq (calc ((closedNbhd G v ∩ F).card : ℝ) * y v + c v * y v
                = (((closedNbhd G v ∩ F).card : ℝ) + c v) * y v := by ring
              _ = ((d : ℝ) + 1) * y v := by rw [hcoeff])
      _ = (∑ v : V, (1 : ℝ) * y v) * ((d : ℝ) + 1) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro v _
          ring
  exact (div_le_iff₀ hb_pos).mp hbound |> fun h => by linarith
