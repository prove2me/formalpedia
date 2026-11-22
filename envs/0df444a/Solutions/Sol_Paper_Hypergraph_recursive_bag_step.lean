-- Prove2me | solution 1 for Paper.Hypergraph.recursive_bag_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:13:33.622865+00:00
-- url     : https://prove2.me/submissions/07ab652a-f11f-496e-be18-ba7655c3d940

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_coverCost_attained
import Theorems.Thm_Paper_Hypergraph_cover_restriction
import Theorems.Thm_Paper_Hypergraph_primal_induce_adj
import Theorems.Thm_Paper_Hypergraph_component_mem_iff_reachable
import Theorems.Thm_Paper_Hypergraph_setCoverCost_mono
import Theorems.Thm_Paper_Hypergraph_setCoverCost_union_le
import Theorems.Thm_Paper_Hypergraph_setCoverCost_singleton_le
import Theorems.Thm_Paper_Hypergraph_cover_mass_ge_one
import Theorems.Thm_Paper_Hypergraph_induce_induce
import Theorems.Thm_Paper_Hypergraph_sep_bounds
import Theorems.Thm_Paper_Hypergraph_exists_separator_lt
import Theorems.Thm_Paper_Hypergraph_component_induce_mono
import Theorems.Thm_Paper_Hypergraph_cover_inter_le_mass

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {η r : ℝ} (hη : 0 < η ∧ η < 1)
    (hr : H.sep η < r) {W Z : Finset ℕ} (hW : W ⊆ H.vertices) (hZ : Z ⊆ W)
    (hcost : H.setCoverCost Z ≤ (r + 1) / (1 - η)) {u : ℕ} (hu : u ∈ W \ Z) :
    ∃ B, Z ⊆ B ∧ B ⊆ W ∧ u ∈ B ∧
      H.setCoverCost B ≤ (r + 1) / (1 - η) + r + 1 ∧
      ∀ K ∈ (H.induce (W \ B)).components,
        H.setCoverCost ((H.induce W).boundary B K) ≤ (r + 1) / (1 - η) := by
  let L := (r + 1) / (1 - η)
  have hr0 : 0 ≤ r := (H.sep_bounds hη).1.trans hr.le
  have hden : 0 < 1 - η := sub_pos.mpr hη.2
  have hL0 : 0 ≤ L := div_nonneg (by linarith) hden.le
  have hL : L = r + 1 + η * L := by
    dsimp [L]; field_simp [ne_of_gt hden]; ring
  have huW : u ∈ W := (mem_sdiff.mp hu).1
  have huV := hW huW
  by_cases hZe : Z = ∅
  · subst Z
    refine ⟨{u}, empty_subset _, singleton_subset_iff.mpr huW, mem_singleton_self _, ?_, ?_⟩
    · exact (H.setCoverCost_singleton_le huV).trans (by change 1 ≤ L + r + 1; linarith)
    · intro K hK
      have hh := (H.setCoverCost_mono (filter_subset (fun z => ∃ v ∈ K,
        (H.induce W).primal.Adj z v) {u})).trans (H.setCoverCost_singleton_le huV)
      exact hh.trans (by change 1 ≤ L; nlinarith)
  · have hZJ : Z ⊆ (H.induce W).vertices := fun v hv => mem_inter.mpr ⟨hW (hZ hv), hZ hv⟩
    obtain ⟨γ, hγ, hγ1, hγcost⟩ := (H.induce W).coverCost_attained
      (x := indicator Z) (by intro v hv; simp only [indicator]; split_ifs <;> norm_num)
    have hγmass : 0 < ∑ e ∈ (H.induce W).edges, γ e :=
      lt_of_lt_of_le (by norm_num) ((H.induce W).cover_mass_ge_one hZJ
        (nonempty_iff_ne_empty.mpr hZe) hγ)
    have hγweight : (H.induce W).EdgeWeight γ :=
      ⟨fun e he => ⟨hγ.1 e he, hγ1 e he⟩, hγmass⟩
    obtain ⟨S, hS, hScost⟩ := H.exists_separator_lt hW hγweight hη hr
    have hSW : S ⊆ W := fun v hv => (mem_inter.mp (hS.1 hv)).2
    have hmass : (∑ e ∈ (H.induce W).edges, γ e) = H.setCoverCost Z := by
      rw [← hγcost]
      exact H.cover_restriction hZ
    let B := Z ∪ S ∪ {u}
    have hBW : B ⊆ W := union_subset (union_subset hZ hSW) (singleton_subset_iff.mpr huW)
    refine ⟨B, subset_trans subset_union_left subset_union_left, hBW, by simp [B], ?_, ?_⟩
    · exact (H.setCoverCost_union_le (Z ∪ S) {u}).trans (by
        have hh := H.setCoverCost_union_le Z S
        have hs := H.setCoverCost_singleton_le huV
        dsimp [L] at *
        linarith)
    · intro K hK
      have hSB : S ⊆ B := subset_trans subset_union_right subset_union_left
      have hsmall : W \ B ⊆ W \ S := fun v hv =>
        mem_sdiff.mpr ⟨(mem_sdiff.mp hv).1, fun hs => (mem_sdiff.mp hv).2 (hSB hs)⟩
      obtain ⟨C, hC, hKC⟩ := H.component_induce_mono hsmall hK
      have hWcap : H.vertices ∩ W = W := inter_eq_right.mpr hW
      have hC' : C ∈ ((H.induce W).induce ((H.induce W).vertices \ S)).components := by
        rw [H.induce_induce]
        have hid : W ∩ (W \ S) = W \ S := inter_eq_right.mpr sdiff_subset
        change C ∈ (H.induce (W ∩ ((H.vertices ∩ W) \ S))).components
        rw [hWcap, hid]
        exact hC
      have hCsub : C ⊆ (H.induce (W \ S)).vertices := mem_powerset.mp (mem_filter.mp hC).1
      have hcontain : (H.induce W).boundary B K ⊆ S ∪ {u} ∪ (Z ∩ C) := by
        intro z hz
        obtain ⟨hzB, v, hvK, hzv⟩ := mem_filter.mp hz
        by_cases hzS : z ∈ S
        · exact mem_union_left _ (mem_union_left _ hzS)
        by_cases hzu : z = u
        · exact mem_union_left _ (mem_union_right _ (mem_singleton.mpr hzu))
        have hzZ : z ∈ Z := by simpa [B, hzS, hzu] using hzB
        have hzJ : z ∈ (H.induce (W \ S)).vertices := mem_inter.mpr ⟨hW (hZ hzZ), mem_sdiff.mpr ⟨hZ hzZ, hzS⟩⟩
        have hvC := hKC hvK
        have hvWS := (mem_inter.mp (hCsub hvC)).2
        have hadj : (H.induce (W \ S)).primal.Adj v z :=
          (H.primal_induce_adj _ hvWS (mem_sdiff.mpr ⟨hZ hzZ, hzS⟩)).mpr
            ((H.primal_induce_adj W (hZ hzZ) (mem_sdiff.mp hvWS).1).mp hzv).symm
        have hzC := ((H.induce (W \ S)).component_mem_iff_reachable hC hvC hzJ).mpr hadj.reachable
        exact mem_union_right _ (mem_inter.mpr ⟨hzZ, hzC⟩)
      have hZC : H.setCoverCost (Z ∩ C) ≤ η * H.setCoverCost Z := by
        rw [← H.cover_restriction (inter_subset_left.trans hZ)]
        exact ((H.induce W).cover_inter_le_mass hγ).trans (by simpa [hmass] using hS.2 C hC')
      calc
        H.setCoverCost ((H.induce W).boundary B K) ≤ H.setCoverCost (S ∪ {u} ∪ (Z ∩ C)) := H.setCoverCost_mono hcontain
        _ ≤ H.setCoverCost (S ∪ {u}) + H.setCoverCost (Z ∩ C) := H.setCoverCost_union_le _ _
        _ ≤ r + 1 + η * L := by
          have hh := H.setCoverCost_union_le S {u}
          have hs := H.setCoverCost_singleton_le huV
          have hz := mul_le_mul_of_nonneg_left hcost hη.1.le
          change H.setCoverCost Z ≤ L at hcost
          change H.setCoverCost (S ∪ {u}) + H.setCoverCost (Z ∩ C) ≤ r + 1 + η * L
          nlinarith
        _ = _ := hL.symm
end Paper.Hypergraph
