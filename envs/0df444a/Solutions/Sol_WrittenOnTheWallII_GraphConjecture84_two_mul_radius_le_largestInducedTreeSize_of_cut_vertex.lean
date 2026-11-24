-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.two_mul_radius_le_largestInducedTreeSize_of_cut_vertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:40:17.946769+00:00
-- url     : https://prove2.me/submissions/a8aa5206-e71d-46a4-99dd-fe1236d2699d

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_dist_add_one_le_largestInducedTreeSize
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_radius_add_one_le_largestInducedTreeSize
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_largestInducedTreeSize_induce_le
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_radius_drop_witness
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_two_mul_radius_le_largestInducedTreeSize_of_isTree
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_chung_induced_tree_bound
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_cut_vertex_two_side_reduction
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_exists_maximal_vertex_core
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_maximal_core_unique_attachment
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_exists_two_adj_of_connected_deletions
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_exists_pendant_geodesic_family
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_all_positive
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_common_length
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_radius_le_core_radius_add
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_lift_induced_tree
public import Theorems.Thm_SimpleGraph_Connected_exists_induced_tree_containing_pair
public import Theorems.Thm_SimpleGraph_card_le_largestInducedTreeSize
public import Theorems.Thm_SimpleGraph_exists_maximum_induced_tree_containing


set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α}
    (hG : G.Connected) (hcut : ∃ x, ¬ (G.induce ({x}ᶜ : Set α)).Connected) :
    2 * G.radius.toNat ≤ largestInducedTreeSize G := by
  classical
  induction hn : Fintype.card α using Nat.strong_induction_on generalizing α with
  | h n ih =>
    haveI : Nonempty α := hG.nonempty
    have htree := radius_add_one_le_largestInducedTreeSize hG
    by_cases hr : G.radius.toNat ≤ 1
    · omega
    have hr : 2 ≤ G.radius.toNat := by omega
    by_cases hT : G.IsTree
    · exact two_mul_radius_le_largestInducedTreeSize_of_isTree hT
    by_contra hbound
    have hlt : largestInducedTreeSize G < 2 * G.radius.toNat := by omega
    have hsmall (S : Set α) (hproper : S ≠ Set.univ) (hS : (G.induce S).Connected)
        (hcutS : ∃ x, ¬ ((G.induce S).induce ({x}ᶜ : Set S)).Connected) :
        2 * (G.induce S).radius.toNat ≤ largestInducedTreeSize (G.induce S) := by
      have hmiss : ∃ x : α, x ∉ S := by
        by_contra! hall
        exact hproper (Set.eq_univ_of_forall hall)
      obtain ⟨x, hx⟩ := hmiss
      have hcard : Fintype.card S < n := by
        rw [← hn]
        exact Fintype.card_subtype_lt hx
      exact ih _ hcard hS hcutS rfl
    have hdelete (x : α) (hx : (G.induce ({x}ᶜ : Set α)).Connected)
        (hcutx : ∃ y, ¬ ((G.induce ({x}ᶜ : Set α)).induce ({y}ᶜ : Set ↥({x}ᶜ : Set α))).Connected) :
        ∃ c : α, c ≠ x ∧ G.eccent c = G.radius ∧ G.dist c x = G.radius.toNat ∧
          ∀ z : α, z ≠ x → G.dist c z ≤ G.radius.toNat - 1 := by
      have hproper : ({x}ᶜ : Set α) ≠ Set.univ := by
        intro heq
        have hxmem : x ∈ ({x}ᶜ : Set α) := heq ▸ Set.mem_univ x
        simpa using hxmem
      have hboundH := hsmall ({x}ᶜ : Set α) hproper hx hcutx
      have htrans := largestInducedTreeSize_induce_le G ({x}ᶜ : Set α)
      have hdrop : (G.induce ({x}ᶜ : Set α)).radius.toNat ≤ G.radius.toNat - 1 := by omega
      exact radius_drop_witness hG x hx (by omega) hdrop
    have htwosides (c : α) (hc : ¬ (G.induce ({c}ᶜ : Set α)).Connected) :=
      cut_vertex_two_side_reduction hG hr hlt (fun S _ => hsmall S) c hc
    obtain ⟨c, hc⟩ := hcut
    obtain ⟨a, b, q, hq, hsep, hgap, hcover⟩ := htwosides c hc
    have hcyc : ¬ G.IsAcyclic := fun hacyc => hT ⟨hG, hacyc⟩
    obtain ⟨K, hKcard, hKconn, hKdel, hKmax⟩ := exists_maximal_vertex_core hcyc
    have hKne : K.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨F⟩ := exists_pendant_geodesic_family hG K hKcard hKconn hKdel
      (fun z w hzw _ _ ha hb haz hbw =>
        maximal_core_unique_attachment K hKcard hKconn hKdel hKmax z w hzw ha hb haz hbw)
      htwosides
    have hpos := F.all_positive hG hKcard hKconn hKdel hdelete (by omega) ⟨c, hc⟩
    obtain ⟨L, hL, hLen⟩ := F.common_length hG hKcard hKconn hdelete (by omega) hpos
    let H := G.induce (K : Set α)
    haveI : Nonempty ↥(K : Set α) := hKconn.nonempty
    let v : ↥(K : Set α) := Classical.choice inferInstance
    obtain ⟨t, _, _, ht⟩ := hKconn.exists_induced_tree_containing_pair v v
    obtain ⟨S, _, hS, hSmax⟩ := H.exists_maximum_induced_tree_containing ∅
      ⟨t, Finset.empty_subset _, ht⟩
    have hcard : largestInducedTreeSize H = S.card := by
      apply le_antisymm
      · apply csSup_le'
        rintro m ⟨T, rfl, hT⟩
        exact hSmax T (Finset.empty_subset _) hT
      · exact card_le_largestInducedTreeSize hS
    have hlift := F.lift_induced_tree hG L hLen S hS
    rw [← hcard] at hlift
    have hrad := F.radius_le_core_radius_add hG hKconn L hLen
    change G.radius.toNat ≤ H.radius.toNat + L at hrad
    have hchung := chung_induced_tree_bound (G := H) hKconn
    obtain ⟨u, w, hvu, _, _⟩ := exists_two_adj_of_connected_deletions
      (G := H) (by simpa using hKcard) hKconn hKdel v
    have htwo : 2 ≤ largestInducedTreeSize H := by
      have hedge := dist_add_one_le_largestInducedTreeSize (hKconn v u)
      rw [dist_eq_one_iff_adj.mpr hvu] at hedge
      exact hedge
    by_cases hs : H.radius.toNat ≤ 1
    · have hmul := Nat.mul_le_mul_right (L + 1) htwo
      omega
    · have hthree : 3 ≤ largestInducedTreeSize H := by omega
      have hmul := Nat.mul_le_mul_right L hthree
      have hcount : 2 * G.radius.toNat ≤ largestInducedTreeSize H * (L + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
        omega
      omega
end WrittenOnTheWallII.GraphConjecture84
