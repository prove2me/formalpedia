-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.chung_induced_tree_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:37:46.453782+00:00
-- url     : https://prove2.me/submissions/2a9101ce-69dc-4eb7-a3a4-2e3dee0cc769

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_radius_add_one_le_largestInducedTreeSize
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_largestInducedTreeSize_induce_le
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_radius_drop_witness
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_chung_bound_of_unique_farthest

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α} (hG : G.Connected) :
    2 * G.radius.toNat ≤ largestInducedTreeSize G + 1 := by
  classical
  induction hn : Fintype.card α using Nat.strong_induction_on generalizing α with
  | h n ih =>
    haveI : Nonempty α := hG.nonempty
    have htree := radius_add_one_le_largestInducedTreeSize (G := G) hG
    by_cases hr : G.radius.toNat ≤ 2
    · omega
    have hr : 3 ≤ G.radius.toNat := by omega
    haveI : Nontrivial α := by
      rcases subsingleton_or_nontrivial α with hsub | hnt
      · have hzero : G.radius = 0 := G.radius_eq_zero_iff.mpr ⟨hG.nonempty, hsub⟩
        simp only [hzero, ENat.toNat_zero] at hr
        omega
      · exact hnt
    obtain ⟨x, hx⟩ := hG.exists_connected_induce_compl_singleton_of_finite_nontrivial
    let H := G.induce ({x}ᶜ : Set α)
    have hcard : Fintype.card ↥({x}ᶜ : Set α) < n := by
      rw [← hn]
      exact Fintype.card_subtype_lt (x := x) (by simp)
    by_cases hrad : G.radius.toNat ≤ H.radius.toNat
    · have hsmall := ih _ hcard (G := H) hx rfl
      have htrans : largestInducedTreeSize H ≤ largestInducedTreeSize G :=
        largestInducedTreeSize_induce_le G ({x}ᶜ : Set α)
      omega
    · have hdrop : H.radius.toNat ≤ G.radius.toNat - 1 := by omega
      obtain ⟨c, _, _, hcx, hother⟩ := radius_drop_witness hG x hx (by omega) hdrop
      exact chung_bound_of_unique_farthest hG hr hcx hother
end WrittenOnTheWallII.GraphConjecture84
