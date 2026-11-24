-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.not_zero_adj_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:36:07.73071+00:00
-- url     : https://prove2.me/submissions/3c5479e1-1159-45b9-ae72-adbe6774e875

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_exists_core_vertex_ne_two
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_dist_from_core
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_endPoint_not_core
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_center_mem_core
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_delete_zero_connected
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_cut_after_delete

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
open WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
variable {G : SimpleGraph α} {K : Finset α} (F : PendantGeodesics G K)
namespace WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
theorem _root_.solution (hG : G.Connected) (hcard : 3 ≤ K.card)
    (hK : (G.induce (K : Set α)).Connected)
    (hdel : ∀ x : ↥(K : Set α),
      ((G.induce (K : Set α)).induce ({x}ᶜ : Set ↥(K : Set α))).Connected)
    (hdelete : DeletionCenters G) (hr : 1 ≤ G.radius.toNat)
    (a b : ↥(K : Set α)) (hab : G.Adj a b)
    (ha : (F.path a).length = 0) (hb : 0 < (F.path b).length) : False := by
  obtain ⟨v, hva, hvb⟩ := exists_core_vertex_ne_two hcard a b
  have heba : F.endPoint b ≠ (a : α) :=
    fun heq => F.endPoint_not_core hG b hb (heq.symm ▸ a.property)
  have hcut := F.cut_after_delete hG a b v hb hab.ne.symm heba
    (fun heq => hvb (congrArg Subtype.val heq)) hva
  obtain ⟨w, _, hw, hwa, hwb⟩ := hdelete a
    (F.delete_zero_connected hG hcard hK hdel a ha) hcut
  let w' : ↥(K : Set α) := ⟨w, F.center_mem_core hG hw⟩
  have hdist := F.dist_from_core hG b w' (F.path b).end_mem_support
  rw [← F.geodesic b] at hdist
  have hfar := hwb (F.endPoint b) heba
  have htri := hG.dist_triangle (u := w) (v := (b : α)) (w := (a : α))
  have hba : G.dist (b : α) a = 1 := dist_eq_one_iff_adj.mpr hab.symm
  change G.dist w (F.endPoint b) = G.dist w b + (F.path b).length at hdist
  omega
end WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
