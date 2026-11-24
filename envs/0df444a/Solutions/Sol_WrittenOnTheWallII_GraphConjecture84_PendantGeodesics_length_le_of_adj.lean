-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.length_le_of_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:37:20.045935+00:00
-- url     : https://prove2.me/submissions/00d97511-a108-4df3-a72c-7fcec039acb8

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_exists_core_vertex_ne_two
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_dist_from_core
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_endPoint_not_core
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_center_mem_core
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_delete_endPoint_connected
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_cut_after_delete
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_endPoint_injective

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
    (hdelete : DeletionCenters G) (hr : 1 ≤ G.radius.toNat)
    (hpos : ∀ c, 0 < (F.path c).length)
    (a b : ↥(K : Set α)) (hab : G.Adj a b) :
    (F.path b).length ≤ (F.path a).length := by
  obtain ⟨d, hda, _⟩ := exists_core_vertex_ne_two hcard a a
  have hda' : d ≠ a := fun heq => hda (congrArg Subtype.val heq)
  have hxK := F.endPoint_not_core hG a (hpos a)
  have hdxa : (d : α) ≠ F.endPoint a := fun heq => hxK (heq ▸ d.property)
  have haxa : (a : α) ≠ F.endPoint a := fun heq => hxK (heq ▸ a.property)
  have hed : F.endPoint d ≠ F.endPoint a := fun heq => hda' (F.endPoint_injective hG heq)
  have hcut := F.cut_after_delete hG (F.endPoint a) d a (hpos d) hdxa hed hda'.symm haxa
  obtain ⟨w, _, hw, hwa, hwb⟩ := hdelete (F.endPoint a)
    (F.delete_endPoint_connected hG a (hpos a)) hcut
  let w' : ↥(K : Set α) := ⟨w, F.center_mem_core hG hw⟩
  have hdistA := F.dist_from_core hG a w' (F.path a).end_mem_support
  have hdistB := F.dist_from_core hG b w' (F.path b).end_mem_support
  rw [← F.geodesic a] at hdistA
  rw [← F.geodesic b] at hdistB
  have heba : F.endPoint b ≠ F.endPoint a := fun heq =>
    hab.ne (congrArg Subtype.val (F.endPoint_injective hG heq)).symm
  have hfar := hwb (F.endPoint b) heba
  have htri := hG.dist_triangle (u := w) (v := (b : α)) (w := (a : α))
  have hba : G.dist (b : α) a = 1 := dist_eq_one_iff_adj.mpr hab.symm
  change G.dist w (F.endPoint a) = G.dist w a + (F.path a).length at hdistA
  change G.dist w (F.endPoint b) = G.dist w b + (F.path b).length at hdistB
  omega
end WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
