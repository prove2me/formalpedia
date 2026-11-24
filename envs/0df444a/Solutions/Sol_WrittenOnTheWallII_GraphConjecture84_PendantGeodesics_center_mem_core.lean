-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.center_mem_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:30:09.95995+00:00
-- url     : https://prove2.me/submissions/d4842184-54bb-4b9d-8150-4b9666b57893

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_dist_add_dist_eq_of_mem_geodesic
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_dist_eq_add_of_not_reachable_compl
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_tail_separated

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
open WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
variable {G : SimpleGraph α} {K : Finset α} (F : PendantGeodesics G K)
include F
namespace WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
theorem _root_.solution (hG : G.Connected) {v : α} (hv : G.eccent v = G.radius) : v ∈ K := by
  haveI : Nonempty α := hG.nonempty
  by_contra hvK
  obtain ⟨c, hvc⟩ := F.cover v
  have hvcne : v ≠ (c : α) := fun heq => hvK (heq.symm ▸ c.property)
  have hvdist : 0 < G.dist (c : α) v := by
    have hne : G.dist (c : α) v ≠ 0 := fun heq => hvcne (hG.dist_eq_zero_iff.mp heq).symm
    omega
  have hsum := dist_add_dist_eq_of_mem_geodesic (F.path c) (F.geodesic c) hvc
  have hpos : 0 < (F.path c).length := by rw [F.geodesic c]; omega
  obtain ⟨a, ha⟩ := F.depth_gap c hpos
  obtain ⟨f, hf⟩ := G.exists_edist_eq_eccent_of_finite (c : α)
  have hmax : G.dist (c : α) a ≤ G.dist c f :=
    ENat.toNat_le_toNat (hf ▸ G.edist_le_eccent)
      (edist_ne_top_iff_reachable.mpr (hG c f))
  have hfoff : f ∉ (F.path c).support := by
    intro hfc
    have hf_sum := dist_add_dist_eq_of_mem_geodesic (F.path c) (F.geodesic c) hfc
    rw [← F.geodesic c] at hf_sum
    omega
  have hfc : f ≠ (c : α) := fun heq => hfoff (heq ▸ (F.path c).start_mem_support)
  have hdist := dist_eq_add_of_not_reachable_compl hG hvcne hfc
    (F.tail_separated c hvc hvcne hfoff)
  have hrad : G.radius.toNat ≤ G.dist (c : α) f :=
    ENat.toNat_le_toNat (hf ▸ G.radius_le_eccent)
      (edist_ne_top_iff_reachable.mpr (hG c f))
  have hvf : G.dist v f ≤ G.radius.toNat :=
    ENat.toNat_le_toNat (hv ▸ G.edist_le_eccent)
      (G.radius_ne_top_iff.mpr hG)
  rw [G.dist_comm (u := v) (v := (c : α))] at hdist
  omega
end WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
