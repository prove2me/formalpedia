-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.delete_zero_connected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:34:32.061801+00:00
-- url     : https://prove2.me/submissions/7a4d210e-266d-45ef-b926-1c2bdcbc29a6

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_dist_add_dist_eq_of_mem_geodesic
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_exists_walk_in_core_avoiding
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_exists_two_adj_of_connected_deletions

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
theorem _root_.solution (hG : G.Connected) (hcard : 3 ≤ K.card)
    (hK : (G.induce (K : Set α)).Connected)
    (hdel : ∀ x : ↥(K : Set α),
      ((G.induce (K : Set α)).induce ({x}ᶜ : Set ↥(K : Set α))).Connected)
    (a : ↥(K : Set α)) (ha : (F.path a).length = 0) :
    (G.induce ({(a : α)}ᶜ : Set α)).Connected := by
  classical
  obtain ⟨u, _, hau, _, _⟩ := exists_two_adj_of_connected_deletions
    (G := G.induce (K : Set α)) (by simpa using hcard) hK hdel a
  have hua : (u : α) ≠ (a : α) := (show G.Adj a u from hau).ne.symm
  let u' : ↥({(a : α)}ᶜ : Set α) := ⟨u, by simpa using hua⟩
  rw [connected_iff_exists_forall_reachable]
  refine ⟨u', ?_⟩
  intro z
  obtain ⟨d, hzd⟩ := F.cover z
  have hda : (d : α) ≠ (a : α) := by
    intro hda
    have hdeq : d = a := Subtype.ext hda
    subst d
    have hsum := dist_add_dist_eq_of_mem_geodesic (F.path a) (F.geodesic a) hzd
    rw [← F.geodesic a, ha] at hsum
    have haz : G.dist (a : α) z = 0 := by omega
    exact z.property (hG.dist_eq_zero_iff.mp haz).symm
  obtain ⟨p, _, hpa⟩ := exists_walk_in_core_avoiding K hK hdel a
    u.property d.property hua hda
  let q := (F.path d).takeUntil (z : α) hzd
  have hqa : (a : α) ∉ q.support := by
    intro haq
    have had := F.core_inter d a
      ((F.path d).support_takeUntil_subset hzd haq) a.property
    exact hda had.symm
  let r := p.append q
  have hra : (a : α) ∉ r.support := by
    intro har
    simp only [r, Walk.support_append, List.mem_append] at har
    exact har.elim hpa (fun har => hqa (List.mem_of_mem_tail har))
  exact ⟨r.induce ({(a : α)}ᶜ : Set α) (by
    intro w hw
    exact show w ≠ (a : α) from fun heq => hra (heq ▸ hw))⟩
end WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
