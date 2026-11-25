-- Prove2me | solution 1 for SimpleGraph.IsClique.exists_isNClique_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:30:36.702526+00:00
-- url     : https://prove2.me/submissions/67463f3f-5542-4e59-bc5d-09664562ec25

module
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Definitions.Def_RamseyReservoir_Reservoir
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Definitions.Def_RamseyReservoir_Bireservoir
public import Theorems.Thm_SimpleGraph_Bireservoir_ofPool_red
public import Theorems.Thm_SimpleGraph_Bireservoir_ofPool_blue
public import Theorems.Thm_SimpleGraph_Bireservoir_ofPool_pool
public import Theorems.Thm_SimpleGraph_Bireservoir_toRed_spine
public import Theorems.Thm_SimpleGraph_Bireservoir_toRed_pool
public import Theorems.Thm_SimpleGraph_Bireservoir_toBlue_spine
public import Theorems.Thm_SimpleGraph_Bireservoir_toBlue_pool
public import Theorems.Thm_SimpleGraph_Bireservoir_redPivot_red
public import Theorems.Thm_SimpleGraph_Bireservoir_redPivot_blue
public import Theorems.Thm_SimpleGraph_Bireservoir_redPivot_pool
public import Theorems.Thm_SimpleGraph_Bireservoir_bluePivot_red
public import Theorems.Thm_SimpleGraph_Bireservoir_bluePivot_blue
public import Theorems.Thm_SimpleGraph_Bireservoir_bluePivot_pool
public import Theorems.Thm_SimpleGraph_Reservoir_ofPool_pool
public import Theorems.Thm_SimpleGraph_Reservoir_ofPool_spine
public import Theorems.Thm_SimpleGraph_Reservoir_pivot_pool
public import Theorems.Thm_SimpleGraph_Reservoir_pivot_spine
attribute [local simp] SimpleGraph.Reservoir.ofPool_pool
attribute [local simp] SimpleGraph.Reservoir.ofPool_spine
attribute [local simp] SimpleGraph.Reservoir.pivot_pool
attribute [local simp] SimpleGraph.Reservoir.pivot_spine


attribute [local simp] SimpleGraph.Bireservoir.ofPool_red
attribute [local simp] SimpleGraph.Bireservoir.ofPool_blue
attribute [local simp] SimpleGraph.Bireservoir.ofPool_pool
attribute [local simp] SimpleGraph.Bireservoir.toRed_spine
attribute [local simp] SimpleGraph.Bireservoir.toRed_pool
attribute [local simp] SimpleGraph.Bireservoir.toBlue_spine
attribute [local simp] SimpleGraph.Bireservoir.toBlue_pool
attribute [local simp] SimpleGraph.Bireservoir.redPivot_red
attribute [local simp] SimpleGraph.Bireservoir.redPivot_blue
attribute [local simp] SimpleGraph.Bireservoir.redPivot_pool
attribute [local simp] SimpleGraph.Bireservoir.bluePivot_red
attribute [local simp] SimpleGraph.Bireservoir.bluePivot_blue
attribute [local simp] SimpleGraph.Bireservoir.bluePivot_pool

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
open SimpleGraph.Bireservoir
variable {G}
variable (S : G.Bireservoir)
namespace SimpleGraph.Bireservoir
namespace _root_.SimpleGraph.IsClique
theorem _root_.solution {H : SimpleGraph V} {s : Finset V}
    (hs : H.IsClique (s : Set V)) {r : ℕ} (hr : r ≤ #s) : ∃ t ⊆ s, H.IsNClique r t := by
  obtain ⟨t, hts, ht⟩ := exists_subset_card_eq hr
  exact ⟨t, hts, ⟨hs.subset (by simpa using hts), ht⟩⟩
end _root_.SimpleGraph.IsClique
end SimpleGraph.Bireservoir
