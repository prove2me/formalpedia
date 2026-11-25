-- Prove2me | solution 1 for SimpleGraph.Bireservoir.card_redPivot_pool_add_card_bluePivot_pool
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:30:34.696883+00:00
-- url     : https://prove2.me/submissions/1ed6a1d0-e920-49c1-9464-882483ddae74

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
public import Theorems.Thm_SimpleGraph_RamseyBound_symm
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
variable [DecidableEq V] [DecidableRel G.Adj] {v : V} (hv : v ∈ S.pool)
namespace SimpleGraph.Bireservoir
theorem _root_.solution :
    #(S.redPivot hv).pool + #(S.bluePivot hv).pool + 1 = #S.pool := by
  have h := card_filter_add_card_filter_not (s := S.pool) (G.Adj v)
  have hblue : {w ∈ S.pool | ¬G.Adj v w} = insert v {w ∈ S.pool | Gᶜ.Adj v w} := by
    ext w
    by_cases hw : w = v
    · subst hw; simp [hv]
    · simp [hw, compl_adj, Ne.symm hw]
  rw [hblue, card_insert_of_notMem (by simp)] at h
  simp only [redPivot_pool, bluePivot_pool]
  omega
end SimpleGraph.Bireservoir
