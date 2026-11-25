-- Prove2me | solution 1 for SimpleGraph.Bireservoir.IsWinning.exists_pivot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:32:38.550883+00:00
-- url     : https://prove2.me/submissions/dca1067d-0d4e-4159-b026-37e7ad7eabf9

module
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Definitions.Def_RamseyReservoir_Reservoir
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Definitions.Def_RamseyReservoir_Bireservoir
public import Theorems.Thm_SimpleGraph_Bireservoir_redPivot_blue
public import Theorems.Thm_SimpleGraph_Bireservoir_bluePivot_red
public import Theorems.Thm_SimpleGraph_Bireservoir_card_redPivot_red
public import Theorems.Thm_SimpleGraph_Bireservoir_card_bluePivot_blue
public import Theorems.Thm_SimpleGraph_Bireservoir_card_redPivot_pool_add_card_bluePivot_pool
public import Theorems.Thm_SimpleGraph_Reservoir_ofPool_pool
public import Theorems.Thm_SimpleGraph_Reservoir_ofPool_spine
public import Theorems.Thm_SimpleGraph_Reservoir_pivot_pool
public import Theorems.Thm_SimpleGraph_Reservoir_pivot_spine
attribute [local simp] SimpleGraph.Reservoir.ofPool_pool
attribute [local simp] SimpleGraph.Reservoir.ofPool_spine
attribute [local simp] SimpleGraph.Reservoir.pivot_pool
attribute [local simp] SimpleGraph.Reservoir.pivot_spine


attribute [local simp] SimpleGraph.Bireservoir.redPivot_blue
attribute [local simp] SimpleGraph.Bireservoir.bluePivot_red

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
open SimpleGraph.Bireservoir
variable {G}
variable (S : G.Bireservoir)
variable {S}
namespace SimpleGraph.Bireservoir
namespace IsWinning
theorem _root_.solution [DecidableEq V] [DecidableRel G.Adj] {R : ℕ → ℕ → ℕ} {r s : ℕ}
    (hR : IsPascal R) (hS : S.IsWinning R r s) (hr : #S.red < r) (hs : #S.blue < s) :
    ∃ v, ∃ hv : v ∈ S.pool,
      (S.redPivot hv).IsWinning R r s ∨ (S.bluePivot hv).IsWinning R r s := by
  obtain ⟨a, ha⟩ : ∃ a, r - #S.red = a + 1 := ⟨r - #S.red - 1, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, s - #S.blue = b + 1 := ⟨s - #S.blue - 1, by omega⟩
  unfold IsWinning at hS
  rw [ha, hb] at hS
  obtain ⟨hpas, hpos⟩ := hR a b
  obtain ⟨v, hv⟩ := card_pos.mp (hpos.trans_le hS)
  refine ⟨v, hv, ?_⟩
  have hpart := S.card_redPivot_pool_add_card_bluePivot_pool hv
  unfold IsWinning
  rw [card_redPivot_red, redPivot_blue, bluePivot_red, card_bluePivot_blue,
    show r - (#S.red + 1) = a by omega, show s - (#S.blue + 1) = b by omega, hb, ha]
  omega
end IsWinning
end SimpleGraph.Bireservoir
