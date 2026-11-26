-- Prove2me | solution 1 for QuarterSumLadder.card_quarter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:06:47.253393+00:00
-- url     : https://prove2.me/submissions/74836b03-c3ca-4a54-811d-29e7c7edb0e8

module
public import Definitions.Def_QuarterSumLadder_Classes
public import Definitions.Def_QuarterSumLadder_Counts
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_gi_re
public import Theorems.Thm_QuarterSumLadder_mod_eight_aux
public import Theorems.Thm_QuarterSumLadder_val_pos_of_ne_zero
attribute [local simp] QuarterSumLadder.gi_im
attribute [local simp] QuarterSumLadder.gi_re



set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuarterSumLadder
theorem _root_.solution (hp8 : p % 8 = 1) :
    (univ.filter fun x : ZMod p => x ≠ 0 ∧ 4 * x.val < p).card = Q p := by
  have hpq := mod_eight_aux hp8
  rw [show Q p = (Icc 1 (Q p)).card by simp]
  refine card_nbij' (fun x => x.val) (fun n => (n : ZMod p)) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, coe_Icc, Set.mem_Icc] at hx ⊢
    have := val_pos_of_ne_zero hx.1
    omega
  · intro n hn
    simp only [coe_Icc, Set.mem_Icc, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hn ⊢
    have hlt : n < p := by omega
    rw [ZMod.val_natCast_of_lt hlt]
    refine ⟨?_, by omega⟩
    rw [Ne, ← ZMod.val_eq_zero, ZMod.val_natCast_of_lt hlt]; omega
  · intro x _; exact ZMod.natCast_zmod_val x
  · intro n hn
    simp only [coe_Icc, Set.mem_Icc] at hn
    exact ZMod.val_natCast_of_lt (by omega)
end QuarterSumLadder
