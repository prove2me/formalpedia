-- Prove2me | solution 1 for QuarterSumLadder.card_two_mod_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:09:26.480528+00:00
-- url     : https://prove2.me/submissions/2edf0fc9-85b5-4210-916b-d5b151bca244

module
public import Definitions.Def_QuarterSumLadder_Counts
public import Definitions.Def_QuarterSumLadder_WeightTwo
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_gi_re
public import Theorems.Thm_QuarterSumLadder_mod_eight_aux
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
    (univ.filter fun x : ZMod p => x.val % 4 = 2).card = Q p := by
  have hpq := mod_eight_aux hp8
  rw [show Q p = (range (Q p)).card by simp]
  refine card_nbij' (fun x => x.val / 4) (fun k => ((4 * k + 2 : ℕ) : ZMod p)) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, coe_range, Set.mem_Iio] at hx ⊢
    have := ZMod.val_lt x; omega
  · intro k hk
    simp only [coe_range, Set.mem_Iio, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hk ⊢
    rw [ZMod.val_natCast_of_lt (by omega)]; omega
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
    have : 4 * (x.val / 4) + 2 = x.val := by omega
    show ((4 * (x.val / 4) + 2 : ℕ) : ZMod p) = x
    rw [this, ZMod.natCast_zmod_val]
  · intro k hk
    simp only [coe_range, Set.mem_Iio] at hk
    show ((4 * k + 2 : ℕ) : ZMod p).val / 4 = k
    rw [ZMod.val_natCast_of_lt (by omega)]; omega
end QuarterSumLadder
