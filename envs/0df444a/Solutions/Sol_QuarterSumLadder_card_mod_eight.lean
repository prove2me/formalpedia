-- Prove2me | solution 1 for QuarterSumLadder.card_mod_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:12:29.548463+00:00
-- url     : https://prove2.me/submissions/7ba27664-9719-46b7-b782-bab394836281

module
public import Definitions.Def_QuarterSumLadder_Ladder
public import Definitions.Def_QuarterSumLadder_Boundary
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_gi_re
attribute [local simp] QuarterSumLadder.gi_im
attribute [local simp] QuarterSumLadder.gi_re



set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuarterSumLadder
theorem _root_.solution (hp8 : p % 8 = 1) {r : ℕ} (hr1 : 1 ≤ r) (hr7 : r ≤ 7) :
    (univ.filter fun x : ZMod p => x.val % 8 = r).card = (p - 1) / 8 := by
  rw [show (p - 1) / 8 = (range ((p - 1) / 8)).card by simp]
  refine card_nbij' (fun x => x.val / 8) (fun k => ((8 * k + r : ℕ) : ZMod p)) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, coe_range, Set.mem_Iio] at hx ⊢
    have := ZMod.val_lt x; omega
  · intro k hk
    simp only [coe_range, Set.mem_Iio, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hk ⊢
    rw [ZMod.val_natCast_of_lt (by omega)]; omega
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
    have : 8 * (x.val / 8) + r = x.val := by omega
    show ((8 * (x.val / 8) + r : ℕ) : ZMod p) = x
    rw [this, ZMod.natCast_zmod_val]
  · intro k hk
    simp only [coe_range, Set.mem_Iio] at hk
    show ((8 * k + r : ℕ) : ZMod p).val / 8 = k
    rw [ZMod.val_natCast_of_lt (by omega)]; omega
end QuarterSumLadder
