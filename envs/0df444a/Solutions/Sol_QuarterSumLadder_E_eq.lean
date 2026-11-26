-- Prove2me | solution 1 for QuarterSumLadder.E_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:04:19.809738+00:00
-- url     : https://prove2.me/submissions/5cb1f604-c3cf-463e-b107-cc35d137b430

module
public import Definitions.Def_QuarterSumLadder_Prelim
public import Definitions.Def_QuarterSumLadder_Classes
public import Theorems.Thm_QuarterSumLadder_mem_fiber
public import Theorems.Thm_QuarterSumLadder_char_two_sq
public import Theorems.Thm_QuarterSumLadder_val_half_of_even
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_gi_re
public import Theorems.Thm_QuarterSumLadder_val_two_mul_of_lt
attribute [local simp] QuarterSumLadder.gi_im
attribute [local simp] QuarterSumLadder.gi_re



set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
namespace QuarterSumLadder
theorem _root_.solution (z : GaussianInt) :
    E χ z = ((fiber χ (χ 2 * z)).filter fun x => 2 * x.val < p ∧ Odd x.val).card := by
  have hsq := char_two_sq hp8 hχ
  unfold E
  refine card_nbij' (fun y => ((y.val / 2 : ℕ) : ZMod p)) (fun x => 2 * x) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [coe_filter, Set.mem_ofPred_eq, mem_fiber] at hy ⊢
    obtain ⟨hyz, hy4⟩ := hy
    have hye : Even y.val := Nat.even_iff.2 (by omega)
    have hlt : y.val / 2 < p := by have := ZMod.val_lt y; omega
    rw [ZMod.val_natCast_of_lt hlt]
    have h2 : χ 2 * χ ((y.val / 2 : ℕ) : ZMod p) = z := by
      rw [← map_mul, val_half_of_even hye, hyz]
    refine ⟨by linear_combination (χ 2) * h2 - χ ((y.val / 2 : ℕ) : ZMod p) * hsq,
      by have := ZMod.val_lt y; omega, Nat.odd_iff.2 (by omega)⟩
  · intro x hx
    simp only [coe_filter, Set.mem_ofPred_eq, mem_fiber] at hx ⊢
    have hv := val_two_mul_of_lt hx.2.1
    rw [hv, map_mul, hx.1]
    refine ⟨by linear_combination z * hsq, ?_⟩
    have := Nat.odd_iff.1 hx.2.2; omega
  · intro y hy
    simp only [coe_filter, Set.mem_ofPred_eq] at hy
    obtain ⟨_, h4⟩ := hy
    exact val_half_of_even (Nat.even_iff.2 (by omega))
  · intro x hx
    simp only [coe_filter, Set.mem_ofPred_eq] at hx
    have hv := val_two_mul_of_lt hx.2.1
    show (((2 * x).val / 2 : ℕ) : ZMod p) = x
    rw [hv, show 2 * x.val / 2 = x.val by omega, ZMod.natCast_zmod_val]
end QuarterSumLadder
