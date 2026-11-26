-- Prove2me | solution 1 for QuarterSumLadder.card_fiber_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:02:18.342872+00:00
-- url     : https://prove2.me/submissions/bef930a4-a876-4cd2-8db5-498a8451ea6b

module
public import Definitions.Def_QuarterSumLadder_Prelim
public import Definitions.Def_QuarterSumLadder_Classes
public import Theorems.Thm_QuarterSumLadder_mem_fiber
public import Theorems.Thm_QuarterSumLadder_exists_char_eq

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
omit hp8
namespace QuarterSumLadder
theorem _root_.solution {z : GaussianInt} (hz : FourVal z) :
    (fiber χ z).card = (fiber χ 1).card := by
  obtain ⟨c, hc0, hc⟩ := exists_char_eq hχ hz
  refine card_nbij' (fun x => c⁻¹ * x) (fun x => c * x) ?_ ?_ ?_ ?_
  · intro x hx
    rw [mem_coe, mem_fiber] at *
    have : χ c * χ c⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hc0, map_one]
    rw [map_mul, hx, ← hc, mul_comm]; exact this
  · intro x hx; rw [mem_coe, mem_fiber] at *; rw [map_mul, hx, hc, mul_one]
  · intro x _; show c * (c⁻¹ * x) = x; rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  · intro x _; show c⁻¹ * (c * x) = x; rw [← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
end QuarterSumLadder
