-- Prove2me | solution 1 for QuarterSumLadder.p_dvd_U
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:08:35.79309+00:00
-- url     : https://prove2.me/submissions/88732de7-ab10-4425-aff5-a96c0cdcac97

module
public import Definitions.Def_QuarterSumLadder_Counts
public import Definitions.Def_QuarterSumLadder_WeightTwo
public import Theorems.Thm_QuarterSumLadder_exists_generator
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_gi_re
public import Theorems.Thm_QuarterSumLadder_mem_fiber
public import Theorems.Thm_QuarterSumLadder_quartic_apply_generator
public import Theorems.Thm_QuarterSumLadder_seventeen_le
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
theorem _root_.solution {z : GaussianInt} : (p : ℤ) ∣ U χ z := by
  have h17 := seventeen_le hp8
  obtain ⟨g, hgo, hg⟩ := exists_generator (p := p)
  set u : ZMod p := (g : ZMod p) ^ 4 with hu
  have hu0 : u ≠ 0 := pow_ne_zero _ g.ne_zero
  have hχu : χ u = 1 := by
    rw [hu, map_pow]
    rcases quartic_apply_generator χ hχ hg with h | h <;> rw [h] <;> decide
  have hu2 : u ^ 2 ≠ 1 := by
    intro h
    rw [hu, ← pow_mul, ← Units.val_pow_eq_pow_val, Units.val_eq_one] at h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hgo] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hS : ((U χ z : ℤ) : ZMod p) = ∑ x ∈ fiber χ z, x ^ 2 := by
    unfold U; push_cast; simp
  rw [hS]
  have hperm : ∑ x ∈ fiber χ z, x ^ 2 = ∑ x ∈ fiber χ z, (u * x) ^ 2 := by
    refine sum_nbij' (fun x => u⁻¹ * x) (fun x => u * x) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rw [mem_fiber] at *
      have : χ u⁻¹ = 1 := by
        have h := (map_mul χ u u⁻¹).symm
        rw [mul_inv_cancel₀ hu0, map_one, hχu, one_mul] at h; exact h
      rw [map_mul, this, one_mul, hx]
    · intro x hx; rw [mem_fiber] at *; rw [map_mul, hχu, one_mul, hx]
    · intro x _; show u * (u⁻¹ * x) = x; rw [← mul_assoc, mul_inv_cancel₀ hu0, one_mul]
    · intro x _; show u⁻¹ * (u * x) = x; rw [← mul_assoc, inv_mul_cancel₀ hu0, one_mul]
    · intro x _; show x ^ 2 = (u * (u⁻¹ * x)) ^ 2; rw [← mul_assoc, mul_inv_cancel₀ hu0, one_mul]
  have : (u ^ 2 - 1) * ∑ x ∈ fiber χ z, x ^ 2 = 0 := by
    have h2 : ∑ x ∈ fiber χ z, (u * x) ^ 2 = u ^ 2 * ∑ x ∈ fiber χ z, x ^ 2 := by
      rw [mul_sum]; exact sum_congr rfl fun x _ => by ring
    rw [sub_mul, one_mul, ← h2, ← hperm, sub_self]
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h) hu2
  · exact h
end QuarterSumLadder
