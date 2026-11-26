-- Prove2me | solution 1 for P2M_FixedOrderFactor_sum_char_pow_eq_one_of_pow__9a04af0fa11c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:03:27.205954+00:00
-- url     : https://prove2.me/submissions/36d3bf44-830c-482d-8d3f-6c2fdc715290

module
public import Mathlib
public import Definitions.Def_FixedOrderFactor_Characters
public import Theorems.Thm_P2M_FixedOrderFactor_sum_char_pow_eq_one__fb05deb8e53f

set_option autoImplicit true
@[expose] public section
public section
open Finset
open FixedOrderFactor
variable (p : ℕ) [Fact p.Prime]
open Classical
namespace FixedOrderFactor
theorem _root_.solution {r : ℕ} (hr : r ∣ p - 1) {m n d a b : ℕ}
    (hm : m = d * a ^ r) (hn : n = d * b ^ r) (hpm : ¬ p ∣ m) (hpn : ¬ p ∣ n) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (fun χ => χ ^ r = 1),
        χ m * starRingEnd ℂ (χ n) = r := by
  have hr0 : r ≠ 0 := by
    rintro rfl
    have := (Fact.out : p.Prime).two_le
    rw [zero_dvd_iff] at hr; omega
  have hn0 : (n : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  rw [sum_char_pow_eq_one' p hr _ _ hn0, if_pos]
  have hd : (d : ZMod p) ≠ 0 := by
    intro h; apply hpn; rw [← ZMod.natCast_eq_zero_iff, hn]; push_cast; rw [h, zero_mul]
  have hb : (b : ZMod p) ≠ 0 := by
    intro h; apply hpn; rw [← ZMod.natCast_eq_zero_iff, hn]; push_cast; rw [h]
    simp [zero_pow hr0]
  have ha : (a : ZMod p) ≠ 0 := by
    intro h; apply hpm; rw [← ZMod.natCast_eq_zero_iff, hm]; push_cast; rw [h]
    simp [zero_pow hr0]
  refine ⟨(a : ZMod p) * (b : ZMod p)⁻¹, mul_ne_zero ha (inv_ne_zero hb), ?_⟩
  rw [hm, hn]; push_cast
  rw [mul_pow, inv_pow, mul_comm (d : ZMod p)]
  have hbr : ((b : ZMod p) ^ r)⁻¹ * (b : ZMod p) ^ r = 1 := inv_mul_cancel₀ (pow_ne_zero _ hb)
  rw [mul_assoc ((a : ZMod p) ^ r), ← mul_assoc ((b : ZMod p) ^ r)⁻¹, mul_comm _ (d : ZMod p),
    mul_right_comm ((b : ZMod p) ^ r)⁻¹, hbr, one_mul, mul_comm]
end FixedOrderFactor
