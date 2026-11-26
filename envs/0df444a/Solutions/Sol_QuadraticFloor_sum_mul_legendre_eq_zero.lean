-- Prove2me | solution 1 for QuadraticFloor.sum_mul_legendre_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:56:41.52188+00:00
-- url     : https://prove2.me/submissions/9a187766-c976-4842-98cc-c1405ec95f6f

module
public import Definitions.Def_QuadraticFloor_Eta
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Theorems.Thm_QuadraticFloor_sum_Icc_one
public import Theorems.Thm_QuadraticFloor_sum_range_mul
public import Theorems.Thm_QuadraticFloor_sum_quadraticChar_affine
public import Theorems.Thm_QuadraticFloor_sum_range_eq_sum_zmod


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) (g : ℕ → ℂ) {m : ℕ} (hm : ¬ p ∣ m)
    (hg : ∀ x, g (x + m) = g x) :
    ∑ x ∈ Icc 1 (m * p), g x * (legendreSym p x : ℂ) = 0 := by
  have hg' : ∀ y k, g (m * k + y) = g y := by
    intro y k
    induction k with
    | zero => simp
    | succ k ih => rw [show m * (k + 1) + y = (m * k + y) + m by ring, hg, ih]
  have hL0 : legendreSym p ((0 : ℕ) : ℤ) = 0 := by simp
  have hLmp : legendreSym p ((m * p : ℕ) : ℤ) = 0 := by
    rw [(legendreSym.eq_zero_iff p _).2]
    push_cast; simp
  -- pass from `[1, mp]` to `[0, mp)`
  have hIcc : ∑ x ∈ Icc 1 (m * p), g x * (legendreSym p x : ℂ) =
      ∑ x ∈ range (m * p), g x * (legendreSym p x : ℂ) := by
    rw [sum_Icc_one]
    have a := sum_range_succ' (fun x => g x * (legendreSym p x : ℂ)) (m * p)
    have b := sum_range_succ (fun x => g x * (legendreSym p x : ℂ)) (m * p)
    simp only [hL0, hLmp, Int.cast_zero, mul_zero, add_zero] at a b
    rw [← a, b]
  rw [hIcc, sum_range_mul, sum_comm]
  apply sum_eq_zero
  intro y _
  simp_rw [hg' y]
  rw [← mul_sum]
  have hm' : ((m : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hm
  have hsum : ∑ k ∈ range p, legendreSym p ((m * k + y : ℕ) : ℤ) = 0 := by
    have := sum_quadraticChar_affine hp2 hm' (y : ZMod p)
    rw [← sum_range_eq_sum_zmod (fun z : ZMod p => quadraticChar (ZMod p) ((y : ZMod p) + m * z))]
      at this
    rw [← this]
    apply sum_congr rfl
    intro k _
    simp only [legendreSym]
    push_cast; ring_nf
  have : ∑ k ∈ range p, (legendreSym p ((m * k + y : ℕ) : ℤ) : ℂ) = 0 := by
    exact_mod_cast hsum
  rw [this, mul_zero]
end QuadraticFloor
