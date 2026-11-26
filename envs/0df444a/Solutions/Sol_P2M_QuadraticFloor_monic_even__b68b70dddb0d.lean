-- Prove2me | solution 1 for P2M_QuadraticFloor_monic_even__b68b70dddb0d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:03:51.617009+00:00
-- url     : https://prove2.me/submissions/f5e4cd7f-345e-4fa2-a7e1-4c5c045ffb8d

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic
public import Theorems.Thm_QuadraticFloor_eq_of_osum_step
public import Theorems.Thm_QuadraticFloor_osum_mul_left
public import Theorems.Thm_QuadraticFloor_negOnePow_ediv_add_mul
public import Theorems.Thm_QuadraticFloor_odd_of_ne_two


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) (t b : ℤ) :
    floorSum 1 (2 * t) b p = (((b - t ^ 2) / (p : ℤ)).negOnePow : ℤ) -
      2 * osum t (fun m => (((m ^ 2 + (b - t ^ 2)) / (p : ℤ)).negOnePow : ℤ)) := by
  set b' := b - t ^ 2
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  obtain ⟨k, hk⟩ := odd_of_ne_two hp2
  set E : ℤ → ℤ := fun m => (((m ^ 2 + b') / (p : ℤ)).negOnePow : ℤ)
  have hE : ∀ m, E (m + p) = -E m := by
    intro m
    simp only [E]
    rw [show (m + p) ^ 2 + b' = (m ^ 2 + b') + (p : ℤ) * (2 * m + p) by ring,
      negOnePow_ediv_add_mul _ _ hp0, Int.negOnePow_odd (2 * m + p) ⟨m + k, by rw [hk]; push_cast; ring⟩]
    simp
  have hEr : ∀ m : ℕ, 1 ≤ m → m < p → E ((p - m : ℕ) : ℤ) = -E m := by
    intro m h1 h2
    simp only [E]
    rw [Nat.cast_sub h2.le, show ((p : ℤ) - m) ^ 2 + b' = ((m : ℤ) ^ 2 + b') + (p : ℤ) * (p - 2 * m)
      by ring, negOnePow_ediv_add_mul _ _ hp0,
      Int.negOnePow_odd ((p : ℤ) - 2 * m) ⟨(k : ℤ) - m, by rw [hk]; push_cast; ring⟩]
    simp
  -- the full period sums to `E 0`
  have hfull : ∑ m ∈ range p, E m = E 0 := by
    rw [hk, sum_range_succ']
    have hrefl := sum_range_reflect (fun j => E ((j + 1 : ℕ) : ℤ)) (2 * k)
    have hneg : ∀ j ∈ range (2 * k), E ((2 * k - 1 - j + 1 : ℕ) : ℤ) = -E ((j + 1 : ℕ) : ℤ) := by
      intro j hj
      rw [mem_range] at hj
      rw [show 2 * k - 1 - j + 1 = (2 * k + 1) - (j + 1) by omega, ← hk]
      exact hEr (j + 1) (by omega) (by omega)
    rw [sum_congr rfl hneg, sum_neg_distrib] at hrefl
    have : ∑ j ∈ range (2 * k), E ((j + 1 : ℕ) : ℤ) = 0 := by linarith
    simp only [Nat.cast_add, Nat.cast_one] at this ⊢
    rw [this, zero_add]
    simp
  -- the shifted window
  set G : ℤ → ℤ := fun t => ∑ n ∈ range p, E (n + t)
  have hG : ∀ c, G (c + 1) = G c + (-2 * E c) := by
    intro c
    simp only [G]
    have a := sum_range_succ (fun n : ℕ => E (n + c)) p
    have b := sum_range_succ' (fun n : ℕ => E (n + c)) p
    have hpc : E ((p : ℕ) + c) = -E c := by rw [add_comm]; exact hE c
    rw [hpc] at a
    have hb : ∑ n ∈ range p, E (((n + 1 : ℕ) : ℤ) + c) = ∑ n ∈ range p, E (n + (c + 1)) :=
      sum_congr rfl fun n _ => by push_cast; ring_nf
    rw [hb] at b
    simp only [Nat.cast_zero, zero_add] at b
    linarith
  have hGt := eq_of_osum_step hG t
  have hosum : osum t (fun c => -2 * E c) = -2 * osum t E := osum_mul_left t (-2) E
  have hG0 : G 0 = E 0 := by simp only [G, add_zero]; exact hfull
  have hlhs : floorSum 1 (2 * t) b p = G t := by
    unfold floorSum
    simp only [G, E]
    apply sum_congr rfl
    intro n _
    congr 3
    simp only [b']; ring
  rw [hlhs, hGt, hosum, hG0]
  simp only [E, zero_pow two_ne_zero, zero_add]
  ring
end QuadraticFloor
