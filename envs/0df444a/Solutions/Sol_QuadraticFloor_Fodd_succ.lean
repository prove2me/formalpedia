-- Prove2me | solution 1 for QuadraticFloor.Fodd_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:02:37.415693+00:00
-- url     : https://prove2.me/submissions/a59a2042-a532-4c31-8664-344d43f9c417

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic
public import Theorems.Thm_QuadraticFloor_ediv_succ
public import Theorems.Thm_QuadraticFloor_card_quadratic_eq
public import Theorems.Thm_QuadraticFloor_ite_of_neg
public import Theorems.Thm_QuadraticFloor_ite_of_pos
public import Theorems.Thm_QuadraticFloor_negOnePow_ediv
public import Theorems.Thm_QuadraticFloor_odd_of_ne_two
public import Theorems.Thm_QuadraticFloor_sum_range_eq_sum_zmod


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) (c : ℤ) :
    Fodd p (c + 1) = Fodd p c + (-2 * (c.negOnePow : ℤ) * (1 + legendreSym p (-4 * c - 3))) := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  unfold Fodd floorSum
  -- termwise change
  have hterm : ∀ n : ℕ, (((1 * (n : ℤ) ^ 2 + 1 * n + (c + 1)) / (p : ℤ)).negOnePow : ℤ) =
      (((1 * (n : ℤ) ^ 2 + 1 * n + c) / (p : ℤ)).negOnePow : ℤ) +
        -2 * (c.negOnePow : ℤ) * (if ((n : ZMod p) ^ 2 + n + (c + 1 : ZMod p)) = 0 then 1 else 0) := by
    intro n
    set v := 1 * (n : ℤ) ^ 2 + 1 * n + c
    rw [show 1 * (n : ℤ) ^ 2 + 1 * n + (c + 1) = v + 1 by ring, ediv_succ hp0]
    have hz : ((n : ZMod p) ^ 2 + n + (c + 1 : ZMod p)) = 0 ↔ (p : ℤ) ∣ v + 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; simp only [v]; push_cast; ring_nf
    by_cases hd : (p : ℤ) ∣ v + 1
    · rw [ite_of_pos hd, ite_of_pos (hz.2 hd), Int.negOnePow_succ, Units.val_neg]
      -- the old sign is `(-1)^c`
      have hvc : Even (v - c) := by
        simp only [v]
        rw [show 1 * (n : ℤ) ^ 2 + 1 * n + c - c = n * (n + 1) by ring]
        exact Int.even_mul_succ_self n
      rw [negOnePow_ediv hp2 v c hvc]
      have hmod : v % (p : ℤ) = p - 1 := by
        obtain ⟨k, hk⟩ := hd
        rw [show v = (p - 1) + (p : ℤ) * (k - 1) by linarith, Int.add_mul_emod_self_left,
          Int.emod_eq_of_lt (by omega) (by omega)]
      rw [hmod, Int.negOnePow_even ((p : ℤ) - 1) (by
        obtain ⟨m, hm⟩ := odd_of_ne_two hp2
        exact ⟨m, by rw [hm]; push_cast; ring⟩)]
      simp; ring
    · rw [ite_of_neg hd, ite_of_neg (fun h => hd (hz.1 h)), add_zero]; ring
  rw [sum_congr rfl fun n _ => hterm n, sum_add_distrib, ← mul_sum]
  congr 1
  rw [sum_range_eq_sum_zmod (fun x : ZMod p => if x ^ 2 + x + (c + 1 : ZMod p) = 0 then (1 : ℤ) else 0),
    sum_boole]
  have hcard := card_quadratic_eq hp2 (A := 1) (B := 1) (C := (c + 1 : ZMod p)) one_ne_zero 0
  simp only [one_mul, mul_zero, add_zero] at hcard
  rw [hcard]
  simp only [legendreSym]
  push_cast
  ring_nf
end QuadraticFloor
