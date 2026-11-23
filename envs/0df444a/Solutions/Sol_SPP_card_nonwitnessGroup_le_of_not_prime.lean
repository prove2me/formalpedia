-- Prove2me | solution 1 for SPP.card_nonwitnessGroup_le_of_not_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:24:50.4902+00:00
-- url     : https://prove2.me/submissions/68279810-d677-4dfd-afad-22af67d2d23f

import Mathlib
import Definitions.Def_MillerRabin_Mathlib_Data_Fintype_Units
import Definitions.Def_MillerRabin_Mathlib_Algebra_Group_Subgroup_Lattice
import Definitions.Def_MillerRabin_FermatProbable
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Val2
import Definitions.Def_MillerRabin_StrongProbable
import Theorems.Thm_SPP_card_nonwitnessGroup_of_prime_pow
import Theorems.Thm_SPP_nonwitnessGroup_lt_lt_of_not_isPrimePow
import Theorems.Thm_Subgroup_two_mul_card_le_card_of_lt


set_option autoImplicit false
open Nat
open SPP
open Subgroup
variable {n : ℕ}
namespace SPP
theorem _root_.solution [Fact (1 < n)]
    (ho : Odd n) (hnp : ¬n.Prime) (h9 : n ≠ 9) :
    4 * Nat.card (nonwitnessGroup n) ≤ φ n := by
  by_cases hpp : IsPrimePow n
  · have ⟨p, m, pp, hm, h⟩ := hpp
    obtain rfl := h
    replace pp := pp.nat_prime
    have : Fact p.Prime := ⟨pp⟩
    have hp : 2 < p := lt_of_le_of_ne pp.two_le fun hp ↦ ho.not_two_dvd_nat ⟨p ^ m.pred,
      by rw [← hp, mul_comm, ← Nat.pow_succ, m.succ_pred hm.ne']⟩
    calc
    _ = 4 * (p - 1) := by rw [card_nonwitnessGroup_of_prime_pow hm hp]
    _ ≤ φ (p ^ m) := by
      rw [totient_prime_pow pp hm]
      apply Nat.mul_le_mul_right
      replace hm := lt_of_le_of_ne hm.nat_succ_le fun pm ↦ hnp (by rwa [← pm, pow_one])
      rcases hm.nat_succ_le.eq_or_lt with rfl | hm
      · rw [pow_one]
        by_contra hp
        interval_cases p
        exact h9 rfl
      apply (pow_le_pow_left' pp.two_le 2).trans
      exact pow_le_pow_right' pp.pos (le_pred_of_lt hm)
  · have ⟨K, hK₁, hK₂⟩ := nonwitnessGroup_lt_lt_of_not_isPrimePow ho hpp
    classical
    calc
      _ = 2 * (2 * Nat.card (nonwitnessGroup n)) := by rw [← mul_assoc]; rfl
      _ ≤ 2 * Nat.card K := Nat.mul_le_mul_left 2 (two_mul_card_le_card_of_lt hK₁)
      _ ≤ Nat.card (⊤ : Subgroup _) := two_mul_card_le_card_of_lt hK₂
      _ = Fintype.card (ZMod n)ˣ := card_top.trans Nat.card_eq_fintype_card
      _ = φ n := ZMod.card_units_eq_totient n
end SPP
