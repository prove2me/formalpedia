-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.U3.exists_teichChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:04:54.91486+00:00
-- url     : https://prove2.me/submissions/dc575b72-af03-441b-b8f0-314b8e6f2b4d

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_v_natCast_le_one
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_v_intCast_lt_one_of_dvd
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_v_intCast_eq_one
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_v_le_one_of_pow_eq
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_teich_unique
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_exists_teich

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.U3
variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.U3
theorem _root_.solution [IsAlgClosed C] (hv : v.Integers R) (hpv : v (p : C) < 1) :
    ∃ ω : ZMod p → C, (∀ a, ω a ^ p = ω a) ∧ (∀ a, v (ω a - (a.val : C)) < 1) ∧
      ω 0 = 0 ∧ ω 1 = 1 ∧ (∀ a b, ω (a * b) = ω a * ω b) ∧
      (∀ a b, a ≠ b → v (ω a - ω b) = 1) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  choose ω hω1 hω2 using fun a : ZMod p => exists_teich hv hpv (p := p) a.val
  have hω1' : ∀ a, v (ω a) ≤ 1 := fun a => v_le_one_of_pow_eq (hω1 a)
  refine ⟨ω, hω1, hω2, ?_, ?_, ?_, ?_⟩
  · refine teich_unique hv hpv (hω1 0) (zero_pow hp.out.ne_zero) ?_
    simpa using hω2 0
  · refine teich_unique hv hpv (hω1 1) (one_pow _) ?_
    have := hω2 1
    rwa [ZMod.val_one, Nat.cast_one] at this
  · intro a b
    refine teich_unique hv hpv (hω1 (a * b)) (by rw [mul_pow, hω1, hω1]) ?_
    have e4 : v (((a * b).val : C) - (a.val : C) * (b.val : C)) < 1 := by
      have hd : (p : ℤ) ∣ (((a * b).val : ℤ) - (a.val : ℤ) * (b.val : ℤ)) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        simp [ZMod.natCast_zmod_val]
      have := v_intCast_lt_one_of_dvd hv hpv hd
      push_cast at this
      exact this
    have e5 : v ((a.val : C) * (b.val : C) - ω a * ω b) < 1 := by
      have hx : (a.val : C) * b.val - ω a * ω b = -((ω a - a.val) * b.val + ω a * (ω b - b.val)) := by ring
      rw [hx, Valuation.map_neg]
      apply v.map_add_lt
      · rw [map_mul]
        calc _ ≤ v (ω a - a.val) * 1 := mul_le_mul_of_nonneg_left (v_natCast_le_one hv _) zero_le'
          _ < 1 := by rw [mul_one]; exact hω2 a
      · rw [map_mul]
        calc _ ≤ 1 * v (ω b - b.val) := mul_le_mul_of_nonneg_right (hω1' a) zero_le'
          _ < 1 := by rw [one_mul]; exact hω2 b
    have hx : ω (a * b) - ω a * ω b = (ω (a * b) - ((a * b).val : C)) +
        ((((a * b).val : C) - (a.val : C) * (b.val : C)) + ((a.val : C) * (b.val : C) - ω a * ω b)) := by ring
    rw [hx]
    exact v.map_add_lt (hω2 (a * b)) (v.map_add_lt e4 e5)
  · intro a b hab
    refine le_antisymm ((v.map_sub (ω a) (ω b)).trans (max_le (hω1' a) (hω1' b))) ?_
    by_contra hlt
    push_neg at hlt
    have h1 : v ((a.val : C) - (b.val : C)) < 1 := by
      have hx : (a.val : C) - b.val = -(ω a - a.val) + (ω a - ω b) + (ω b - b.val) := by ring
      rw [hx]
      exact v.map_add_lt (v.map_add_lt (by rw [Valuation.map_neg]; exact hω2 a) hlt) (hω2 b)
    have hnd : ¬ (p : ℤ) ∣ ((a.val : ℤ) - (b.val : ℤ)) := by
      intro hd
      apply hab
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hd
      push_cast at hd
      simpa [sub_eq_zero, ZMod.natCast_zmod_val] using hd
    have := v_intCast_eq_one hv hpv hnd
    push_cast at this
    rw [this] at h1
    exact lt_irrefl _ h1
end ReciprocityTheory.PGsh.Up.U3
