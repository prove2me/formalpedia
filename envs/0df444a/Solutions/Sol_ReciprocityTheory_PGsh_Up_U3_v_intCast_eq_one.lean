-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.U3.v_intCast_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:59.071819+00:00
-- url     : https://prove2.me/submissions/0d46cc96-edb4-44be-b30f-30982baabe9e

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_v_intCast_le_one

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
theorem _root_.solution (hv : v.Integers R) (hpv : v (p : C) < 1) {n : ℤ}
    (h : ¬ (p : ℤ) ∣ n) : v (n : C) = 1 := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  obtain ⟨a, b, hab⟩ := (Prime.coprime_iff_not_dvd hpz).mpr h
  have h1 : (a : C) * (p : C) + (b : C) * (n : C) = 1 := by
    have := congrArg (Int.cast : ℤ → C) hab
    push_cast at this
    exact this
  have ha : v ((a : C) * (p : C)) < 1 := by
    rw [map_mul]
    calc v (a : C) * v (p : C) ≤ 1 * v (p : C) :=
          mul_le_mul_of_nonneg_right (v_intCast_le_one hv a) zero_le'
      _ < 1 := by rw [one_mul]; exact hpv
  have hb : 1 ≤ v ((b : C) * (n : C)) := by
    by_contra hlt
    push_neg at hlt
    have := v.map_add_lt ha hlt
    rw [h1, map_one] at this
    exact lt_irrefl _ this
  refine le_antisymm (v_intCast_le_one hv n) ?_
  rw [map_mul] at hb
  calc 1 ≤ v (b : C) * v (n : C) := hb
    _ ≤ 1 * v (n : C) := mul_le_mul_of_nonneg_right (v_intCast_le_one hv b) zero_le'
    _ = v (n : C) := one_mul _
end ReciprocityTheory.PGsh.Up.U3
