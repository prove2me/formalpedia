-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.FrobeniusGroupField.pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:43:45.510108+00:00
-- url     : https://prove2.me/submissions/88ae53b2-6653-43fb-8b4e-458d2ccf681b

import Definitions.Def_ReciprocityTheory_DualLattices_EigPowEqOne
import Definitions.Def_ReciprocityTheory_DualLattices_IsAdicCompleteOfBasis
import Definitions.Def_ReciprocityTheory_DualLattices_SgAlgebraMap
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_seed
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_charP


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix Polynomial
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.FrobeniusGroupField
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.FrobeniusGroupField
theorem _root_.solution (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hv : v.Integers R)
    (hpv : v (algebraMap R C (p : R)) < 1)
    [Algebra ℤ_[p] R] {n : Type} [Fintype n] [DecidableEq n] {ι : Type}
    {O : Type} [CommRing O] [Algebra ℤ_[p] O] (ρ : O →ₐ[ℤ_[p]] Matrix n n ℤ_[p])
    (εT : ι → Matrix n n R) (sg : ι → O →+* R)
    (heig : ∀ a j, (ρ a).map (algebraMap ℤ_[p] R) * εT j = sg j a • εT j) (a : O) (t : ℕ)
    (i j : ι) (hi : εT i ≠ 0) (hj : εT j ≠ 0) (h : res hv (sg j a) ≠ res hv (sg i a) ^ p ^ t) :
    ∃ (b : O) (m : ℕ), 0 < m ∧ ¬ p ∣ m ∧ ρ b ^ m = 1 ∧
      res hv (sg j b) ≠ res hv (sg i b) ^ p ^ t := by
  have hpr : p.Prime := Fact.out
  let _ : Field (R ⧸ mI hv) := instField hv
  have hch : CharP (R ⧸ mI hv) p := charP p hv hpv
  set yi := res hv (sg i a)
  set yj := res hv (sg j a)
  have h10 : (1 : R ⧸ mI hv) ≠ 0 := one_ne_zero
  have h20 : (2 : R ⧸ mI hv) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff (R ⧸ mI hv) p 2).1 (by exact_mod_cast h0)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).1 this)
  have hc : ∃ c : ℤ, yi + (c : R ⧸ mI hv) ≠ 0 ∧ yj + (c : R ⧸ mI hv) ≠ 0 := by
    by_contra hno
    push Not at hno
    have h0 := hno 0
    have h1 := hno 1
    have h2 := hno 2
    simp only [Int.cast_zero, Int.cast_one, Int.cast_ofNat, add_zero] at h0 h1 h2
    by_cases a0 : yi = 0
    · have b1 := h1 (by rw [a0, zero_add]; exact h10)
      have b2 := h2 (by rw [a0, zero_add]; exact h20)
      exact h10 (by linear_combination b2 - b1)
    · have b0 := h0 a0
      by_cases a1 : yi + 1 = 0
      · have b2 := h2 (fun e => h10 (by linear_combination e - a1))
        exact h20 (by linear_combination b2 - b0)
      · have b1 := h1 a1
        exact h10 (by linear_combination b1 - b0)
  obtain ⟨c, hci, hcj⟩ := hc
  obtain ⟨b, m, s, hm0, hmp, hbm, hbres⟩ := seed p hv hpv ρ εT sg heig a c
  refine ⟨b, m, hm0, hmp, hbm, fun heq => h ?_⟩
  have hri : res hv (sg i a + c) = yi + c := by rw [map_add, map_intCast]
  have hrj : res hv (sg j a + c) = yj + c := by rw [map_add, map_intCast]
  rw [hbres j hj (by rwa [hrj]), hbres i hi (by rwa [hri]), hri, hrj, ← pow_mul, mul_comm,
    pow_mul] at heq
  have hcfix : ∀ k : ℕ, ((c : R ⧸ mI hv)) ^ p ^ k = c := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_mul, ih]
      have := map_intCast (frobenius (R ⧸ mI hv) p) c
      rwa [frobenius_def] at this
  have hrhs : (yi + c) ^ p ^ t = yi ^ p ^ t + c := by rw [add_pow_char_pow, hcfix]
  rw [hrhs] at heq
  have hsub : (yj + c - (yi ^ p ^ t + c)) ^ p ^ s = 0 := by
    rw [sub_pow_char_pow, heq, sub_self]
  have := pow_eq_zero_iff (pow_ne_zero s hpr.ne_zero) |>.1 hsub
  linear_combination this
end ReciprocityTheory.PGsh.Up.FrobeniusGroupField
