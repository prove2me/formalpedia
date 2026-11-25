-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.factorial_sum_add_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:14:08.550569+00:00
-- url     : https://prove2.me/submissions/7d3a8bb7-6280-4f2a-843b-ad3cff34802e

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonoNormSq
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_ChiPSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_chiPAux_multinomial_univ_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.GeometryOfNumbersTheory
open Finset
private theorem factorial_add_le_mul_pow (n k : ℕ) : (n + k).factorial ≤ n.factorial * (n + k) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Nat.add_assoc, Nat.factorial_succ, pow_succ]
    calc (n + k + 1) * (n + k).factorial ≤ (n + k + 1) * (n.factorial * (n + k) ^ k) :=
          Nat.mul_le_mul (le_refl _) ih
      _ ≤ (n + k + 1) * (n.factorial * (n + k + 1) ^ k) :=
          Nat.mul_le_mul (le_refl _) (Nat.mul_le_mul (le_refl _) (Nat.pow_le_pow_left (Nat.le_succ _) _))
      _ = n.factorial * ((n + k + 1) ^ k * (n + k + 1)) := by ring
end ReciprocityTheory.GeometryOfNumbersTheory
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Finset
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {D : ℕ} (a : Fin (D + 1) → ℕ) :
    ((∑ i, a i) + D).factorial ≤ (D + 1) ^ (∑ i, a i) * ((∑ i, a i) + D) ^ D * ∏ i, (a i).factorial := by
  have hspec := Nat.multinomial_spec (Finset.univ : Finset (Fin (D + 1))) a
  have hm := chiPAux_multinomial_univ_le a
  have h1 : (∑ i, a i).factorial ≤ (D + 1) ^ (∑ i, a i) * ∏ i, (a i).factorial := by
    calc (∑ i, a i).factorial = (∏ i, (a i).factorial) * Nat.multinomial Finset.univ a := hspec.symm
      _ ≤ (∏ i, (a i).factorial) * (D + 1) ^ (∑ i, a i) := Nat.mul_le_mul (le_refl _) hm
      _ = (D + 1) ^ (∑ i, a i) * ∏ i, (a i).factorial := mul_comm _ _
  calc ((∑ i, a i) + D).factorial ≤ (∑ i, a i).factorial * ((∑ i, a i) + D) ^ D := factorial_add_le_mul_pow _ _
    _ ≤ ((D + 1) ^ (∑ i, a i) * ∏ i, (a i).factorial) * ((∑ i, a i) + D) ^ D :=
        Nat.mul_le_mul h1 (le_refl _)
    _ = (D + 1) ^ (∑ i, a i) * ((∑ i, a i) + D) ^ D * ∏ i, (a i).factorial := by ring
end ReciprocityTheory.GeometryOfNumbersTheory
