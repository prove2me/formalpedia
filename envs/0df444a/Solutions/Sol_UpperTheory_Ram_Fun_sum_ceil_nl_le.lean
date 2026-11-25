-- Prove2me | solution 1 for UpperTheory.Ram.Fun.sum_ceil_nl_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:59:30.526692+00:00
-- url     : https://prove2.me/submissions/4b34608d-3911-4d75-ae4b-663cc61aa4e6

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsPrimeOfDifferentLe
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_FunKit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Finset
noncomputable section
open UpperTheory UpperTheory.Ram UpperTheory.Ram.Fun
namespace UpperTheory.Ram.Fun
theorem _root_.solution (S : Finset ℕ) (n c t : ℕ → ℝ) {K k A B : ℝ} (hK : 0 ≤ K) (hk : 0 ≤ k)
    (hc : ∀ l ∈ S, 0 ≤ c l) (ht : ∀ l ∈ S, t l ≤ 3 / 2) (hn0 : ∀ l ∈ S, 0 ≤ n l)
    (hn : ∀ l ∈ S, n l = 0 ∨ n l = K * c l + k * (2 * c l + 1 + t l))
    (hA : ∑ l ∈ S, c l * Real.log l ≤ A) (hB : ∑ l ∈ S, Real.log l ≤ B) :
    ∑ l ∈ S, ((⌈n l⌉₊ : ℕ) : ℝ) * Real.log l ≤ (K + 2 * k) * A + (5 / 2 * k + 1) * B := by
  have h1 : ∀ l ∈ S, ((⌈n l⌉₊ : ℕ) : ℝ) * Real.log l ≤
      (K + 2 * k) * (c l * Real.log l) + (5 / 2 * k + 1) * Real.log l := by
    intro l hl
    have hl0 := Real.log_natCast_nonneg l
    have h2 := (Nat.ceil_lt_add_one (hn0 l hl)).le
    have h3 : n l + 1 ≤ (K + 2 * k) * c l + (5 / 2 * k + 1) := by
      have a := hc l hl
      have b := mul_le_mul_of_nonneg_left (ht l hl) hk
      rcases hn l hl with h | h <;> rw [h]
      · nlinarith [mul_nonneg hK a, mul_nonneg hk a]
      · nlinarith
    have := mul_le_mul_of_nonneg_right (h2.trans h3) hl0
    nlinarith
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have a := mul_le_mul_of_nonneg_left hA (by positivity : 0 ≤ K + 2 * k)
  have b := mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ 5 / 2 * k + 1)
  linarith
end UpperTheory.Ram.Fun
