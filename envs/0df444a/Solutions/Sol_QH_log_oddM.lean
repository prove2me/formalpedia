-- Prove2me | solution 1 for QH.log_oddM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:02:09.048958+00:00
-- url     : https://prove2.me/submissions/d315170a-8228-415d-8ab9-563cee83f61e

import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_PrimeSetTwoBounds
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_LogOddM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open QH
namespace QH
theorem _root_.solution :
    ∀ (z : ℝ) (q : ℕ), 0 ≤ z → 0 < q → Real.log ((16 * oddM z q : ℕ) : ℝ) ≤ Real.log 16 + Real.log q + z * Real.log 4 := by
  intro z q hz hq
  have hPle : (∏ p ∈ Icc 3 ⌊z⌋₊ with Nat.Prime p, p) ≤ 4 ^ ⌊z⌋₊ := by
    refine le_trans ?_ (primorial_le_4_pow ⌊z⌋₊)
    unfold primorial
    apply Finset.prod_le_prod_of_subset_of_one_le'
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hp ⊢
      exact ⟨by omega, hp.2⟩
    · intro p hp _
      simp only [Finset.mem_filter] at hp
      exact hp.2.one_lt.le
  have hPpos : 0 < (∏ p ∈ Icc 3 ⌊z⌋₊ with Nat.Prime p, p) :=
    Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.pos)
  have hoddM : oddM z q = q * (∏ p ∈ Icc 3 ⌊z⌋₊ with Nat.Prime p, p) := rfl
  generalize (∏ p ∈ Icc 3 ⌊z⌋₊ with Nat.Prime p, p) = P at hPle hPpos hoddM
  rw [hoddM]
  have hPR : (0 : ℝ) < P := by exact_mod_cast hPpos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hPle' : (P : ℝ) ≤ 4 ^ ⌊z⌋₊ := by exact_mod_cast hPle
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat]
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  have h1 : Real.log P ≤ (⌊z⌋₊ : ℝ) * Real.log 4 := by
    calc Real.log P ≤ Real.log ((4 : ℝ) ^ ⌊z⌋₊) := Real.log_le_log hPR hPle'
      _ = (⌊z⌋₊ : ℝ) * Real.log 4 := by rw [Real.log_pow]
  have h2 : (⌊z⌋₊ : ℝ) ≤ z := Nat.floor_le hz
  have h3 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  nlinarith
end QH
