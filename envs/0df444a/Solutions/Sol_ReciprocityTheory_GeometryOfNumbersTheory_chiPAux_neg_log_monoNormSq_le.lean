-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.chiPAux_neg_log_monoNormSq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:57:58.019871+00:00
-- url     : https://prove2.me/submissions/1cabedc9-d30f-47b2-a6e6-cb31eed6b8a4

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonoNormSq
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_ChiPSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_monoNormSq_pos
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_le_monoNormSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Finset
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {D : ℕ} (b : Fin (D + 1) → ℕ) :
    -Real.log (monoNormSq b) ≤
      (∑ i, b i : ℕ) * Real.log (D + 1) + D * Real.log ((∑ i, b i : ℕ) + D) := by
  have hQ := le_monoNormSq b
  have hA : (0 : ℝ) < (D + 1 : ℝ) ^ (∑ i, b i) := by positivity
  have hB : (0 : ℝ) < ((∑ i, b i : ℕ) + D : ℝ) ^ D := by
    rcases Nat.eq_zero_or_pos D with hD | hD
    · subst hD
      simp
    · apply pow_pos
      have h1 : (0 : ℝ) < D := by exact_mod_cast hD
      have h2 : (0 : ℝ) ≤ ((∑ i, b i : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
  have hQpos : 0 < (D + 1 : ℝ) ^ (∑ i, b i) * ((∑ i, b i : ℕ) + D : ℝ) ^ D := mul_pos hA hB
  have hlog : Real.log (((D + 1 : ℝ) ^ (∑ i, b i)) * ((∑ i, b i : ℕ) + D : ℝ) ^ D)⁻¹ ≤
      Real.log (monoNormSq b) := by
    first
      | exact Real.log_le_log (inv_pos.mpr hQpos) hQ
      | exact (Real.log_le_log_iff (inv_pos.mpr hQpos) (monoNormSq_pos b)).mpr hQ
  rw [Real.log_inv, Real.log_mul hA.ne' hB.ne', Real.log_pow, Real.log_pow] at hlog
  linarith
end ReciprocityTheory.GeometryOfNumbersTheory
