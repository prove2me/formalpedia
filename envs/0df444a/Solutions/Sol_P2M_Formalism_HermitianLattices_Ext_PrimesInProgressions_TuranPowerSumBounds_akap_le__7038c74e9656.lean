-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_akap_le__7038c74e9656
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:45:11.537876+00:00
-- url     : https://prove2.me/submissions/2b185693-4d90-48db-a9f3-294f2e132b1e

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExistsPowerSumLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TwentyFiveMulSmallConstant
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_th_pos
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_eps_pos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Complex
noncomputable section
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
private theorem mul_kap_div_eps_sq_eq_th_div_succ (a : ℕ) (ha : 1 ≤ a) (D : ℝ) (hD : 0 ≤ D) :
    (a : ℝ) * kap a D / eps a ^ 2 = th a / (D + 1) := by
  have ha0 : (a : ℝ) ≠ 0 := (Nat.cast_pos.mpr (by omega)).ne'
  have hi : eps a ^ 2 ≠ 0 := (pow_pos (eps_pos a) 2).ne'
  calc (a : ℝ) * kap a D / eps a ^ 2
      = th a / (D + 1) * ((a : ℝ) * (a : ℝ)⁻¹)
          * (eps a ^ 2 * (eps a ^ 2)⁻¹) := by
        have e : ∀ x h i d : ℝ, x * (h * i ^ 2 / (x * d)) / i ^ 2
            = h / d * (x * x⁻¹) * (i ^ 2 * (i ^ 2)⁻¹) := by
          intro x h i d
          ring
        unfold kap
        exact e _ _ _ _
    _ = th a / (D + 1) := by
        rw [mul_inv_cancel₀ ha0, mul_inv_cancel₀ hi, mul_one, mul_one]
private theorem div_mul_cancel_of_ne_zero_real (q d : ℝ) (hd : d ≠ 0) : q / d * d = q := by
  have e : q / d * d = q * (d * d⁻¹) := by ring
  rw [e, mul_inv_cancel₀ hd, mul_one]
end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
end
end

set_option autoImplicit false
open Finset Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
theorem _root_.solution (a : ℕ) (ha : 1 ≤ a) (D : ℝ) (hD : 0 ≤ D) : a * kap a D / eps a ^ 2 ≤ th a := by
  have hD1 : (0 : ℝ) < D + 1 := by linarith
  have hq0 : 0 ≤ th a / (D + 1) := (div_pos (th_pos a) hD1).le
  have hq : th a / (D + 1) * (D + 1) = th a :=
    div_mul_cancel_of_ne_zero_real _ _ hD1.ne'
  rw [mul_kap_div_eps_sq_eq_th_div_succ a ha D hD]
  nlinarith [hq, hq0, mul_nonneg hq0 hD]
end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
