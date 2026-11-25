-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_GenusMassVolumes_gaussian_ray_integral__5c65c0386822
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:45:16.872969+00:00
-- url     : https://prove2.me/submissions/0a31a7d2-1aa2-490e-943a-c2cbca47d48d

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_GaussianIntegralFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset MeasureTheory
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : GaussianRayIntegral := by
  intro n t₀ Q hn ht hQ
  have hb : 0 < Q / t₀ ^ 2 := by positivity
  have key := _root_.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (n : ℝ) - 1) (b := Q / t₀ ^ 2)
    (by norm_num) (by have : (1 : ℝ) ≤ n := by exact_mod_cast hn
                      linarith) hb
  have hcongr : ∫ t in Set.Ioi (0 : ℝ), t ^ (n - 1) * Real.exp (-((t / t₀) ^ 2 * Q)) =
      ∫ x in Set.Ioi (0 : ℝ), x ^ ((n : ℝ) - 1) * Real.exp (-(Q / t₀ ^ 2) * x ^ (2 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    have e1 : t ^ ((n : ℝ) - 1) = t ^ (n - 1) := by
      rw [← Real.rpow_natCast]
      congr 1
      rw [Nat.cast_sub hn]; simp
    have e2 : t ^ (2 : ℝ) = t ^ 2 := by
      rw [← Real.rpow_natCast]; norm_num
    simp only [e1, e2]
    congr 2
    field_simp
  rw [hcongr, key]
  have e3 : -((n : ℝ) - 1 + 1) / 2 = -((n : ℝ) / 2) := by ring
  have e4 : ((n : ℝ) - 1 + 1) / 2 = (n : ℝ) / 2 := by ring
  rw [e3, e4, Real.rpow_neg hb.le, Real.div_rpow hQ.le (by positivity)]
  have e5 : (t₀ ^ 2) ^ ((n : ℝ) / 2) = t₀ ^ n := by
    rw [← Real.rpow_natCast t₀ 2, ← Real.rpow_mul ht.le, ← Real.rpow_natCast t₀ n]
    congr 1
    push_cast; ring
  rw [e5]
  have hQn : 0 < Q ^ ((n : ℝ) / 2) := Real.rpow_pos_of_pos hQ _
  field_simp
end Formalism.HermitianLattices.GenusMassVolumes
