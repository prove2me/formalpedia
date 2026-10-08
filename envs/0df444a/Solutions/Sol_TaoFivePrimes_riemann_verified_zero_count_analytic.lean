-- Prove2me | solution 1 for TaoFivePrimes.riemann_verified_zero_count_analytic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T05:10:56.542711+00:00
-- url     : https://prove2.me/submissions/ff393386-f57f-49b4-8f08-f6cbfc3d572d

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import Batteries.Tactic.Lemma
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Fourier
import Definitions.Def_Zeta23_FromPNTPlus_Rectangle
import Definitions.Def_Zeta23_FromPNTPlus_ResidueCalcOnRectangles
import Definitions.Def_Zeta23_FromPNTPlus_Sobolev
import Definitions.Def_Zeta23_FromPNTPlus_StrongPNTPrefix
import Definitions.Def_Zeta23_FromPNTPlus_ZetaBounds
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_RvM_LocalCount
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_ZetaReflect
import Theorems.Thm_ZerosBound
import Theorems.Thm_Zeta23_RvM_analyticOrderNatAt_gfun
import Theorems.Thm_Zeta23_RvM_norm_riemannZeta_sub_one_le
import Theorems.Thm_Zeta23_RvM_zeta_growth_right_at
import Theorems.Thm_Zeta23_StirlingVert_re_digamma_stirlingPrime
import Theorems.Thm_Zeta23_mu_smooth
import Theorems.Thm_Zeta23_MuInts_integral_main_eq
import Theorems.Thm_Zeta23_ZeroConfig_N_le_two_mul_half
import Theorems.Thm_ZetaKernel_rect6_riemannZeta_ne_zero_of_abs_im_le_six
import Theorems.Thm_Zeta23_RvM_reZeroSet_card_le_of_growth
import Theorems.Thm_Zeta23_RvM_backlund_horizontal_of_count_at
import Theorems.Thm_Zeta23_RvM_rvM_main_param
import Theorems.Thm_Zeta23_RvM_vertical_two
-- BEGIN ScalarConstants

section
set_option autoImplicit false
set_option maxHeartbeats 0
namespace TaoZeroCount

lemma exp_four_ge_forty : (40:ℝ)≤ Real.exp 4 := by
  have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤8/3)
    (show (8/3:ℝ)≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) 4
  rw [show Real.exp 4=(Real.exp 1)^4 by
    simpa only [Nat.cast_ofNat,mul_one] using Real.exp_nat_mul (1:ℝ) 4]
  norm_num at h ⊢
  linarith

lemma log_between_zero_four (x : ℝ) (hx : 1≤ x) (h40 : x≤40) :
    0≤ Real.log x ∧ Real.log x≤4 := by
  refine ⟨Real.log_nonneg hx,?_⟩
  exact (Real.log_le_iff_le_exp (by linarith : 0< x)).mpr (h40.trans exp_four_ge_forty)

lemma jensen_coefficient_le_hundred (r : ℝ) (hr : (1/10:ℝ)≤ Real.log r)
    (x : ℝ) (hx : 1≤ x) (h40 : x≤40) :
    1/Real.log r*(|Real.log x|+2)≤100 := by
  obtain ⟨h0,h4⟩ := log_between_zero_four x hx h40
  rw [abs_of_nonneg h0]
  have hl : 0< Real.log r := by linarith
  have hi : 1/Real.log r≤10 := (div_le_iff₀ hl).mpr (by linarith)
  have hmul := mul_le_mul hi (show Real.log x+2≤6 by linarith)
    (by linarith : 0≤ Real.log x+2) (by norm_num : (0:ℝ)≤10)
  linarith

lemma half_coefficient_le_hundred :
    1/Real.log ((0.95:ℝ)/0.84)*(|Real.log (3*(20/3))|+2*max (1:ℝ) 0)≤100 := by
  norm_num only [show (3*(20/3):ℝ)=20 by norm_num,max_eq_left (by norm_num : (0:ℝ)≤1),mul_one]
  apply jensen_coefficient_le_hundred _ _ _ (by norm_num) (by norm_num)
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<(0.95:ℝ)/0.84)
  norm_num at h ⊢
  linarith

lemma realzero_coefficient_le_hundred :
    1/Real.log ((0.9:ℝ)/0.8)*(|Real.log (6*(20/3))|+2*max (1:ℝ) 0)≤100 := by
  norm_num only [show (6*(20/3):ℝ)=40 by norm_num,max_eq_left (by norm_num : (0:ℝ)≤1),mul_one]
  apply jensen_coefficient_le_hundred _ _ _ (by norm_num) (by norm_num)
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<(0.9:ℝ)/0.8)
  norm_num at h ⊢
  linarith

lemma backlund_coefficient_le_thousand : 2*Real.pi*((100:ℝ)+1)≤1000 := by
  linarith [Real.pi_lt_d2]

lemma log_T0_le_twenty_two : Real.log (329*10^7:ℝ)≤22 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0:ℝ)<329*10^7)).mpr
  rw [show Real.exp 22=(Real.exp 1)^22 by
    simpa only [Nat.cast_ofNat,mul_one] using Real.exp_nat_mul (1:ℝ) 22]
  have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2718/1000)
    (show (2718/1000:ℝ)≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) 22
  exact (by norm_num : (329*10^7:ℝ)≤(2718/1000)^22).trans h

lemma log_main_T0_le : Real.log ((329*10^7:ℝ)/(2*Real.pi*Real.exp 1))≤477/25 := by
  have he20 : (485160000:ℝ)≤ Real.exp 20 := by
    rw [show Real.exp 20=(Real.exp 1)^20 by
      simpa only [Nat.cast_ofNat,mul_one] using Real.exp_nat_mul (1:ℝ) 20]
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2.7182818283) Real.exp_one_gt_d9.le 20
    exact (by norm_num : (485160000:ℝ)≤2.7182818283^20).trans h
  have he008 : (27/25:ℝ)≤ Real.exp (2/25) := by
    have h := Real.add_one_le_exp (2/25:ℝ)
    linarith
  have he208 : (523972800:ℝ)≤ Real.exp (502/25) := by
    have h := mul_le_mul he20 he008 (by norm_num) (Real.exp_pos 20).le
    rw [←Real.exp_add] at h
    norm_num at h ⊢
    exact h
  have hpi : (157/25:ℝ)≤2*Real.pi := by linarith [Real.pi_gt_d2]
  have hbig := mul_le_mul hpi he208 (by norm_num) (by positivity : (0:ℝ)≤2*Real.pi)
  have hT : (329*10^7:ℝ)≤2*Real.pi*Real.exp (502/25) := by nlinarith
  apply (Real.log_le_iff_le_exp (by positivity : (0:ℝ)<(329*10^7)/(2*Real.pi*Real.exp 1))).mpr
  apply (div_le_iff₀ (by positivity : (0:ℝ)<2*Real.pi*Real.exp 1)).mpr
  have he : Real.exp (477/25)*(2*Real.pi*Real.exp 1)=2*Real.pi*Real.exp (502/25) := by
    rw [show Real.exp (502/25)=Real.exp (477/25)*Real.exp 1 by
      rw [←Real.exp_add]; congr 1; norm_num]
    ring
  rw [he]
  exact hT

lemma coarse_count_budget :
    (329*10^7:ℝ)/(2*Real.pi)*Real.log ((329*10^7:ℝ)/(2*Real.pi*Real.exp 1))+
      3845*29*Real.log (329*10^7:ℝ)+601≤10^10 := by
  calc
    _ ≤ (329*10^7:ℝ)/(2*Real.pi)*(477/25)+3845*29*22+601 := by
      gcongr
      · exact log_main_T0_le
      · exact log_T0_le_twenty_two
    _ ≤ (329*10^7:ℝ)/(157/25)*(477/25)+3845*29*22+601 := by
      gcongr
      linarith [Real.pi_gt_d2]
    _ ≤ _ := by norm_num

end TaoZeroCount

end
-- END ScalarConstants
-- BEGIN DyadicCount
section
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace TaoZeroCountDyadic

def rvMain (t : ℝ) : ℝ := t / (2 * Real.pi) * Real.log (t / (2 * Real.pi * Real.exp 1))
def T0 : ℝ := 329 * 10 ^ 7

theorem rvMain_eq (t : ℝ) (ht : 0 < t) :
    rvMain t = t / (2 * Real.pi) * (Real.log (t / (2 * Real.pi)) - 1) := by
  have hp : 0 < 2 * Real.pi := by positivity
  have hlog : Real.log (t / (2 * Real.pi * Real.exp 1)) =
      Real.log (t / (2 * Real.pi)) - 1 := by
    rw [div_mul_eq_div_div, Real.log_div (div_pos ht hp).ne' (Real.exp_pos 1).ne',
      Real.log_exp]
  exact congrArg (fun z => t / (2 * Real.pi) * z) hlog

theorem rvMain_lower (t : ℝ) (ht : 0 < t) : -1 ≤ rvMain t := by
  rw [rvMain_eq t ht]
  have hy : 0 < t / (2 * Real.pi) := div_pos ht (by positivity)
  have hm := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hy) hy.le
  rw [mul_sub, mul_one, mul_inv_cancel₀ hy.ne'] at hm
  nlinarith

theorem rvMain_doubling (t : ℝ) (ht : 0 < t) :
    rvMain (2 * t) - rvMain t =
      t / (2 * Real.pi) * (Real.log (t / (2 * Real.pi)) + 2 * Real.log 2 - 1) := by
  have hy : 0 < t / (2 * Real.pi) := div_pos ht (by positivity)
  have hlog : Real.log (2 * t / (2 * Real.pi)) =
      Real.log 2 + Real.log (t / (2 * Real.pi)) := by
    rw [show 2 * t / (2 * Real.pi) = 2 * (t / (2 * Real.pi)) by ring,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hy.ne']
  rw [rvMain_eq (2 * t) (by positivity), rvMain_eq t ht, hlog]
  ring

theorem dyadic_count_bound (F : ℝ → ℝ)
    (hstep : ∀ t : ℝ, 5 ≤ t →
      F (2 * t) - F t ≤ rvMain (2 * t) - rvMain t + 3845 * Real.log t)
    (hbase : F (T0 / 2 ^ 29) ≤ 600) :
    F T0 ≤ rvMain T0 + 3845 * 29 * Real.log T0 + 601 := by
  have ht0 : 0 < T0 := by norm_num [T0]
  have hiter : ∀ n : ℕ, n ≤ 29 →
      F T0 ≤ F (T0 / (2 : ℝ) ^ n) + rvMain T0 - rvMain (T0 / (2 : ℝ) ^ n) +
        3845 * n * Real.log T0 := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hi := ih (by omega)
      have hp : 0 < (2 : ℝ) ^ (n + 1) := by positivity
      have hp29 : (2 : ℝ) ^ (n + 1) ≤ 2 ^ 29 := by gcongr; norm_num
      have ht5 : 5 ≤ T0 / (2 : ℝ) ^ (n + 1) := by
        apply (le_div_iff₀ hp).mpr
        calc
          5 * (2 : ℝ) ^ (n + 1) ≤ 5 * 2 ^ 29 := by gcongr
          _ ≤ T0 := by norm_num [T0]
      have htpos : 0 < T0 / (2 : ℝ) ^ (n + 1) := div_pos ht0 hp
      have hp1 : 1 ≤ (2 : ℝ) ^ (n + 1) := one_le_pow₀ (by norm_num)
      have htle : T0 / (2 : ℝ) ^ (n + 1) ≤ T0 := by
        apply (div_le_iff₀ hp).mpr
        nlinarith
      have htwo : 2 * (T0 / (2 : ℝ) ^ (n + 1)) = T0 / (2 : ℝ) ^ n := by
        rw [pow_succ]
        field_simp
      have hs := hstep (T0 / (2 : ℝ) ^ (n + 1)) ht5
      rw [htwo] at hs
      have hl := mul_le_mul_of_nonneg_left (Real.log_le_log htpos htle)
        (by norm_num : (0 : ℝ) ≤ 3845)
      simp only [Nat.cast_add, Nat.cast_one] at *
      nlinarith
  have h := hiter 29 (le_refl _)
  have hl := rvMain_lower (T0 / 2 ^ 29) (by norm_num [T0])
  norm_num only [Nat.cast_ofNat] at h
  linarith

end TaoZeroCountDyadic

end
-- END DyadicCount
-- BEGIN DyadicBudget
section
set_option autoImplicit false
namespace TaoZeroCountDyadic

theorem count_le_ten_billion (F : ℝ→ℝ)
    (hstep : ∀ t : ℝ, 5≤ t → F (2*t)-F t≤ rvMain (2*t)-rvMain t+3845*Real.log t)
    (hbase : F (T0/2^29)≤600) : F T0≤10^10 := by
  apply (dyadic_count_bound F hstep hbase).trans
  simpa only [rvMain,T0] using TaoZeroCount.coarse_count_budget

end TaoZeroCountDyadic

end
-- END DyadicBudget
-- BEGIN HalfCountExplicit
section
-- Prove2me | solution 1 for Zeta23.RvM.half_count_large
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:43:29.098311+00:00
-- url     : https://prove2.me/submissions/f80e7f91-829b-47cf-a7a0-21de426b715b


-- from Zeta23.Defs.Counting
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Defs/Counting.lean — elementary counting facts for an abstract ZeroConfig.
[eq:trivialchain] at the abstract level; Statement.lean transfers it to ζ.
-/

open Set

noncomputable section

namespace Zeta23.ZeroConfig

variable (Z : ZeroConfig) (T₁ T₂ : ℝ)

lemma window_finite : (Z.window T₁ T₂).Finite := Z.finite_window T₁ T₂








end Zeta23.ZeroConfig
end
end

-- from Zeta23.RvM.ZetaGrowth
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/ZetaGrowth.lean — growth of ζ in vertical strips (consumed by the Landau/Jensen
local zero count and the Backlund S(T) bound).

CONTENT:
* `norm_riemannZeta_le_of_re_pos` — the explicit half-plane bound
      ‖ζ(s)‖ ≤ 1/2 + 1/‖1 − s‖ + ‖s‖ / Re s        (0 < Re s, s ≠ 1),
  from the N = 1 case of the summation-by-parts representation
      ζ(s) = Σ_{n≤ N} n^{-s} − N^{1−s}/(1−s) − N^{−s}/2 + s ∫_N^∞ (⌊x⌋ + 1/2 − x) x^{−s−1} dx
  [Tit86, (2.1.4) / §2.1], which is `riemannZeta0` / `Zeta23_Zeta0EqZeta` in the PrimeNumberTheoremAnd
  port Zeta23/FromPNTPlus/ZetaBounds.lean (Apache-2.0, see README § Provenance).
* `riemannZeta_linear_growth` — for every δ > 0:  ‖ζ(σ+it)‖ ≤ (5/2 + δ⁻¹)·|t|  (σ ≥ δ, |t| ≥ 1)
  [Tit86, §5.1: ζ(s) = O(|t|) uniformly in σ ≥ δ], and the ∃-constant corollaries
  (`zeta_growth`, `zeta_growth_quarter`).
* `norm_riemannZeta_sub_one_le` — ‖ζ(s) − 1‖ ≤ π²/6 − 1 for Re s ≥ 2, hence the two-sided bounds
  0 < 2 − π²/6 ≤ ‖ζ(s)‖ ≤ π²/6 there (the Jensen/Landau disc centre 2 + it needs ζ ≠ 0 and a
  lower bound at the centre) [Tit86, §9.2 uses |ζ(2+iT)| ≥ … > 0].
* `analyticOnNhd_riemannZeta` — ζ is analytic on any set avoiding 1 (Mathlib's
  differentiableAt_riemannZeta, repackaged for the Jensen hypotheses).

NOT here: anything for Re s ≤ 0 (that needs the functional equation + Γ-ratio growth, i.e.
Stirling); no consumer in this repository needs it (σ ≥ 1/4 suffices).
-/

open Complex Set MeasureTheory Real

noncomputable section

namespace Zeta23
namespace RvM

/-! ## Analyticity away from the pole -/


/-! ## The half-plane bound  [Tit86, (2.1.4) with N = 1] -/


/-! ## Linear growth in σ ≥ δ  [Tit86, §5.1] -/





theorem zeta_growth_right :
    ∃ A C : ℝ, 0 < C ∧ ∀ s : ℂ, (0.15 : ℝ) ≤ s.re → 1 ≤ ‖s - 1‖ →
      ‖riemannZeta s‖ ≤ C * (|s.im| + 3) ^ A :=
  ⟨1, 20 / 3, by norm_num, zeta_growth_right_at⟩

/-! ## Bounds on Re s ≥ 2 (the Jensen disc centre)  -/



/-- Lower bound at the Jensen disc centre: 0 < 2 − π²/6 ≤ ‖ζ(s)‖ for Re s ≥ 2. -/
theorem norm_riemannZeta_ge_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    2 - Real.pi ^ 2 / 6 ≤ ‖riemannZeta s‖ := by
  have h := norm_riemannZeta_sub_one_le hs
  have h' : ‖(1 : ℂ)‖ - ‖1 - riemannZeta s‖ ≤ ‖riemannZeta s‖ := by
    simpa using norm_sub_norm_le (1 : ℂ) (1 - riemannZeta s)
  rw [norm_sub_rev] at h'
  simp only [norm_one] at h'
  linarith


/-- 1/3 < 2 − π²/6 (π < 3.15 ⇒ π²/6 < 1.654). -/
lemma one_third_lt_two_sub_pi_sq_div_six : (1 / 3 : ℝ) < 2 - Real.pi ^ 2 / 6 := by
  have := Real.pi_lt_d2
  nlinarith [Real.pi_pos]

/-- **Consumer interface.** ‖ζ(2 + it)‖ ≥ 1/3 for all real t. -/
theorem zeta_lower_bound_two : ∀ t : ℝ, (1 / 3 : ℝ) ≤ ‖riemannZeta (2 + t * I)‖ := by
  intro t
  have h := norm_riemannZeta_ge_of_two_le_re (s := 2 + t * I) (by simp)
  linarith [one_third_lt_two_sub_pi_sq_div_six]



end RvM
end Zeta23
end
end

-- from Zeta23.RvM.LocalCount
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/LocalCount.lean

H-RvM's local count for Mathlib's ζ:  N(t, t+1] ≤ A₀ log(|t| + 3) for all real t
(= Zeta23.RiemannVonMangoldt.local_count at Z := zetaZeroConfig; [Tit86, Thm 9.2]).

Route (never evaluating ζ left of σ = 0.19, so no Stirling is needed):
 * count only zeros with β ≥ 1/2 and double (Zeta23.ZeroConfig.N_le_two_mul_half, Zeta23/RvM/Halving.lean,
   via the ρ ↦ 1−ρ̄ symmetry);
 * Jensen-type zero count on a disc: the ported PNT+ `ZerosBound` (Zeta23/FromPNTPlus/StrongPNTPrefix.lean,
   Apache-2.0) applied to g(w) := ζ(c₀ + 1.9 w)/ζ(c₀), c₀ := 2 + (t+½)i, r = 0.84, R = 0.95:
   the β ≥ 1/2 part of the window lies in ‖w‖ ≤ 0.84 (1.5² + 0.5² ≤ (1.9·0.84)²), the big disc stays in
   σ ≥ 0.195 and at distance ≥ 1 from the pole for |t| ≥ 4;
 * ζ-growth ‖ζ(s)‖ ≤ C(|Im s|+3)^A on σ ≥ 0.15, ‖s−1‖ ≥ 1 and ‖ζ(2+it)‖ ≥ 1/3
   (Zeta23.RvM.zeta_growth_right / zeta_lower_bound_two, Zeta23/RvM/ZetaGrowth.lean);
 * |t| < 4 by the finite constant N(−4, 5].
-/


open Complex Set Filter Topology Metric

noncomputable section

namespace Zeta23.RvM

/-- zeros of ζ in any compact set are finite (none accumulate, none near the pole). -/
theorem riemannZeta_zeros_finite_of_isCompact {K : Set ℂ} (hK : IsCompact K) :
    (K ∩ {ρ : ℂ | ρ ≠ 1 ∧ riemannZeta ρ = 0}).Finite := by
  choose t ht hfin using riemannZeta_zeros_locallyFinite
  obtain ⟨I, -, hcover⟩ := hK.elim_nhds_subcover t (fun z _ => ht z)
  refine (I.finite_toSet.biUnion fun z _ => hfin z).subset ?_
  rintro ρ ⟨hρK, hρ⟩
  obtain ⟨z, hzI, hρz⟩ := mem_iUnion₂.mp (hcover hρK)
  exact mem_iUnion₂.mpr ⟨z, hzI, hρz, hρ⟩


lemma comp_affine_analyticAt {s₀ c z : ℂ} (h : s₀ + c * z ≠ 1) :
    AnalyticAt ℂ (fun z : ℂ => riemannZeta (s₀ + c * z)) z := by
  have hζ : AnalyticAt ℂ riemannZeta (s₀ + c * z) := riemannZeta_analyticOnNhd_compl_one _ h
  have haff : AnalyticAt ℂ (fun z : ℂ => s₀ + c * z) z := by fun_prop
  exact hζ.comp_of_eq haff rfl

lemma gfun_analyticAt {s₀ c u z : ℂ} (h : s₀ + c * z ≠ 1) : AnalyticAt ℂ (gfun s₀ c u) z := by
  have h1 := comp_affine_analyticAt h
  have h2 : AnalyticAt ℂ (fun _ : ℂ => u) z := analyticAt_const
  have := h1.mul h2
  exact this










end Zeta23.RvM
end
open Complex Set Filter Topology Metric
open Zeta23
open Zeta23.RvM

theorem TaoZeroCount.half_count_of_growth (A C : ℝ) (hC : 0 < C)
    (hgrowth : ∀ s : ℂ, (0.15 : ℝ) ≤ s.re → 1 ≤ ‖s - 1‖ →
      ‖riemannZeta s‖ ≤ C * (|s.im| + 3) ^ A) :
    ∀ t : ℝ, 4 ≤ |t| → NhalfR t ≤
      (1/Real.log ((0.95:ℝ)/0.84)*(|Real.log (3*C)|+2*max A 0))*
        Real.log (|t|+3) := by
  have hL := zeta_lower_bound_two
  set A' : ℝ := max A 0 with hA'
  have hA'0 : 0 ≤ A' := le_max_right _ _
  -- constants
  set r : ℝ := 0.84 with hr
  set R : ℝ := 0.95 with hR
  have hlogRr : 0 < Real.log (R / r) := Real.log_pos (by norm_num [hr, hR])
  intro t ht
  -- centre and rescaling
  set c₀ : ℂ := 2 + (t + 1/2 : ℝ) * I with hc₀
  set κ : ℂ := ((19/10 : ℝ) : ℂ) with hκ
  have hκ0 : κ ≠ 0 := by simp [hκ]
  have hnormκ : ‖κ‖ = 1.9 := by simp [hκ]; norm_num
  have hζc₀ : (1/3 : ℝ) ≤ ‖riemannZeta c₀‖ := by simpa [hc₀] using hL (t + 1/2)
  have hζc₀ne : riemannZeta c₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hζc₀; norm_num at hζc₀
  set u : ℂ := (riemannZeta c₀)⁻¹ with hu
  have hu0 : u ≠ 0 := inv_ne_zero hζc₀ne
  have hnu : ‖u‖ ≤ 3 := by
    rw [hu, norm_inv]; rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
  set g : ℂ → ℂ := gfun c₀ κ u with hg
  -- geometry: ‖c₀ + κ z - 1‖ ≥ |t + 1/2| - 1.9 ‖z‖
  have hc₀1 : |t + 1/2| ≤ ‖c₀ - 1‖ := by
    have : (c₀ - 1).im = t + 1/2 := by simp [hc₀]
    rw [← this]; exact Complex.abs_im_le_norm _
  have ht' : 3.5 ≤ |t + 1/2| := by
    rcases le_abs'.mp ht with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hdist : ∀ z : ℂ, ‖z‖ ≤ 1 → |t + 1/2| - 1.9 * ‖z‖ ≤ ‖c₀ + κ * z - 1‖ := by
    intro z hz
    have h1 : ‖c₀ - 1‖ - ‖κ * z‖ ≤ ‖c₀ + κ * z - 1‖ := by
      have := norm_sub_norm_le (c₀ - 1) (-(κ * z))
      rw [norm_neg] at this
      have e : c₀ - 1 - -(κ * z) = c₀ + κ * z - 1 := by ring
      rw [e] at this; linarith
    rw [norm_mul, hnormκ] at h1; linarith
  have hne1 : ∀ z : ℂ, ‖z‖ ≤ 1 → c₀ + κ * z ≠ 1 := by
    intro z hz h
    have := hdist z hz
    rw [h, sub_self, norm_zero] at this
    nlinarith
  -- hypotheses of ZerosBound
  have hfAnalytic : AnalyticOnNhd ℂ g (Metric.closedBall (0 : ℂ) 1) := by
    intro z hz
    rw [Metric.mem_closedBall, _root_.dist_zero_right] at hz
    exact gfun_analyticAt (hne1 z hz)
  have hg0 : g 0 = 1 := by simp [hg, gfun, hu, hζc₀ne]
  have hfin : (SetOfZeros 1 g).Finite := by
    have hK := riemannZeta_zeros_finite_of_isCompact (isCompact_closedBall c₀ (1.9 : ℝ))
    refine (hK.image fun ρ => (ρ - c₀) / κ).subset ?_
    rintro z ⟨hz, hgz⟩
    refine ⟨c₀ + κ * z, ⟨?_, hne1 z hz, ?_⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, hnormκ]; nlinarith [norm_nonneg z]
    · simpa [hg, gfun, hu0] using hgz
    · show (c₀ + κ * z - c₀) / κ = z
      rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hκ0]
  set B : ℝ := 3 * C * (|t| + 6) ^ A' with hB
  have hBpos : 0 < B := by positivity
  have hfz : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ B := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := hz.trans (by norm_num [hR])
    set s : ℂ := c₀ + κ * z with hs
    have hsre : (0.15:ℝ) ≤ s.re := by
      have : s.re = 2 + 1.9 * z.re := by norm_num [hs, hc₀, hκ]
      rw [this]
      obtain ⟨h1, -⟩ := abs_le.mp ((abs_re_le_norm z).trans hz)
      rw [hR] at h1; nlinarith
    have hs1 : 1 ≤ ‖s - 1‖ := by have := hdist z hz1; rw [hR] at hz; nlinarith
    have hsim : |s.im| + 3 ≤ |t| + 6 := by
      have : s.im = t + 1/2 + 1.9 * z.im := by norm_num [hs, hc₀, hκ]
      rw [this]
      have hzi := (abs_im_le_norm z).trans hz; rw [hR] at hzi
      have h1 := abs_add_le (t + 1/2) (1.9 * z.im)
      have h2 : |1.9 * z.im| ≤ 1.9 * 0.95 := by
        rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1.9)]; nlinarith
      have h3 : |t + 1/2| ≤ |t| + 1/2 := by simpa using abs_add_le t (1/2)
      linarith
    have h1 : ‖riemannZeta s‖ ≤ C * (|s.im| + 3) ^ A := hgrowth s hsre hs1
    have hbase : 1 ≤ |s.im| + 3 := by linarith [abs_nonneg s.im]
    have h2 : (|s.im| + 3) ^ A ≤ (|s.im| + 3) ^ A' := Real.rpow_le_rpow_of_exponent_le hbase (le_max_left _ _)
    have h3 : (|s.im| + 3) ^ A' ≤ (|t| + 6) ^ A' := Real.rpow_le_rpow (by linarith [abs_nonneg s.im]) hsim hA'0
    calc ‖g z‖ = ‖riemannZeta s‖ * ‖u‖ := by simp [hg, gfun, hs]
      _ ≤ (C * (|t| + 6) ^ A') * 3 := by
          apply mul_le_mul (h1.trans ((mul_le_mul_of_nonneg_left (h2.trans h3) hC.le))) hnu (norm_nonneg _)
          positivity
      _ = B := by rw [hB]; ring
  have hZ := ZerosBound (B := B) (r := r) (R := R) (by norm_num [hr]) (by norm_num [hr])
    (by norm_num [hr, hR]) (by norm_num [hR]) hfAnalytic hg0 hfin hfz
  -- the window's β ≥ 1/2 part maps injectively into the zero finset of g
  set W : Set ℂ := zetaZeroConfig.window t (t + 1) ∩ {ρ | 1/2 ≤ ρ.re} with hW
  have hWfin : W.Finite := (zetaZeroConfig.finite_window t (t + 1)).subset inter_subset_left
  set φ : ℂ → ℂ := fun ρ => (ρ - c₀) / κ with hφ
  have hφinj : Function.Injective φ := by
    intro a b h; simp only [hφ] at h
    have := congrArg (fun w => c₀ + κ * w) h
    simpa [mul_div_cancel₀ _ hκ0] using this
  have hφinv : ∀ ρ, c₀ + κ * φ ρ = ρ := by intro ρ; simp only [hφ]; field_simp; ring
  have hmemS : ∀ ρ ∈ W, φ ρ ∈ (finiteSetOfZeros_mono (by norm_num [hr] : r < 1) hfin).toFinset := by
    rintro ρ ⟨⟨hρZ, hρt, hρt1⟩, hρre⟩
    simp only [Set.Finite.mem_toFinset]
    have hρ : IsNontrivialZero ρ := hρZ
    refine ⟨?_, ?_⟩
    · -- ‖φ ρ‖ ≤ 0.84
      simp only [hφ, norm_div, hnormκ]
      rw [div_le_iff₀ (by norm_num), hr]
      have hre : (ρ - c₀).re = ρ.re - 2 := by simp [hc₀]
      have him : (ρ - c₀).im = ρ.im - (t + 1/2) := by simp [hc₀]
      have hsq : ‖ρ - c₀‖ ^ 2 ≤ (0.84 * 1.9) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
        have := hρ.2.2; have := hρre.out
        nlinarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp hsq
    · show g (φ ρ) = 0
      simp only [hg, gfun, hφinv]; rw [hρ.1, zero_mul]
  have hmult : ∀ ρ ∈ W, (zeroMult ρ : ℝ) = (analyticOrderNatAt g (φ ρ) : ℝ) := by
    rintro ρ ⟨⟨hρZ, -, -⟩, -⟩
    have hρ : IsNontrivialZero ρ := hρZ
    rw [analyticOrderNatAt_gfun hκ0 hu0 (by rw [hφinv]; exact hρ.not_trivial.2), hφinv]
  -- compare the sums
  have hsum : NhalfR t ≤ ((∑ ρ' ∈ (finiteSetOfZeros_mono (by norm_num [hr] : r < 1) hfin).toFinset,
      analyticOrderNatAt g ρ' : ℕ) : ℝ) := by
    unfold NhalfR
    rw [← hW, finsum_mem_eq_finite_toFinset_sum _ hWfin,
      Finset.sum_congr rfl (fun ρ hρ => hmult ρ (hWfin.mem_toFinset.mp hρ)),
      ← Finset.sum_image (f := fun w => (analyticOrderNatAt g w : ℝ))
        (fun a _ b _ h => hφinj h)]
    push_cast
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro w hw
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hw
      exact hmemS ρ (hWfin.mem_toFinset.mp hρ)
    · intros; positivity
  -- log B ≤ (|log 3C| + 2A') log(|t|+3)
  have hlog3 : 1 ≤ Real.log (|t| + 3) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith [abs_nonneg t]
  have hlog6 : Real.log (|t| + 6) ≤ 2 * Real.log (|t| + 3) := by
    rw [← Real.log_rpow (by positivity), Real.rpow_two]
    apply Real.log_le_log (by positivity); nlinarith [abs_nonneg t]
  have hlogB : Real.log B ≤ (|Real.log (3 * C)| + 2 * A') * Real.log (|t| + 3) := by
    rw [hB, Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity)]
    have h1 := le_abs_self (Real.log (3 * C))
    have h2 : |Real.log (3 * C)| ≤ |Real.log (3 * C)| * Real.log (|t| + 3) :=
      le_mul_of_one_le_right (abs_nonneg _) hlog3
    have h3 : A' * Real.log (|t| + 6) ≤ A' * (2 * Real.log (|t| + 3)) :=
      mul_le_mul_of_nonneg_left hlog6 hA'0
    linarith
  calc NhalfR t ≤ _ := hsum
    _ ≤ 1 / Real.log (R / r) * Real.log B := by exact_mod_cast hZ
    _ ≤ 1 / Real.log (R / r) * ((|Real.log (3 * C)| + 2 * A') * Real.log (|t| + 3)) :=
        mul_le_mul_of_nonneg_left hlogB (by positivity)
    _ = _ := by ring

end
-- END HalfCountExplicit
-- BEGIN MuExplicit
section
open Complex MeasureTheory
open Zeta23
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace TaoZeroCount

lemma mu_pointwise (t : ℝ) (ht : 1 ≤ t) :
    |mu t - 1 / (2 * Real.pi) * Real.log (t / (2 * Real.pi))| ≤ 4 / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hp : 0 < 2 * Real.pi := by positivity
  have hd := Zeta23.StirlingVert.re_digamma_stirlingPrime
    (a := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (t := t / 2)
    (by rw [abs_of_pos (by positivity : 0 < t / 2)]; linarith)
  rw [abs_of_pos (by positivity : 0 < t / 2)] at hd
  push_cast at hd
  have harg : (1 / 4 : ℂ) + I * (t : ℂ) / 2 = (1 / 4 : ℂ) + I * (t / 2 : ℝ) := by
    push_cast; ring
  have hlog : Real.log (t / (2 * Real.pi)) = Real.log (t / 2) - Real.log Real.pi := by
    rw [show t / (2 * Real.pi) = (t / 2) / Real.pi by ring]
    exact Real.log_div (by positivity) Real.pi_ne_zero
  have heq : mu t - 1 / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) =
      1 / (2 * Real.pi) * ((digamma ((1 / 4 : ℂ) + I * (t / 2 : ℝ))).re - Real.log (t / 2)) := by
    rw [mu, harg, hlog]; ring
  rw [heq, abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  push_cast
  calc
    _ ≤ 1 / (2 * Real.pi) * (5 / (t / 2) ^ 2) := mul_le_mul_of_nonneg_left hd (by positivity)
    _ ≤ 4 / t ^ 2 := by
      field_simp
      nlinarith [Real.pi_gt_three]

lemma mu_log_bound (t : ℝ) (ht : 1 ≤ t) : |mu t| ≤ 10 * Real.log (t + 3) := by
  have ht0 : 0 < t := by linarith
  have hp : 0 < 2 * Real.pi := by positivity
  have hLp := log_between_zero_four (2 * Real.pi) (by linarith [Real.pi_gt_three])
    (by linarith [Real.pi_lt_four])
  have hLt : 0 ≤ Real.log t := Real.log_nonneg ht
  have hmono : Real.log t ≤ Real.log (t + 3) := Real.log_le_log ht0 (by linarith)
  have hL : (3 / 4 : ℝ) ≤ Real.log (t + 3) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 4)
    have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (show 4 ≤ t + 3 by linarith)
    norm_num at h
    linarith
  have hi : 1 / (2 * Real.pi) ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ hp).mpr
    linarith [Real.pi_gt_three]
  have hmain : |1 / (2 * Real.pi) * Real.log (t / (2 * Real.pi))| ≤
      Real.log (t + 3) + 1 := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi)),
      Real.log_div ht0.ne' hp.ne']
    have hlogabs : |Real.log t - Real.log (2 * Real.pi)| ≤ Real.log t + Real.log (2 * Real.pi) := by
      simpa [abs_of_nonneg hLt, abs_of_nonneg hLp.1] using abs_sub (Real.log t) (Real.log (2 * Real.pi))
    calc
      _ ≤ 1 / (2 * Real.pi) * (Real.log t + Real.log (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hlogabs (by positivity)
      _ ≤ (1 / 4 : ℝ) * (Real.log (t + 3) + 4) :=
        mul_le_mul hi (by linarith [hLp.2]) (by linarith [hLp.1]) (by norm_num)
      _ ≤ _ := by linarith
  have herr : 4 / t ^ 2 ≤ (4 : ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos ht0)).mpr
    nlinarith
  have htri := abs_add_le (mu t - 1 / (2 * Real.pi) * Real.log (t / (2 * Real.pi)))
    (1 / (2 * Real.pi) * Real.log (t / (2 * Real.pi)))
  rw [sub_add_cancel] at htri
  linarith [mu_pointwise t ht]

lemma mu_integral_bound (T : ℝ) (hT : 1 ≤ T) :
    |(∫ t in T..2 * T, mu t) - T * ell1 T / (2 * Real.pi)| ≤ 4 / T := by
  have hT0 : 0 < T := by linarith
  have hc : ContinuousOn (fun t : ℝ => 1 / (2 * Real.pi) * Real.log (t / (2 * Real.pi)))
      (Set.uIcc T (2 * T)) := by
    apply continuousOn_const.mul
    apply ContinuousOn.log (continuousOn_id.div_const _) ?_
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    change t / (2 * Real.pi) ≠ 0
    exact ne_of_gt (div_pos (by linarith [ht.1]) (by positivity))
  rw [← Zeta23.MuInts.integral_main_eq hT0, ← intervalIntegral.integral_sub
    (Zeta23.mu_smooth.continuous.intervalIntegrable _ _) hc.intervalIntegrable]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := T) (b := 2 * T) (C := 4 / T ^ 2)
    (f := fun t => mu t - 1 / (2 * Real.pi) * Real.log (t / (2 * Real.pi))) (by
      intro t ht
      rw [Set.uIoc_of_le (by linarith)] at ht
      rw [Real.norm_eq_abs]
      exact (mu_pointwise t (by linarith [ht.1])).trans (by
        apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hT0)
        nlinarith [ht.1]))
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 2 * T - T)] at hb
  have heq : 4 / T ^ 2 * (2 * T - T) = 4 / T := by field_simp; ring
  simpa only [heq] using hb

end TaoZeroCount

end
-- END MuExplicit
-- BEGIN LocalCountExplicit
section
open Complex MeasureTheory
open Zeta23 Zeta23.RvM
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace TaoZeroCount

lemma half_count_explicit (t : ℝ) (ht : 4 ≤ |t|) : NhalfR t ≤ 100 * Real.log (|t| + 3) := by
  have h := half_count_of_growth 1 (20 / 3) (by norm_num)
    (fun s hs h1 => zeta_growth_right_at s hs h1) t ht
  exact h.trans (mul_le_mul_of_nonneg_right half_coefficient_le_hundred
    (Real.log_nonneg (by linarith [abs_nonneg t])))

lemma small_count_eq_zero (t : ℝ) (ht : |t| ≤ 4) : Ncount t (t + 1) = 0 := by
  have hset : zerosIn t (t + 1) = ∅ := by
    ext s
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hs
    have ht' := abs_le.mp ht
    exact ZetaKernel.rect6_riemannZeta_ne_zero_of_abs_im_le_six (s := s) hs.1.2.1 hs.1.2.2
      (abs_le.mpr ⟨by linarith [hs.2.1], by linarith [hs.2.2]⟩) hs.1.1
  simp [Ncount, hset]

lemma local_count_explicit (t : ℝ) : (Ncount t (t + 1) : ℝ) ≤ 200 * Real.log (|t| + 3) := by
  rcases le_or_gt 4 |t| with ht | ht
  · have h := zetaZeroConfig.N_le_two_mul_half t (t + 1)
    change (Ncount t (t + 1) : ℝ) ≤ 2 * NhalfR t at h
    linarith [half_count_explicit t ht]
  · rw [small_count_eq_zero t ht.le, Nat.cast_zero]
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith [abs_nonneg t]))

lemma backlund_explicit (T : ℝ) (hT : 4 ≤ T)
    (havoid : ∀ s, IsNontrivialZero s → s.im ≠ T) :
    |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T * I)).im| ≤ 1000 * Real.log T := by
  have hJ : ∀ t : ℝ, 4 ≤ t → (reZeroSet t).Finite ∧ ((reZeroSet t).ncard : ℝ) ≤ 100 * Real.log t := by
    intro t ht
    obtain ⟨hf, hb⟩ := reZeroSet_card_le_of_growth (A := 1) (C := 20 / 3)
      (by norm_num) (fun s hs h1 => zeta_growth_right_at s hs h1) t ht
    exact ⟨hf, hb.trans (mul_le_mul_of_nonneg_right realzero_coefficient_le_hundred
      (Real.log_nonneg (by linarith)))⟩
  have h := backlund_horizontal_of_count_at hJ T (max_le hT (by linarith)) havoid
  exact h.trans (mul_le_mul_of_nonneg_right backlund_coefficient_le_thousand
    (Real.log_nonneg (by linarith)))

end TaoZeroCount

end
-- END LocalCountExplicit
-- BEGIN CountMain
section
open Complex MeasureTheory
open Zeta23 Zeta23.RvM
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace TaoZeroCount

lemma zerosIn_finite (a b : ℝ) : (zerosIn a b).Finite := by
  exact zetaSeam.finite_window a b

-- Window arithmetic follows the accepted Apache-2.0 Zeta23/RvM/NcountWindow proof.
-- Copyright 2026 Anthropic PBC; exact source attribution is retained in the local manifest.
lemma count_add {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) :
    Ncount a c = Ncount a b + Ncount b c := by
  have heq : zerosIn a c = zerosIn a b ∪ zerosIn b c := by
    ext s
    simp only [zerosIn, Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · rintro ⟨hs, ha, hc⟩
      rcases le_or_gt s.im b with hb | hb
      · exact Or.inl ⟨hs, ha, hb⟩
      · exact Or.inr ⟨hs, hb, hc⟩
    · rintro (⟨hs, ha, hb⟩ | ⟨hs, hb, hc⟩)
      · exact ⟨hs, ha, hb.trans h2⟩
      · exact ⟨hs, h1.trans_lt hb, hc⟩
  unfold Ncount
  rw [heq]
  refine finsum_mem_union ?_ (zerosIn_finite a b) (zerosIn_finite b c)
  rw [Set.disjoint_left]
  rintro s ⟨_, _, hb⟩ ⟨_, ha, _⟩
  exact (not_lt_of_ge hb) ha

lemma count_mono {a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d) : Ncount a b ≤ Ncount c d := by
  unfold Ncount
  rw [finsum_mem_eq_finite_toFinset_sum _ (zerosIn_finite a b),
    finsum_mem_eq_finite_toFinset_sum _ (zerosIn_finite c d)]
  apply Finset.sum_le_sum_of_subset
  intro s hs
  rw [Set.Finite.mem_toFinset] at hs ⊢
  exact ⟨hs.1, hca.trans_lt hs.2.1, hs.2.2.trans hbd⟩

lemma count_six_zero : Ncount 0 6 = 0 := by
  have heq : zerosIn 0 6 = ∅ := by
    ext s
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hs
    exact ZetaKernel.rect6_riemannZeta_ne_zero_of_abs_im_le_six (s := s) hs.1.2.1 hs.1.2.2
      (by rw [abs_of_pos hs.2.1]; exact hs.2.2) hs.1.1
  simp [Ncount, heq]

lemma count_low : (Ncount 0 ((329 * 10 ^ 7 : ℝ) / 2 ^ 29) : ℝ) ≤ 600 := by
  have hm := count_mono (a := 0) (b := (329 * 10 ^ 7 : ℝ) / 2 ^ 29)
    (c := 0) (d := 7) (by rfl) (by norm_num)
  have ha := count_add (a := 0) (b := 6) (c := 7) (by norm_num) (by norm_num)
  rw [count_six_zero, zero_add] at ha
  have hc := local_count_explicit 6
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 6), show (6 + 1 : ℝ) = 7 by norm_num,
    show (6 + 3 : ℝ) = 9 by norm_num] at hc
  have hlog : Real.log (9 : ℝ) ≤ 3 := by
    apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 9)).mpr
    rw [show Real.exp 3 = (Real.exp 1) ^ 3 by
      simpa only [Nat.cast_ofNat, mul_one] using Real.exp_nat_mul (1 : ℝ) 3]
    have he := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8 / 3)
      (show (8 / 3 : ℝ) ≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) 3
    exact (by norm_num : (9 : ℝ) ≤ (8 / 3) ^ 3).trans he
  rw [ha] at hm
  exact (Nat.cast_le.mpr hm).trans (by linarith)

lemma dyadic_step (T : ℝ) (hT : 5 ≤ T) :
    (Ncount 0 (2 * T) : ℝ) - (Ncount 0 T : ℝ) ≤
      TaoZeroCountDyadic.rvMain (2 * T) - TaoZeroCountDyadic.rvMain T + 3845 * Real.log T := by
  have hr := rvM_main_param (CB := 1000) (TB := 4) (A₀ := 200) (Cμ := 4) (Tμ := 1) (CM := 10)
    backlund_explicit vertical_two (by norm_num) local_count_explicit mu_integral_bound
    (by norm_num) mu_log_bound Zeta23.mu_smooth.continuous T (max_le (max_le (by linarith) (by linarith)) (by linarith))
  change |(Ncount T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1 T| ≤
    (3 * |(1000 : ℝ)| + 4 * 200 + 4 * 10 + |(4 : ℝ)| + 1) * Real.log T at hr
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1000),
    abs_of_pos (by norm_num : (0 : ℝ) < 4)] at hr
  have ha := count_add (a := 0) (b := T) (c := 2 * T) (by linarith) (by linarith)
  have har : (Ncount 0 (2 * T) : ℝ) = (Ncount 0 T : ℝ) + (Ncount T (2 * T) : ℝ) := by
    exact_mod_cast ha
  have hm := TaoZeroCountDyadic.rvMain_doubling T (by linarith)
  unfold ell1 Zeta23.l at hr
  linarith [le_of_abs_le hr]

lemma count_at_T0 : (Ncount 0 (329 * 10 ^ 7 : ℝ) : ℝ) ≤ (10 : ℝ) ^ 10 := by
  exact TaoZeroCountDyadic.count_le_ten_billion (fun t => (Ncount 0 t : ℝ)) dyadic_step count_low

end TaoZeroCount

end
-- END CountMain

-- BEGIN ClosedStripCount
section
set_option autoImplicit false
set_option maxHeartbeats 0
open scoped BigOperators
namespace TaoZeroCount

lemma zeta_ne_zero_on_re_zero {s : ℂ} (hre : s.re=0) : riemannZeta s≠0 := by
  rcases eq_or_ne s.im 0 with him | him
  · have hs : s=0 := Complex.ext (by simpa using hre) (by simpa using him)
    rw [hs,riemannZeta_zero]
    norm_num
  · have hneg : ∀ n : ℕ, s≠-(n:ℂ) := by
      intro n he
      have hh := congrArg Complex.im he
      simp only [Complex.neg_im,Complex.natCast_im,neg_zero] at hh
      exact him hh
    have hs1 : s≠1 := by
      intro he
      have hh := congrArg Complex.re he
      simp only [hre,Complex.one_re] at hh
      norm_num at hh
    intro hz
    have hn := riemannZeta_ne_zero_of_one_le_re (s:=1-s)
      (by simpa only [Complex.sub_re,Complex.one_re,hre,sub_zero] using (le_refl (1:ℝ)))
    apply hn
    rw [riemannZeta_one_sub hneg hs1,hz,mul_zero]

lemma closed_strip_zeros_eq (T : ℝ) :
    {s : ℂ | 0≤ s.re ∧ s.re≤1 ∧ 0≤ s.im ∧ s.im≤ T ∧ riemannZeta s=0} =
      Zeta23.zerosIn 0 T := by
  ext s
  change (0≤ s.re ∧ s.re≤1 ∧ 0≤ s.im ∧ s.im≤ T ∧ riemannZeta s=0) ↔
    ((riemannZeta s=0 ∧ 0< s.re ∧ s.re<1) ∧ 0< s.im ∧ s.im≤ T)
  constructor
  · rintro ⟨h0,_h1,him0,himT,hz⟩
    have hr0 : 0< s.re := by
      by_contra h
      have he : s.re=0 := le_antisymm (not_lt.mp h) h0
      exact zeta_ne_zero_on_re_zero he hz
    have hr1 : s.re<1 := by
      by_contra h
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz
    have hi : 0< s.im := by
      by_contra h
      have he : s.im=0 := le_antisymm (not_lt.mp h) him0
      exact ZetaKernel.rect6_riemannZeta_ne_zero_of_abs_im_le_six (s := s) hr0 hr1 (by simp [he]) hz
    exact ⟨⟨hz,hr0,hr1⟩,hi,himT⟩
  · rintro ⟨⟨hz,hr0,hr1⟩,hi,himT⟩
    exact ⟨hr0.le,hr1.le,hi.le,himT,hz⟩

theorem closed_strip_count_eq (T : ℝ) :
    (∑ᶠ s ∈ {s : ℂ | 0≤ s.re ∧ s.re≤1 ∧ 0≤ s.im ∧ s.im≤ T ∧ riemannZeta s=0},
      (analyticOrderNatAt riemannZeta s : ℝ)) = (Zeta23.Ncount 0 T : ℝ) := by
  rw [closed_strip_zeros_eq]
  have hfin : (Zeta23.zerosIn 0 T).Finite := Zeta23.zetaSeam.finite_window 0 T
  rw [Zeta23.Ncount,Nat.cast_finsum_mem hfin]
  rfl

theorem tao_closed_strip_count_eq :
    (∑ᶠ s ∈ {s : ℂ | 0≤ s.re ∧ s.re≤1 ∧ 0≤ s.im ∧ s.im≤3.29*10^9 ∧ riemannZeta s=0},
      (analyticOrderNatAt riemannZeta s : ℝ)) = (Zeta23.Ncount 0 (329*10^7) : ℝ) := by
  rw [closed_strip_count_eq]
  norm_num

end TaoZeroCount

end
-- END ClosedStripCount

/-
The Riemann--von Mangoldt count of zeta zeros in the verified window, weighted by
the analytic order of vanishing.

The dyadic summation above is rebuilt from the accepted Apache-2.0 source of
TaoFivePrimes.zeta_zero_count_multiplicity_T0_le (submission
0262b747-b745-43e4-b283-52ceb99c8a97).  The zero-free rectangles used for the
base case are imported as Proved platform theorems.  No unproved analytic input.
-/

namespace TaoFivePrimes

theorem riemann_verified_zero_count_analytic :
    (∑ᶠ s ∈ {s : ℂ | riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧
      s.im ≤ 3.29 * 10 ^ 9}, (analyticOrderNatAt riemannZeta s : ℝ)) ≤ (10 : ℝ) ^ 10 := by
  have h := TaoZeroCount.count_at_T0
  have hset :
      {s : ℂ | riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧
          s.im ≤ 3.29 * 10 ^ 9} =
        {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧ s.im ≤ 3.29 * 10 ^ 9 ∧
          riemannZeta s = 0} := by
    ext s
    simp only [Set.mem_setOf_eq, and_assoc, and_left_comm, and_comm]
  rw [hset]
  have h' :
      (∑ᶠ s ∈ {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧ s.im ≤ 3.29 * 10 ^ 9 ∧
        riemannZeta s = 0}, (analyticOrderNatAt riemannZeta s : ℝ))
        = (Zeta23.Ncount 0 (329 * 10 ^ 7 : ℝ) : ℝ) :=
    TaoZeroCount.tao_closed_strip_count_eq
  rw [h']
  simpa only [show (3.29 * 10 ^ 9 : ℝ) = 329 * 10 ^ 7 by norm_num] using h

end TaoFivePrimes

theorem solution :
    (∑ᶠ s ∈ {s : ℂ | riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧
      s.im ≤ 3.29 * 10 ^ 9}, (analyticOrderNatAt riemannZeta s : ℝ)) ≤ (10 : ℝ) ^ 10 :=
  TaoFivePrimes.riemann_verified_zero_count_analytic
