-- Prove2me | solution 1 for ThreeSumSharpTail.admissible_parameters_solve_3sum
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-13T18:28:02.145643+00:00
-- url     : https://prove2.me/submissions/8dd09e30-fb6a-4ec5-b696-400ce5c61423

import Theorems.Thm_ThreeSumSharpTail_rational_theta_certificate
import Theorems.Thm_ThreeSumSharpTail_rational_cost_regime
import Theorems.Thm_ThreeSumSharpTail_cost_regime_solve_3sum

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem solution
    (c : ℕ) (θ : ℝ) (a s r : ℚ) (hc : 10 < c)
    (hθ0 : 0 < θ) (hθ9 : θ < 9 / 10)
    (ha0 : 0 < a) (ha1 : a < 1) (hs0 : 0 < s) (hs1 : s < 1)
    (henc : (a : ℝ) * (ThreeSumSharpTail.encodingExponent c + ThreeSumSharpTail.sharpSaving c θ) < 1)
    (hprep : (s : ℝ) < ThreeSumSharpTail.sharpSaving c θ)
    (hquery : (s : ℝ) < 1 / 2 - ThreeSumSharpTail.queryExponent θ)
    (hprime : Real.log 7 / Real.log 2 + 3 * (a : ℝ) / 2 < 3 - (a : ℝ) * s / 2)
    (hbuild : 2 + (a : ℝ) * (1 + (s : ℝ) / 2) < 3 - (a : ℝ) * s / 2)
    (hr : 2 - a * s / 4 < r) :
    EndStatement.ThreeSum.SolvedInTime r := by
  have hθ1 : θ < 1 := by linarith
  have hlogθ := Real.log_nonpos hθ0.le hθ1.le
  have hlog1θ := Real.log_nonpos (by linarith : 0 ≤ 1 - θ) (by linarith : 1 - θ ≤ 1)
  have hentropy : 0 ≤ ThreeSumSharpTail.entropy θ := by
    unfold ThreeSumSharpTail.entropy
    have hfirst : 0 ≤ -θ * Real.log θ := mul_nonneg_of_nonpos_of_nonpos (by linarith) hlogθ
    have hsecond : 0 ≤ -(1 - θ) * Real.log (1 - θ) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) hlog1θ
    linarith
  have hq0 : 0 ≤ ThreeSumSharpTail.queryExponent θ := by
    unfold ThreeSumSharpTail.queryExponent
    exact div_nonneg (add_nonneg hentropy (mul_nonneg hθ0.le (Real.log_nonneg (by norm_num))))
      (Real.log_nonneg (by norm_num))
  have hsHalfReal : (s : ℝ) < 1 / 2 := by linarith
  have hsHalf : s < 1 / 2 := (Rat.cast_lt (K := ℝ)).mp (by
    norm_num
    exact hsHalfReal)
  obtain ⟨η, hη0, hη9, hηenc, hηprep, hηquery⟩ :=
    ThreeSumSharpTail.rational_theta_certificate c θ a s hc hθ0 hθ9 henc hprep hquery
  obtain ⟨G, C, hC, hregime⟩ := ThreeSumSharpTail.rational_cost_regime c η a s hc
    (by exact_mod_cast hη0) ((Rat.cast_lt (K := ℝ)).mp (by
      norm_num
      exact hη9)) ha0
    (by exact_mod_cast ha1) hs0 hsHalfReal hηenc hηprep hηquery
  exact ThreeSumSharpTail.cost_regime_solve_3sum G a s r ha0 ha1 hs0 hsHalf
    ⟨C, hC, hregime⟩ hprime hbuild hr

-- This reduction remains open until the actual cost-regime algorithm bridge is proved.
