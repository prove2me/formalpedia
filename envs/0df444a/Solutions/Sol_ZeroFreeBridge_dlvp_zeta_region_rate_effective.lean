-- Prove2me | solution 1 for ZeroFreeBridge.dlvp_zeta_region_rate_effective
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:41:28.937979+00:00
-- url     : https://prove2.me/submissions/56bf1c8b-cd1e-453d-a653-14edcde32233

import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
import Theorems.Thm_ZeroFreeBridge_Azeta_le_of_c0_2_gamma
import Theorems.Thm_ZeroFreeBridge_U_le_of_c0_2_gamma
import Theorems.Thm_ZeroFreeBridge_dlvp_zeta_region_concrete_wired
import Theorems.Thm_ZeroFreeBridge_hpole_effective
import Theorems.Thm_ZeroFreeBridge_norm_logDeriv_g_le_wired
import Theorems.Thm_ZeroFreeBridge_zeta_norm_ge_two_sub
import Theorems.Thm_ZeroFreeBridge_zeta_zero_count_strip
/- PHASE 4 (dVP frontier, ζ boundary growth — LOWER BOUND): a uniform lower bound on |ζ|
   at Re s = 2, the missing lower half of the ζ-growth sphere input.

   The composition `DlvpBoundaryDecomp.norm_logDeriv_le_of_boundary_split` needs, on the sphere,
   `log‖ζ z‖ - log‖ζ c‖ ≤ Aζ`; the upper half is `zeta_sphere_bound`, the lower half is a POSITIVE
   lower bound `‖ζ c‖ ≥ c₀`.  Centering the dVP disk at `Re c = 2` makes this an absolute constant:

     `2 - π²/6 ≤ ‖ζ(s)‖`   for   `2 ≤ Re s`   (and `2 - π²/6 > 0`).

   Proof: `ζ(s) = ∑ₙ 1/(n+1)^s = 1 + T` (Dirichlet series, `n=0` term is `1`); reverse triangle
   `‖ζ‖ ≥ 1 - ‖T‖`; `‖T‖ ≤ ∑ₙ 1/(n+2)^{Re s} ≤ ∑ₙ 1/(n+2)² = π²/6 - 1` (termwise since `Re s ≥ 2`,
   the tail of Basel `hasSum_zeta_two`); so `‖ζ‖ ≥ 1 - (π²/6 - 1) = 2 - π²/6`.  conjecture1_proved = False.
-/


open Complex

namespace ZeroFreeBridge





/-- The constant is positive: `0 < 2 - π²/6`  (since `π < 3.15 ⟹ π² < 9.93 < 12`). -/
theorem two_sub_pi_sq_div_six_pos : (0 : ℝ) < 2 - Real.pi ^ 2 / 6 := by
  nlinarith [Real.pi_lt_d2, Real.pi_pos]



end ZeroFreeBridge


/- PHASE 4 (dVP frontier, item (A) — the explicit height-γ entire-part bound `hg_bound₁`): combine
   `norm_logDeriv_g_le_wired` (item 1, the fully-wired O(L) entire-part bound) with
   `Azeta_le_of_c0_2_gamma` (item 2ii, `Aζ'' ≤ log((2|γ|+11)/(2-π²/6))`) into the explicit `Bg` that
   `bc_sum_concrete` consumes for the concrete centre `c₀ = 2+iγ`.  This is the last analytic
   assembling step for the height-γ half; discharging `hc2/hRlt/himc` at `c₀=2+iγ` (via `simp` on
   `re`/`im`) and monotonicity (`gcongr`) in the oscillation constant.  conjecture1_proved = False.
-/


open Complex MeromorphicOn Metric

namespace ZeroFreeBridge

/-- **Explicit O(log|γ|) entire-part bound for c₀ = 2+iγ.**  Combines `norm_logDeriv_g_le_wired`
    (item 1) with `Azeta_le_of_c0_2_gamma` (item 2): the `Bg` that `bc_sum_concrete` consumes,
    with the sphere-oscillation constant replaced by its explicit `log((2|γ|+11)/(2-π²/6))` bound. -/
theorem hg_bound_gamma {γ R : ℝ} {g : ℂ → ℂ} (hR : 0 < R) (hR2 : R < 3/2) (hγ : R + 2 ≤ |γ|)
    (D : CanonicalDecomp (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) g R)
    {z₀ : ℂ} (hz₀ : ‖z₀‖ < R) :
    ‖logDeriv g z₀‖
      ≤ 4 * Real.log ((2 * |γ| + 11) / (2 - Real.pi ^ 2 / 6))
          * (R + ‖z₀ - 0‖) / (R - ‖z₀ - 0‖) ^ 2 := by
  have hc2 : (2 : ℝ) ≤ ((2 : ℂ) + (γ : ℂ) * I).re := by simp
  have hRlt : R < ((2 : ℂ) + (γ : ℂ) * I).re - 1 / 2 := by simp; linarith
  have himc : R + 2 ≤ |((2 : ℂ) + (γ : ℂ) * I).im| := by simp; exact hγ
  have hw := norm_logDeriv_g_le_wired hR hc2 hRlt himc D hz₀
  refine hw.trans ?_
  have hρ : ‖z₀ - 0‖ < R := by rwa [sub_zero]
  have hRz : (0:ℝ) < R - ‖z₀ - 0‖ := sub_pos.mpr hρ
  gcongr
  exact Azeta_le_of_c0_2_gamma γ R hR hR2 hγ

end ZeroFreeBridge


/- PHASE 4 (dVP frontier, the EFFECTIVE rate): `dlvp_zeta_region_rate` with an EXPLICIT constant.

   `dlvp_zeta_region_rate` concludes `∃ c > 0, β ≤ 1 - c/log|γ|` with `c` non-effective (its `A`
   came from Mathlib's bare-`∃` pole constant).  Here we use `hpole_effective` (explicit `A₀ = 16`,
   `ε₀ = 1/48`) instead, so `A = 16` is fixed and `c = dlvpRateC` is a CONCRETE closed-form real
   (built only from `π`, `log(23/22)`, `log(15/(2-π²/6))` — all effective).  With `A = 16` the width
   `σ - 1 = 1/(2(48 + 80L)) ≤ 1/96 < 1/48`, so `hpole_effective` applies with no neighborhood
   threshold on `L`.

   conjecture1_proved = False (NOT a proof of RH; a kernel-verified reduction for a concrete zero).
-/






open Complex MeromorphicOn Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge






set_option maxHeartbeats 3200000

theorem solution (β γ : ℝ) (k : ℤ)
    (h34 : 3/4 ≤ β) (hβ1 : β < 1) (hΓ : 55/16 ≤ |γ|) (hk : 1 ≤ k)
    (hmρ₀ : divisor riemannZeta (ball ((2 : ℂ) + (γ : ℂ) * I) (11/8)) ((β : ℂ) + (γ : ℂ) * I) = k) :
    β ≤ 1 - dlvpRateC / Real.log |γ| := by
  have hpi : (0 : ℝ) < 2 - Real.pi ^ 2 / 6 := two_sub_pi_sq_div_six_pos
  set Lr : ℝ := Real.log ((23/16) / (11/8)) with hLrdef
  have hLrpos : 0 < Lr := by rw [hLrdef]; exact Real.log_pos (by norm_num)
  have hLrne : Lr ≠ 0 := ne_of_gt hLrpos
  clear_value Lr
  set M : ℝ := (8 / (3 * Lr) + 608/9) / 16 with hMdef
  have hMpos : 0 < M := by rw [hMdef]; positivity
  clear_value M
  have hlog15 : 0 ≤ Real.log (15 / (2 - Real.pi ^ 2 / 6)) :=
    Real.log_nonneg (by rw [le_div_iff₀ hpi]; nlinarith [hpi])
  -- reduce the goal's constant to c = 1/(112*16*K), K = 1 + 2M(log15D+1)
  rw [dlvpRateC, dlvpRateK, ← hLrdef, ← hMdef]
  set K : ℝ := 1 + 2 * M * (Real.log (15 / (2 - Real.pi ^ 2 / 6)) + 1) with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  clear_value K
  have hA : (0:ℝ) < 16 := by norm_num
  have hA1 : (1:ℝ) ≤ 16 := by norm_num
  have hγ1 : (1 : ℝ) ≤ |γ| := by linarith
  have hlogγpos : 0 < Real.log |γ| := Real.log_pos (by linarith)
  have hlogγ1 : 1 ≤ Real.log |γ| := by
    have hle : Real.exp 1 ≤ |γ| := by nlinarith [Real.exp_one_lt_d9]
    calc (1 : ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ ≤ Real.log |γ| := Real.log_le_log (by positivity) hle
  have hc0re : ((2 : ℂ) + (γ : ℂ) * I).re = 2 := by simp
  have hc0im : ((2 : ℂ) + (γ : ℂ) * I).im = γ := by simp
  have hc1re : ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I).re = 2 := by simp
  have hc1im : ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I).im = 2 * γ := by simp
  have h2γ : |γ| ≤ |2 * γ| := by
    rw [abs_mul]; have h2 : |(2 : ℝ)| = 2 := by norm_num
    rw [h2]; linarith [abs_nonneg γ]
  have hc0lt : (1 : ℝ) < ((2 : ℂ) + (γ : ℂ) * I).re := by rw [hc0re]; norm_num
  have hc1lt : (1 : ℝ) < ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I).re := by rw [hc1re]; norm_num
  set C₁ : ℝ := Real.log ((2 * |γ| + 11) / (2 - Real.pi ^ 2 / 6)) / Lr with hC₁def
  set C₂ : ℝ := Real.log ((2 * |2 * γ| + 11) / (2 - Real.pi ^ 2 / 6)) / Lr with hC₂def
  have hC₁nn : 0 ≤ C₁ := by
    rw [hC₁def]; apply div_nonneg _ (le_of_lt hLrpos)
    apply Real.log_nonneg; rw [le_div_iff₀ hpi]; nlinarith [abs_nonneg γ, hpi]
  have hC₂nn : 0 ≤ C₂ := by
    rw [hC₂def]; apply div_nonneg _ (le_of_lt hLrpos)
    apply Real.log_nonneg; rw [le_div_iff₀ hpi]; nlinarith [abs_nonneg (2 * γ), hpi]
  have hC₁ : ((∑ᶠ ρ, divisor riemannZeta (closedBall ((2 : ℂ) + (γ : ℂ) * I) (11/8)) ρ : ℤ) : ℝ)
      ≤ C₁ := by
    have hcnt := zeta_zero_count_strip ((2 : ℂ) + (γ : ℂ) * I) (11/8) (23/16)
      (by rw [abs_of_pos (by norm_num : (0:ℝ) < 11/8)]; norm_num)
      (by rw [abs_of_pos (by norm_num : (0:ℝ) < 11/8), abs_of_pos (by norm_num : (0:ℝ) < 23/16)]; norm_num)
      hc0lt
      (by rw [abs_of_pos (by norm_num : (0:ℝ) < 23/16), hc0re]; norm_num)
      (by rw [abs_of_pos (by norm_num : (0:ℝ) < 23/16), hc0im]; linarith)
    rw [abs_of_pos (by norm_num : (0:ℝ) < 11/8), abs_of_pos (by norm_num : (0:ℝ) < 23/16),
      ← hLrdef] at hcnt
    refine le_trans hcnt ?_
    rw [hC₁def]
    have hUle := U_le_of_c0_2_gamma γ (23/16) (by norm_num) (by norm_num) (by linarith)
    have hζ0 := zeta_norm_ge_two_sub (s := (2 : ℂ) + (γ : ℂ) * I) (by rw [hc0re])
    set U : ℝ := (‖(2:ℂ)+(γ:ℂ)*I‖ + 23/16) / (|((2:ℂ)+(γ:ℂ)*I).im| - 23/16)
        + (‖(2:ℂ)+(γ:ℂ)*I‖ + 23/16) / (((2:ℂ)+(γ:ℂ)*I).re - 23/16) with hUdef
    have hfrac : U / ‖riemannZeta ((2:ℂ)+(γ:ℂ)*I)‖ ≤ (2 * |γ| + 11) / (2 - Real.pi ^ 2 / 6) := by
      gcongr
    have hlogle : Real.log (U / ‖riemannZeta ((2:ℂ)+(γ:ℂ)*I)‖)
        ≤ Real.log ((2 * |γ| + 11) / (2 - Real.pi ^ 2 / 6)) := by
      apply Real.log_le_log _ hfrac
      have h1 : (0:ℝ) < |((2:ℂ)+(γ:ℂ)*I).im| - 23/16 := by rw [hc0im]; linarith [abs_nonneg γ]
      have h2 : (0:ℝ) < ((2:ℂ)+(γ:ℂ)*I).re - 23/16 := by rw [hc0re]; norm_num
      have hznz : (0:ℝ) < ‖riemannZeta ((2:ℂ)+(γ:ℂ)*I)‖ := by linarith [hζ0, hpi]
      rw [hUdef]; positivity
    gcongr
  have hC₂ : ((∑ᶠ ρ, divisor riemannZeta (closedBall ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) (11/8)) ρ : ℤ) : ℝ)
      ≤ C₂ := by
    have hcnt := zeta_zero_count_strip ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) (11/8) (23/16)
      (by rw [abs_of_pos (by norm_num : (0:ℝ) < 11/8)]; norm_num)
      (by rw [abs_of_pos (by norm_num : (0:ℝ) < 11/8), abs_of_pos (by norm_num : (0:ℝ) < 23/16)]; norm_num)
      hc1lt
      (by rw [abs_of_pos (by norm_num : (0:ℝ) < 23/16), hc1re]; norm_num)
      (by rw [abs_of_pos (by norm_num : (0:ℝ) < 23/16), hc1im]; linarith only [h2γ, hΓ])
    rw [abs_of_pos (by norm_num : (0:ℝ) < 11/8), abs_of_pos (by norm_num : (0:ℝ) < 23/16),
      ← hLrdef] at hcnt
    refine le_trans hcnt ?_
    rw [hC₂def]
    have hUle := U_le_of_c0_2_gamma (2 * γ) (23/16) (by norm_num) (by norm_num) (by linarith only [h2γ, hΓ])
    have hζ1 := zeta_norm_ge_two_sub (s := (2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) (by rw [hc1re])
    set U : ℝ := (‖(2:ℂ)+((2*γ:ℝ):ℂ)*I‖ + 23/16) / (|((2:ℂ)+((2*γ:ℝ):ℂ)*I).im| - 23/16)
        + (‖(2:ℂ)+((2*γ:ℝ):ℂ)*I‖ + 23/16) / (((2:ℂ)+((2*γ:ℝ):ℂ)*I).re - 23/16) with hUdef
    have hfrac : U / ‖riemannZeta ((2:ℂ)+((2*γ:ℝ):ℂ)*I)‖
        ≤ (2 * |2 * γ| + 11) / (2 - Real.pi ^ 2 / 6) := by gcongr
    have hlogle : Real.log (U / ‖riemannZeta ((2:ℂ)+((2*γ:ℝ):ℂ)*I)‖)
        ≤ Real.log ((2 * |2 * γ| + 11) / (2 - Real.pi ^ 2 / 6)) := by
      apply Real.log_le_log _ hfrac
      have h1 : (0:ℝ) < |((2:ℂ)+((2*γ:ℝ):ℂ)*I).im| - 23/16 := by
        rw [hc1im]; nlinarith [h2γ, hΓ, abs_nonneg (2*γ)]
      have h2 : (0:ℝ) < ((2:ℂ)+((2*γ:ℝ):ℂ)*I).re - 23/16 := by rw [hc1re]; norm_num
      have hznz : (0:ℝ) < ‖riemannZeta ((2:ℂ)+((2*γ:ℝ):ℂ)*I)‖ := by linarith [hζ1, hpi]
      rw [hUdef]; positivity
    gcongr
  clear_value C₁ C₂
  have hAz1 : (0:ℝ) ≤ Real.log ((2 * |γ| + 11) / (2 - Real.pi ^ 2 / 6)) := by
    apply Real.log_nonneg; rw [le_div_iff₀ hpi]; nlinarith [abs_nonneg γ, hpi]
  have hAz2 : (0:ℝ) ≤ Real.log ((2 * |2 * γ| + 11) / (2 - Real.pi ^ 2 / 6)) := by
    apply Real.log_nonneg; rw [le_div_iff₀ hpi]; nlinarith [abs_nonneg (2 * γ), hpi]
  set Bg₁cap : ℝ := 4 * Real.log ((2 * |γ| + 11) / (2 - Real.pi ^ 2 / 6)) * (11/8 + 1) / (11/8 - 1) ^ 2
    with hBg₁capdef
  set Bg₂cap : ℝ :=
    4 * Real.log ((2 * |2 * γ| + 11) / (2 - Real.pi ^ 2 / 6)) * (11/8 + 1) / (11/8 - 1) ^ 2
    with hBg₂capdef
  have hBg1cap_nn : 0 ≤ Bg₁cap := by
    rw [hBg₁capdef]; exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hAz1) (by norm_num)) (by positivity)
  have hBg2cap_nn : 0 ≤ Bg₂cap := by
    rw [hBg₂capdef]; exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hAz2) (by norm_num)) (by positivity)
  clear_value Bg₁cap Bg₂cap
  set L : ℝ := 1 + (C₁ / (11/8 - 1) + Bg₁cap) / 16 + (C₂ / (11/8 - 1) + Bg₂cap) / 16 with hLdef
  have ht2 : (0 : ℝ) ≤ (C₁ / (11/8 - 1) + Bg₁cap) / 16 :=
    div_nonneg (add_nonneg (div_nonneg hC₁nn (by norm_num)) hBg1cap_nn) (by norm_num)
  have ht3 : (0 : ℝ) ≤ (C₂ / (11/8 - 1) + Bg₂cap) / 16 :=
    div_nonneg (add_nonneg (div_nonneg hC₂nn (by norm_num)) hBg2cap_nn) (by norm_num)
  have hL : 1 ≤ L := by rw [hLdef]; linarith
  have hLnum1 : (C₁ / (11/8 - 1) + Bg₁cap) / 16 ≤ L := by rw [hLdef]; linarith
  have hLnum2 : (C₂ / (11/8 - 1) + Bg₂cap) / 16 ≤ L := by rw [hLdef]; linarith
  clear_value L
  have hAL1 : (1 : ℝ) ≤ 16 * L := by linarith only [hL]
  have hden : (0 : ℝ) < 2 * (3 * 16 + 5 * (16 * L)) := by linarith only [hL]
  set σ : ℝ := 1 + 1 / (2 * (3 * 16 + 5 * (16 * L))) with hσdef
  clear_value σ
  have hσ_opt : σ - 1 = 1 / (2 * (3 * 16 + 5 * (16 * L))) := by rw [hσdef]; ring
  have hσ1 : 1 < σ := by rw [hσdef]; have := div_pos one_pos hden; linarith
  have hσ2 : σ ≤ 2 := by
    rw [hσdef]
    have h16 : (1 : ℝ) ≤ 2 * (3 * 16 + 5 * (16 * L)) := by linarith only [hL]
    have : 1 / (2 * (3 * 16 + 5 * (16 * L))) ≤ 1 := by rw [div_le_one hden]; linarith
    linarith
  have hR32 : (11/8 : ℝ) < 3/2 := by norm_num
  have hβR : 2 - β < (11/8 : ℝ) := by linarith
  have himc0 : (11/8 : ℝ) + 2 ≤ |γ| := by linarith
  have hβσ : β < σ := by linarith
  have hσdelt : σ - 1 < 1/48 := by
    rw [hσ_opt, div_lt_iff₀ hden]; linarith only [hL]
  have hpole_pf : (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
      ≤ (1 / ((σ : ℂ) - 1)).re + 16 := hpole_effective hσ1 hσdelt
  have hzn : ‖(σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)‖ = 2 - σ := by
    have he : (σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I) = ((σ - 2 : ℝ) : ℂ) := by push_cast; ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : σ - 2 ≤ 0)]; ring
  have hzn0 : ‖(σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I) - 0‖ = 2 - σ := by rw [sub_zero]; exact hzn
  have hzn1 : ‖(σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I)‖ = 2 - σ := by
    have he : (σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) = ((σ - 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : σ - 2 ≤ 0)]; ring
  have hzn10 : ‖(σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) - 0‖ = 2 - σ := by
    rw [sub_zero]; exact hzn1
  have hz₀mem : ‖(σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)‖ < (11/8 : ℝ) := by rw [hzn]; linarith
  have hz₀mem2 : ‖(σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I)‖ < (11/8 : ℝ) := by
    rw [hzn1]; linarith
  set Bg₁ : ℝ := 4 * Real.log ((2 * |γ| + 11) / (2 - Real.pi ^ 2 / 6))
      * ((11/8 : ℝ) + ‖(σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I) - 0‖)
      / ((11/8 : ℝ) - ‖(σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I) - 0‖) ^ 2 with hBg₁def
  set Bg₂ : ℝ := 4 * Real.log ((2 * |2 * γ| + 11) / (2 - Real.pi ^ 2 / 6))
      * ((11/8 : ℝ) + ‖(σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) - 0‖)
      / ((11/8 : ℝ) - ‖(σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) - 0‖) ^ 2
    with hBg₂def
  clear_value Bg₁ Bg₂
  have hd1 : (0 : ℝ) < (11/8 : ℝ) - (2 - σ) := by linarith
  have hBg1_le : Bg₁ ≤ Bg₁cap := by
    rw [hBg₁def, hBg₁capdef, hzn0, mul_div_assoc, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num) hAz1)
    gcongr <;> linarith
  have hBg2_le : Bg₂ ≤ Bg₂cap := by
    rw [hBg₂def, hBg₂capdef, hzn10, mul_div_assoc, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num) hAz2)
    gcongr <;> linarith
  have hgb₁ : ∀ g : ℂ → ℂ,
      CanonicalDecomp (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) g (11/8) →
      ‖logDeriv g ((σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I))‖ ≤ Bg₁ := by
    intro g D; rw [hBg₁def]; exact hg_bound_gamma (by norm_num) hR32 himc0 D hz₀mem
  have hgb₂ : ∀ g : ℂ → ℂ,
      CanonicalDecomp (fun w => riemannZeta (((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I) + w)) g (11/8) →
      ‖logDeriv g ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I))‖ ≤ Bg₂ := by
    intro g D; rw [hBg₂def]
    exact hg_bound_gamma (by norm_num) hR32 (by linarith only [h2γ, hΓ]) D hz₀mem2
  have hnum₁ : C₁ / ((11/8 : ℝ) - ‖(σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)‖) + Bg₁ ≤ 16 * L := by
    rw [hzn]
    have hRHS1 : C₁ / (11/8 - 1) + Bg₁cap ≤ 16 * L := by
      rw [mul_comm]; exact (div_le_iff₀ hA).mp hLnum1
    have hC1step : C₁ / ((11/8 : ℝ) - (2 - σ)) ≤ C₁ / (11/8 - 1) := by gcongr <;> linarith
    linarith [add_le_add hC1step hBg1_le]
  have hnum₂ : C₂ / ((11/8 : ℝ) - ‖(σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - ((2 : ℂ) + ((2 * γ : ℝ) : ℂ) * I)‖)
      + Bg₂ ≤ 16 * L := by
    rw [hzn1]
    have hRHS2 : C₂ / (11/8 - 1) + Bg₂cap ≤ 16 * L := by
      rw [mul_comm]; exact (div_le_iff₀ hA).mp hLnum2
    have hC2step : C₂ / ((11/8 : ℝ) - (2 - σ)) ≤ C₂ / (11/8 - 1) := by gcongr <;> linarith
    linarith [add_le_add hC2step hBg2_le]
  have hdiff₁ : DifferentiableAt ℂ riemannZeta ((σ : ℂ) + (γ : ℂ) * I) := by
    refine differentiableAt_riemannZeta ?_
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hdiff₂ : DifferentiableAt ℂ riemannZeta ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I) := by
    refine differentiableAt_riemannZeta ?_
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hreg : β ≤ 1 - 1 / (112 * (16 * L)) :=
    dlvp_zeta_region_concrete_wired σ 16 L β γ k (11/8) Bg₁ C₁ Bg₂ C₂ hA hL hk hσ_opt hβ1 hσ2
      (by norm_num) hβR himc0 hmρ₀ hpole_pf hgb₁ hC₁ hnum₁ hgb₂ hC₂ hnum₂
  -- L ≤ K·log|γ|
  have hLK : L ≤ K * Real.log |γ| := by
    set Lg1 : ℝ := Real.log ((2 * |γ| + 11) / (2 - Real.pi ^ 2 / 6)) with hLg1
    set Lg2 : ℝ := Real.log ((2 * |2 * γ| + 11) / (2 - Real.pi ^ 2 / 6)) with hLg2
    have hg12 : Lg1 ≤ Lg2 := by
      rw [hLg1, hLg2]; apply Real.log_le_log (by positivity); gcongr
    have hLγ2 : Lg2 ≤ (Real.log (15 / (2 - Real.pi ^ 2 / 6)) + 1) * Real.log |γ| := by
      rw [hLg2]
      have hstep : (2 * |2 * γ| + 11) / (2 - Real.pi ^ 2 / 6) ≤ (15 / (2 - Real.pi ^ 2 / 6)) * |γ| := by
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hpi]
        have h4 : 2 * |2 * γ| + 11 ≤ 15 * |γ| := by
          rw [abs_mul, show |(2:ℝ)| = 2 by norm_num]; nlinarith only [hγ1]
        nlinarith only [h4]
      calc Real.log ((2 * |2 * γ| + 11) / (2 - Real.pi ^ 2 / 6))
          ≤ Real.log ((15 / (2 - Real.pi ^ 2 / 6)) * |γ|) := Real.log_le_log (by positivity) hstep
        _ = Real.log (15 / (2 - Real.pi ^ 2 / 6)) + Real.log |γ| :=
            Real.log_mul (by positivity) (by positivity)
        _ ≤ (Real.log (15 / (2 - Real.pi ^ 2 / 6)) + 1) * Real.log |γ| := by nlinarith only [hlog15, hlogγ1]
    have heq1 : (C₁ / (11/8 - 1) + Bg₁cap) / 16 = M * Lg1 := by
      rw [hC₁def, hBg₁capdef, hMdef]; field_simp; ring
    have heq2 : (C₂ / (11/8 - 1) + Bg₂cap) / 16 = M * Lg2 := by
      rw [hC₂def, hBg₂capdef, hMdef]; field_simp; ring
    have hL2 : L = 1 + M * Lg1 + M * Lg2 := by rw [hLdef, heq1, heq2]
    have hp1 : 0 ≤ M * (Lg2 - Lg1) := mul_nonneg hMpos.le (by linarith)
    have hp2 : 0 ≤ M * ((Real.log (15 / (2 - Real.pi ^ 2 / 6)) + 1) * Real.log |γ| - Lg2) :=
      mul_nonneg hMpos.le (by linarith)
    have hp3 : 0 ≤ (Real.log |γ| - 1) := by linarith
    rw [hL2, hKdef]; nlinarith only [hp1, hp2, hp3]
  -- conclude
  have hden112 : (0:ℝ) < 112 * (16 * L) := by positivity
  have hchain : 112 * (16 * L) ≤ 112 * 16 * K * Real.log |γ| := by
    nlinarith only [hLK]
  have hrecip : 1 / (112 * 16 * K * Real.log |γ|) ≤ 1 / (112 * (16 * L)) :=
    one_div_le_one_div_of_le hden112 hchain
  have hce : (1 / (112 * 16 * K)) / Real.log |γ| = 1 / (112 * 16 * K * Real.log |γ|) := by rw [div_div]
  calc β ≤ 1 - 1 / (112 * (16 * L)) := hreg
    _ ≤ 1 - (1 / (112 * 16 * K)) / Real.log |γ| := by rw [hce]; linarith [hrecip]
