-- Prove2me | solution 1 for ZeroFreeBridge.riemannZeta_ne_zero_region
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:47:44.145297+00:00
-- url     : https://prove2.me/submissions/1a5c1bde-a639-47dd-bdc3-600b6972361e

import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
import Theorems.Thm_ZeroFreeBridge_dlvp_zeta_region_rate_effective
import Theorems.Thm_ZeroFreeBridge_zeta_zero_divisor_pos
/- PHASE 4 (dVP frontier, final-assembly foundation atoms): reusable helpers that cut the boilerplate
   of the capstone `dlvp_zeta_region_of_bc_sums` instantiation for c₀=2+iγ (and c₁=2+2iγ).

   Every downstream analyticity hypothesis derives from ONE atom, `zeta_recenter_ana_closedBall`
   (recentred ζ analytic on `closedBall 0 R`): `hf_ana` = `.mono ball_subset_closedBall`, sphere
   continuity = `.mono sphere_subset_closedBall |>.continuousOn`, `hf'_mero` = `.meromorphicOn`; and
   `hf_ana_cl`/`hf_mero` on the physical disk = `zeta_analyticOnNhd_disk` directly.  The `1∉closedBall`
   precondition is `one_notMem_closedBall_of_himc` (from `R+2 ≤ |c₀.im|`).  conjecture1_proved = False.
-/

open Complex MeromorphicOn Metric

namespace ZeroFreeBridge

/-- `1 ∉ closedBall c₀ R` from `R + 2 ≤ |c₀.im|` (the height dominates the radius). -/
theorem one_notMem_closedBall_of_himc {c₀ : ℂ} {R : ℝ} (himc : R + 2 ≤ |c₀.im|) :
    (1 : ℂ) ∉ closedBall c₀ R := by
  rw [mem_closedBall, Complex.dist_eq]
  intro hle
  have h3 : |((1 : ℂ) - c₀).im| = |c₀.im| := by
    rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
  have h4 : |((1 : ℂ) - c₀).im| ≤ ‖(1 : ℂ) - c₀‖ := Complex.abs_im_le_norm _
  rw [h3] at h4; linarith



end ZeroFreeBridge


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

namespace ZeroFreeBridge







theorem dlvpRateC_pos : 0 < dlvpRateC := by
  rw [dlvpRateC, dlvpRateK]
  have hpi : (0 : ℝ) < 2 - Real.pi ^ 2 / 6 := two_sub_pi_sq_div_six_pos
  have hLrpos : 0 < Real.log ((23/16) / (11/8)) := Real.log_pos (by norm_num)
  have hlog15 : 0 ≤ Real.log (15 / (2 - Real.pi ^ 2 / 6)) :=
    Real.log_nonneg (by rw [le_div_iff₀ hpi]; nlinarith [hpi])
  positivity



end ZeroFreeBridge



/- PHASE 4 (dVP frontier, the SELF-CONTAINED zero-free region): drop the multiplicity hypothesis.

   `dlvp_zeta_region_rate_effective` takes the zero's multiplicity `k` (with `1 ≤ k`) as input.
   `zeta_zero_divisor_pos` derives `1 ≤ divisor ζ (ball c₀ R) ρ₀` directly from `ζ ρ₀ = 0`
   (`analyticOrderAt ≥ 1` at a zero, finite because ζ is not locally zero on the connected disk —
   `ζ c₀ ≠ 0` at the centre `Re c₀ > 1`).  Feeding this in gives the fully self-contained region

     `riemannZeta_ne_zero_region` :  `55/16 ≤ |γ|` ∧ `1 - dlvpRateC/log|γ| < β`  ⟹  `ζ(β+iγ) ≠ 0`,

   i.e. `ζ(s) ≠ 0` on `Re s > 1 - dlvpRateC/log|Im s|` (for `|Im s| ≥ 55/16`), with `dlvpRateC` the
   EXPLICIT effective constant.  The `β ≥ 3/4` restriction of the rate theorem is discharged here:
   `dlvpRateC ≤ 1/1792` and `log|γ| ≥ 1`, so `1 - dlvpRateC/log|γ| > 3/4`, hence any zero in the
   region already has `β > 3/4`; and `β < 1` since ζ has no zeros with `Re ≥ 1`.

   conjecture1_proved = False (NOT a proof of RH — a kernel-verified reduction; it says a zero in the
   region cannot exist, which is what dVP gives, not a proof that ζ's zeros lie on the line).
-/




open Complex MeromorphicOn Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge




theorem solution (β γ : ℝ)
    (hγ : 55/16 ≤ |γ|) (hβlow : 1 - dlvpRateC / Real.log |γ| < β) :
    riemannZeta ((β : ℂ) + (γ : ℂ) * I) ≠ 0 := by
  intro hz
  have hβ1 : β < 1 := by
    by_contra h; push_neg at h
    exact riemannZeta_ne_zero_of_one_le_re (by simpa using h) hz
  have hlogγ1 : 1 ≤ Real.log |γ| := by
    have hle : Real.exp 1 ≤ |γ| := by nlinarith [Real.exp_one_lt_d9]
    calc (1 : ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ ≤ Real.log |γ| := Real.log_le_log (by positivity) hle
  have hpi : (0 : ℝ) < 2 - Real.pi ^ 2 / 6 := two_sub_pi_sq_div_six_pos
  have hdK1 : 1 ≤ dlvpRateK := by
    rw [dlvpRateK]
    have hLrpos : 0 < Real.log ((23/16) / (11/8)) := Real.log_pos (by norm_num)
    have hlog15 : 0 ≤ Real.log (15 / (2 - Real.pi ^ 2 / 6)) :=
      Real.log_nonneg (by rw [le_div_iff₀ hpi]; nlinarith [hpi])
    have : 0 ≤ 2 * ((8 / (3 * Real.log ((23/16) / (11/8))) + 608/9) / 16)
        * (Real.log (15 / (2 - Real.pi ^ 2 / 6)) + 1) := by positivity
    linarith
  have hcpos := dlvpRateC_pos
  have hcsmall : dlvpRateC ≤ 1/1792 := by
    rw [dlvpRateC, show (112:ℝ) * 16 * dlvpRateK = 1792 * dlvpRateK by ring]
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith [hdK1])
  have hdivsmall : dlvpRateC / Real.log |γ| ≤ 1/4 := by
    have h := div_le_self (le_of_lt hcpos) hlogγ1
    linarith [h, hcsmall]
  have h34 : 3/4 ≤ β := by linarith [hβlow, hdivsmall]
  have h1c0 : (1 : ℂ) ∉ closedBall ((2 : ℂ) + (γ : ℂ) * I) (11/8) :=
    one_notMem_closedBall_of_himc (by rw [show ((2 : ℂ) + (γ : ℂ) * I).im = γ by simp]; linarith)
  have hc0re2 : (1 : ℝ) < ((2 : ℂ) + (γ : ℂ) * I).re := by
    rw [show ((2 : ℂ) + (γ : ℂ) * I).re = 2 by simp]; norm_num
  have hρmem : (β : ℂ) + (γ : ℂ) * I ∈ ball ((2 : ℂ) + (γ : ℂ) * I) (11/8) := by
    rw [mem_ball_iff_norm,
      show (β : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I) = ((β - 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hk : 1 ≤ divisor riemannZeta (ball ((2 : ℂ) + (γ : ℂ) * I) (11/8)) ((β : ℂ) + (γ : ℂ) * I) :=
    zeta_zero_divisor_pos (by norm_num) h1c0 hc0re2 hρmem hz
  have hbound := dlvp_zeta_region_rate_effective β γ
    (divisor riemannZeta (ball ((2 : ℂ) + (γ : ℂ) * I) (11/8)) ((β : ℂ) + (γ : ℂ) * I))
    h34 hβ1 hγ hk rfl
  linarith [hbound, hβlow]
