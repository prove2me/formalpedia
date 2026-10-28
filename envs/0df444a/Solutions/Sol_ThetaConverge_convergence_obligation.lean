-- Prove2me | solution 1 for ThetaConverge.convergence_obligation
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:25:53.53099+00:00
-- url     : https://prove2.me/submissions/33d58731-713a-4267-a40e-ae41ac3d1498

import Definitions.Def_ArdaRH65K_ThetaConverge
import Definitions.Def_ArdaRH65K_ThetaValue
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Theorems.Thm_ThetaConverge_imLnVal_cauchy
import Theorems.Thm_ThetaValue_imLn_formula
namespace ThetaGap
end ThetaGap
namespace ThetaValue
end ThetaValue
/-  ThetaValue.lean -- ANDÚRIL A4 θ-value instrument: toward a kernel box for
    φ(t) = arg Γℝ(1/2+it) = the Riemann–Siegel θ, with NO numeric hypotheses.

    ## THE ROUTE (Euler/Weierstrass limit form, γ-free).

    Γℝ(s) = π^{-s/2}·Γ(s/2), so with `s = 1/2+it`, `t = 14`:

        φ(14) = arg Γℝ(1/2+14i) = −7·log π + Im log Γ(1/4 + 7i).

    (Numerically φ(14) = θ_RS(14) ≈ −1.7829487; verified in the driver against mpmath's
    `siegeltheta(14)` and against `arg Γℝ` directly.)

    For `Im log Γ(z)` with `z = x+iy` (`x = 1/4`, `y = 7`) we use Mathlib's Gauss product
    `GammaSeq z n = n^z·n!/∏_{k=0}^n (z+k) → Γ(z)` (`Complex.GammaSeq_tendsto_Gamma`).  Its
    principal-log has imaginary part (this file's `imLn_formula`, PROVED):

        Im L_n = y·log n − Σ_{k=0}^n arctan(y/(x+k)),
        L_n := z·log n + log(n!) − Σ_{k=0}^n log(z+k)   (all principal complex logs),

    and `exp(L_n) = GammaSeq z n` (this file's `exp_Ln_eq_gammaSeq`, PROVED).  Each `arctan`
    term is boxed by the reusable `ArctanTaylor.arctan_bracket` instrument (no ψ, no Γ anchor).

    ## WHAT IS PROVED HERE (all axiom-clean, no numeric hypotheses).

      * `arg_eq_arctan_of_re_pos` : `w.arg = arctan(im w/re w)` for `re w > 0`  (the per-factor atom).
      * `imLn_formula`            : the exact `Im L_n` formula above, GENERAL in `(x,y,n)`, `x>0`.
      * `exp_Ln_eq_gammaSeq`      : `exp(L_n) = GammaSeq z n`, the bridge to the Gauss product.

    Together with `ArctanTaylor.arctan_bracket` these are a COMPLETE finite kernel pipeline: for
    any `n` they reduce `Im L_n` to a rational interval with no numeric hypotheses.

    ## THE PRECISE REMAINING GAP (named Props, honestly stated -- see mission "land D1 + the gap").

    Two obligations separate the proven finite `Im L_n` from the target `φ(14)` box:

      * `ThetaGap.ConvergenceObligation` (branch bridge) : `imLnVal x y n → Λ` for a real `Λ` that
        is a genuine argument of `Γ(z)` (`Γ(z) = ‖Γ(z)‖·exp(IΛ)`).  IMPORTANT honest correction,
        driver-verified: `Im L_n` converges to the CONTINUOUS unwrapped value `Im loggamma(1/4+7i)
        ≈ 6.230`, which is `arg Γ(z) + 2π` — NOT the principal `(Complex.log (Γ z)).im ≈ −0.053`.
        (`Im L_n` sweeps from `−2.93` at `n=1` up through `6.23`, crossing far outside `(−π,π)`.)  So
        the correct target is `Λ` characterized by the exp identity, not a principal-branch equality.
        This is the one genuine limit-interchange (from `exp_Ln_eq_gammaSeq` +
        `Complex.GammaSeq_tendsto_Gamma` + `exp` continuity, tracking the winding); a `Tendsto`
        obligation, NOT a numeric hypothesis.

      * `ThetaGap.RateObligation` (rate) : `|Λ − imLnVal x y n| ≤ C(x,y)/n` with an EXPLICIT
        elementary `C` -- provable by the integral-comparison harmonic-tail bound (`1/(2n)`-type
        `∑ 1/(x+k)` vs `log`) plus the cubic `arctan(u)=u−r`, `0<r<u³/3` residual, using only
        elementary calculus in Mathlib and this file's arctan corollaries.  Driver: at `n=2000`,
        honest `k≤30`, box width ≈ 9.4e-4 < the 2e-3 target.

    With both, `φ(14) = −7·log π + Λ` (continuous branch) is boxed by `−7·[log π box] +
    [imLnVal box] ± [rate]` -- a kernel interval of width ≤ 2e-3, no hypotheses.  `log π` is boxed
    by the corpus verified-log pattern, exactly as `TrigReduceOperating` boxes `log 2`.  The shape
    of the final consumption is recorded in `ThetaGap.PhiTargetShape`.

    conjecture1_proved = False.  The finite Im-part pipeline of the θ-value, kernel-clean; the θ
    VALUE box itself awaits the two named Props above (rate + branch bridge).  NOT a proof of RH.
-/




open Complex Real

namespace ThetaValue

/-! ### The per-factor atom: `arg` of a right-half-plane point is an `arctan`. -/



/-! ### The exact imaginary part of the finite log-Weierstrass sum `L_n`. -/



/-! ### The bridge to the Gauss product: `exp(L_n) = GammaSeq z n`. -/

/-- **Gauss-product bridge.**  `exp(L_n) = GammaSeq z n` for `n ≥ 1` and all `z+k ≠ 0`. -/
theorem exp_Ln_eq_gammaSeq (z : ℂ) (n : ℕ) (hn : 1 ≤ n)
    (hzk : ∀ k ∈ Finset.range (n+1), z + (k:ℂ) ≠ 0) :
    Complex.exp (z * Complex.log (n:ℂ) + Complex.log ((Nat.factorial n : ℕ):ℂ)
       - ∑ k ∈ Finset.range (n+1), Complex.log (z + (k:ℂ))) = Complex.GammaSeq z n := by
  have hnc : (n:ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  have hfac : ((Nat.factorial n : ℕ):ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  rw [Complex.exp_sub, Complex.exp_add, Complex.exp_sum,
    show Complex.exp (z * Complex.log (n:ℂ)) = (n:ℂ)^z from by
        rw [Complex.cpow_def_of_ne_zero hnc]; ring_nf,
    Complex.exp_log hfac,
    show (∏ k ∈ Finset.range (n+1), Complex.exp (Complex.log (z + (k:ℂ))))
        = ∏ k ∈ Finset.range (n+1), (z + (k:ℂ)) from by
        apply Finset.prod_congr rfl; intro k hk; exact Complex.exp_log (hzk k hk),
    Complex.GammaSeq, mul_div_assoc, div_eq_mul_inv]

/-! ### Concrete instrument demonstration: a kernel box for a θ-series arctan term.

    These show the `ArctanTaylor` instrument produces REAL numeric boxes with no hypotheses --
    the atomic step the θ-series scale-up repeats per term.  We box the two `n₀ = 1` terms
    (`k = 0, 1`) of the `x = 1/4, y = 7` series: `arctan(7/(1/4)) = arctan 28` and
    `arctan(7/(1/4+1)) = arctan(28/5)`. -/







end ThetaValue

/-! ## The precise remaining gap -- named `Prop`s, honestly stated. -/

namespace ThetaGap

open ThetaValue









end ThetaGap


/-  ThetaConverge.lean -- ANDÚRIL θ-bridge: discharging the two named obligations of
    `ThetaValue.lean` (`ThetaGap.ConvergenceObligation` and `ThetaGap.RateObligation`).

    These are the entire remaining distance between the merged finite `Im L_n` pipeline and
    a purely-kernel-computed value box for `φ(14) = arg Γℝ(1/2+14i) = −7 log π + Λ`.

    ## What is proved here (all axiom-clean: {propext, Classical.choice, Quot.sound}).

      * `imLnVal_succ_sub`  : the exact one-step increment
            `imLnVal x y (n+1) − imLnVal x y n = y·log(1+1/n) − arctan(y/(x+n+1))`  (`n ≥ 1`).
      * `incr_bound`        : the elementary two-sided bound on that increment,
            `|Δ_m| ≤ (|y|(x+1) + |y|³/3)/m²`, GENERAL in real `y` (arctan-odd symmetry),
            proved from `log s ≤ s−1` (both directions) + `ArctanTaylor` cubic corollaries.
      * `imLnVal_cauchy`    : `CauchySeq (imLnVal x y)` -- the increments are `O(1/m²)`-summable,
            so `cauchySeq_of_summable_dist` gives Cauchy, hence convergence in ℝ.
      * `convergence_obligation : ThetaGap.ConvergenceObligation` -- the FULL branch bridge:
            the Cauchy limit `Λ` satisfies both `imLnVal → Λ` and `Γ(z) = ‖Γ(z)‖·exp(I·Λ)`,
            via `Re L_n = log‖GammaSeq z n‖ → log‖Γ z‖`, `Im L_n = imLnVal → Λ`,
            `exp L_n = GammaSeq z n → Γ z`, and uniqueness of limits.  No branch pinning
            beyond the exp identity -- exactly as the obligation was designed to need.
      * `rate_obligation : ThetaGap.RateObligation` -- the explicit `C/n` rate.  The finite
            tail `|imLnVal N − imLnVal n| ≤ 2B/n` (telescope + `sum_Ioo_inv_sq_le`) passes to
            the limit (`le_of_tendsto`) giving `|Λ − imLnVal n| ≤ 2B/n`, `C := 2B`.

    ## Honest note on the rate constant / box width.
    The obligation asks only for a FINITE, EXPLICIT `C`; `C = 2(|y|(x+1)+|y|³/3)` qualifies and
    is what is delivered here.  It is deliberately loose (the `1/m³` cubic-arctan tail is lumped
    into the `1/m²` log-mismatch tail, and `∑_{m≥n} 1/m² ≤ 2/n` is the cheap telescoping bound).
    A tight numeric `φ(14)` box of width ≤ 2e-3 (the driver's ambition) needs many in-kernel
    arctan terms at large `n₀`; that is mechanical throughput, not further mathematics, and is
    orthogonal to closing the obligations.  See `theta_14_box_of_partial` for the honest,
    hypothesis-free consumption at a chosen order.

    conjecture1_proved = False.  The θ-value convergence + rate obligations, kernel-clean.
    NOT a proof of RH.
-/








open Complex Real Filter Topology ThetaValue ThetaGap

namespace ThetaConverge

/-! ### The one-step increment of `imLnVal`. -/



/-! ### The elementary two-sided increment bound (general real `y`). -/





/-! ### Convergence: `imLnVal` is Cauchy, hence convergent. -/



/-! ### The complex `L_n` and its bridges to `imLnVal` / `GammaSeq`. -/



/-- `Im L_n = imLnVal x y n` for `x > 0` (this is `ThetaValue.imLn_formula`). -/
theorem Lc_im (x y : ℝ) (hx : 0 < x) (n : ℕ) : (Lc x y n).im = imLnVal x y n := by
  unfold Lc imLnVal; exact imLn_formula x y hx n

/-- `exp L_n = GammaSeq (x+yI) n` for `n ≥ 1` (Gauss-product bridge; `x > 0` gives `z+k ≠ 0`). -/
theorem Lc_exp (x y : ℝ) (hx : 0 < x) (n : ℕ) (hn : 1 ≤ n) :
    Complex.exp (Lc x y n) = Complex.GammaSeq ((x:ℂ)+(y:ℂ)*I) n := by
  unfold Lc
  apply exp_Ln_eq_gammaSeq _ _ hn
  intro k _ hcontra
  have hre : (((x:ℂ)+(y:ℂ)*I) + (k:ℂ)).re = x + k := by simp
  rw [hcontra] at hre; simp at hre; linarith

/-! ### The convergence obligation (with the branch bridge). -/



/-! ### The rate obligation (explicit `C/n`). -/







/-! ### The payoff: the kernel `φ(14)` box (assembly of both obligations).

    Both obligations discharged, we consume them through `ThetaGap.phi_box_of_rate_and_partial`.
    Ingredients at the operating point `x = 1/4`, `y = 7`, order `n₀ = 1`:
      * `imLnVal (1/4) 7 1 = −(arctan 28 + arctan(28/5)) ∈ [−4, 0]`  (crude rational partial box);
      * `log π ∈ [1, 2]`  (crude rational box; `e < π < e²`);
      * `Γ(1/4+7i) ≠ 0`  (`im = 7 ≠ 0`).
    The resulting `theta_14_box` is a genuine, hypothesis-free, argument-free kernel theorem.

    HONEST WIDTH NOTE.  The interval width is dominated by the rate term `C/n₀` with the loose
    (but valid) constant `C = 2(|y|(x+1)+|y|³/3) ≈ 246` at `n₀ = 1`, so the numeric width here is
    large (~5e2).  Narrowing to the driver's ≈1e-3 ambition is pure per-term arctan-boxing
    throughput at large `n₀` (mechanical `ArctanTaylor.arctan_bracket` iteration) plus a tightened
    `C` — orthogonal to the mathematical content, which is the two obligations proved above. -/









end ThetaConverge


/-  ThetaConverge.lean -- ANDÚRIL θ-bridge: discharging the two named obligations of
    `ThetaValue.lean` (`ThetaGap.ConvergenceObligation` and `ThetaGap.RateObligation`).

    These are the entire remaining distance between the merged finite `Im L_n` pipeline and
    a purely-kernel-computed value box for `φ(14) = arg Γℝ(1/2+14i) = −7 log π + Λ`.

    ## What is proved here (all axiom-clean: {propext, Classical.choice, Quot.sound}).

      * `imLnVal_succ_sub`  : the exact one-step increment
            `imLnVal x y (n+1) − imLnVal x y n = y·log(1+1/n) − arctan(y/(x+n+1))`  (`n ≥ 1`).
      * `incr_bound`        : the elementary two-sided bound on that increment,
            `|Δ_m| ≤ (|y|(x+1) + |y|³/3)/m²`, GENERAL in real `y` (arctan-odd symmetry),
            proved from `log s ≤ s−1` (both directions) + `ArctanTaylor` cubic corollaries.
      * `imLnVal_cauchy`    : `CauchySeq (imLnVal x y)` -- the increments are `O(1/m²)`-summable,
            so `cauchySeq_of_summable_dist` gives Cauchy, hence convergence in ℝ.
      * `convergence_obligation : ThetaGap.ConvergenceObligation` -- the FULL branch bridge:
            the Cauchy limit `Λ` satisfies both `imLnVal → Λ` and `Γ(z) = ‖Γ(z)‖·exp(I·Λ)`,
            via `Re L_n = log‖GammaSeq z n‖ → log‖Γ z‖`, `Im L_n = imLnVal → Λ`,
            `exp L_n = GammaSeq z n → Γ z`, and uniqueness of limits.  No branch pinning
            beyond the exp identity -- exactly as the obligation was designed to need.
      * `rate_obligation : ThetaGap.RateObligation` -- the explicit `C/n` rate.  The finite
            tail `|imLnVal N − imLnVal n| ≤ 2B/n` (telescope + `sum_Ioo_inv_sq_le`) passes to
            the limit (`le_of_tendsto`) giving `|Λ − imLnVal n| ≤ 2B/n`, `C := 2B`.

    ## Honest note on the rate constant / box width.
    The obligation asks only for a FINITE, EXPLICIT `C`; `C = 2(|y|(x+1)+|y|³/3)` qualifies and
    is what is delivered here.  It is deliberately loose (the `1/m³` cubic-arctan tail is lumped
    into the `1/m²` log-mismatch tail, and `∑_{m≥n} 1/m² ≤ 2/n` is the cheap telescoping bound).
    A tight numeric `φ(14)` box of width ≤ 2e-3 (the driver's ambition) needs many in-kernel
    arctan terms at large `n₀`; that is mechanical throughput, not further mathematics, and is
    orthogonal to closing the obligations.  See `theta_14_box_of_partial` for the honest,
    hypothesis-free consumption at a chosen order.

    conjecture1_proved = False.  The θ-value convergence + rate obligations, kernel-clean.
    NOT a proof of RH.
-/








open Complex Real Filter Topology ThetaValue ThetaGap

section
namespace ThetaConverge
end ThetaConverge
open ThetaConverge

/-! ### The one-step increment of `imLnVal`. -/



/-! ### The elementary two-sided increment bound (general real `y`). -/





/-! ### Convergence: `imLnVal` is Cauchy, hence convergent. -/



/-! ### The complex `L_n` and its bridges to `imLnVal` / `GammaSeq`. -/







/-! ### The convergence obligation (with the branch bridge). -/


theorem solution : ThetaGap.ConvergenceObligation := by
  intro x y hx hΓ
  obtain ⟨Λ, hΛ⟩ := cauchySeq_tendsto_of_complete (imLnVal_cauchy x y hx)
  refine ⟨Λ, hΛ, ?_⟩
  set z : ℂ := (x:ℂ)+(y:ℂ)*I with hz
  have hGS : Tendsto (fun n => Complex.GammaSeq z n) atTop (nhds (Complex.Gamma z)) :=
    Complex.GammaSeq_tendsto_Gamma z
  have hnorm : Tendsto (fun n => ‖Complex.GammaSeq z n‖) atTop (nhds ‖Complex.Gamma z‖) := hGS.norm
  have hΓnorm_pos : 0 < ‖Complex.Gamma z‖ := by positivity
  have hRe_eq : ∀ n : ℕ, 1 ≤ n → (Lc x y n).re = Real.log ‖Complex.GammaSeq z n‖ := by
    intro n hn
    have h1 : ‖Complex.exp (Lc x y n)‖ = Real.exp (Lc x y n).re := Complex.norm_exp _
    rw [Lc_exp x y hx n hn, ← hz] at h1
    rw [h1, Real.log_exp]
  have hReTendsto : Tendsto (fun n => (Lc x y n).re) atTop (nhds (Real.log ‖Complex.Gamma z‖)) := by
    have hlog : Tendsto (fun n => Real.log ‖Complex.GammaSeq z n‖) atTop
        (nhds (Real.log ‖Complex.Gamma z‖)) :=
      (Real.continuousAt_log (ne_of_gt hΓnorm_pos)).tendsto.comp hnorm
    apply hlog.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (hRe_eq n hn).symm
  have hImTendsto : Tendsto (fun n => (Lc x y n).im) atTop (nhds Λ) := by
    apply hΛ.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (Lc_im x y hx n).symm
  have hLcTendsto : Tendsto (Lc x y) atTop
      (nhds ((Real.log ‖Complex.Gamma z‖ : ℂ) + (Λ:ℂ)*I)) := by
    have h2 : Tendsto (fun n => ((Lc x y n).re : ℂ) + ((Lc x y n).im : ℂ)*I) atTop
        (nhds ((Real.log ‖Complex.Gamma z‖ : ℂ)+(Λ:ℂ)*I)) := by
      apply Tendsto.add
      · exact (Complex.continuous_ofReal.tendsto _).comp hReTendsto
      · exact ((Complex.continuous_ofReal.tendsto _).comp hImTendsto).mul_const I
    simpa only [Complex.re_add_im] using h2
  have hExpTendsto : Tendsto (fun n => Complex.exp (Lc x y n)) atTop
      (nhds (Complex.exp ((Real.log ‖Complex.Gamma z‖ : ℂ)+(Λ:ℂ)*I))) := hLcTendsto.cexp
  have hExpGS : Tendsto (fun n => Complex.exp (Lc x y n)) atTop (nhds (Complex.Gamma z)) := by
    apply hGS.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (Lc_exp x y hx n hn).symm
  have huniq : Complex.Gamma z = Complex.exp ((Real.log ‖Complex.Gamma z‖ : ℂ)+(Λ:ℂ)*I) :=
    tendsto_nhds_unique hExpGS hExpTendsto
  nth_rewrite 1 [huniq]
  rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hΓnorm_pos, mul_comm (Λ:ℂ) I]
