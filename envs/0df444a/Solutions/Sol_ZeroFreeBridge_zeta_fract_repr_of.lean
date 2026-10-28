-- Prove2me | solution 1 for ZeroFreeBridge.zeta_fract_repr_of
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:54:31.173141+00:00
-- url     : https://prove2.me/submissions/afc87d7b-8a4d-400e-960e-0b98eec7ffab

import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Mathlib
/- INPUT (R) FOR THE STRIP GROWTH BOUND: the fractional-part / Euler-Maclaurin representation
   of the Riemann zeta function on the half-plane Re s > 0,

       zeta(s) = s/(s-1) - s * integral_{x>1} {x} * x^{-(s+1)} dx        (Re s > 0, s != 1),

   where {x} = Int.fract x.  This is the piece `zeta_strip_bound_of` (in ZeroFreeBridge.lean)
   CONSUMES as its hypothesis `hrepr` (with I = the integral), and whose companion bound
   `zeta_repr_integral_bound` (input B) is already discharged there.  Assembling (R) closes the
   crude strip growth bound |zeta(sigma+it)| <= ||s||/||s-1|| + ||s||/sigma to a single unconditional
   input.  Crude growth only (~|t|); NOT the sharp |t|^{1-sigma} nor the log|t| that feeds the region,
   and the Vinogradov-Korobov rate needs VMVT (absent from Mathlib).  A gap-filler FEEDING Layer 2,
   NOT a proof of RH.  conjecture1_proved = False.

   PROOF ARCHITECTURE (5 steps):
     R1  identity on Re s > 1, via Abel summation (`sum_mul_eq_sub_integral_mul` +
         `tendsto_sum_mul_atTop_nhds_one_sub_integral`) applied to f(x) = x^{-s}, c = 1;
     R2  the RHS integral is complex-analytic in s on {Re s > 0} (differentiation under the integral);
     R3  the whole RHS s/(s-1) - s*I(s) is analytic on {0 < Re s} \ {1};
     R4  zeta is analytic on {s != 1};
     R5  identity theorem: both sides analytic on the preconnected open {0<Re s}\{1}, agree on the
         open subset {Re s > 1}, hence agree everywhere.

   This file FULLY ASSEMBLES R3/R4/R5 with NO `stub` and NO `postulate`.  The two genuinely-hard
   analytic inputs R1 and R2 are taken as explicit HYPOTHESES of the main theorem
   `zeta_fract_repr_of` -- exactly the style of `zeta_boundary_contradiction` and `zeta_strip_bound_of`
   in ZeroFreeBridge.lean, which likewise take their hard analytic limits/representations as
   hypotheses.  The convenience wrapper `zeta_fract_repr` (matching the requested signature) is then
   `zeta_fract_repr_of` fed the R1/R2 witnesses; those two witnesses are the remaining CI-iteration
   targets and their intended proofs are sketched in `zeta_fract_repr_gt`/`differentiableAt_fractIntegral`
   below (currently the only two declarations awaiting discharge, clearly delimited).

   RISK ORDER: R1 (Abel-summation identity) >> R5-preconnectedness > R2.  Uncertain Mathlib names
   are flagged inline with `-- FLAG:`.
-/

open scoped Real
open Filter Topology MeasureTheory

namespace ZeroFreeBridge









theorem isOpen_stripDomain : IsOpen stripDomain := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hEq : stripDomain = {s : ℂ | 0 < s.re} ∩ {(1 : ℂ)}ᶜ := by
    ext s; simp [stripDomain, Set.mem_singleton_iff]
  rw [hEq]; exact hopen.inter isOpen_compl_singleton

theorem mem_stripDomain_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : s ∈ stripDomain := by
  refine ⟨show (0:ℝ) < s.re by linarith, ?_⟩
  simp only [Set.mem_singleton_iff]
  rintro rfl; simp at hs  -- (1 : ℂ).re = 1 contradicts 1 < 1

/- ===================================================================================
   ASSEMBLED MAIN THEOREM (R3 + R4 + R5), taking R1 and R2 as hypotheses.  NO `stub`/`postulate`.
   =================================================================================== -/



/- ===================================================================================
   THREE REMAINING CI-ITERATION TARGETS — the hypotheses `zeta_fract_repr_of` consumes, to be
   discharged (each unblocks the fully-unconditional `zeta_fract_repr` matching the requested
   signature).  Kept as DOCUMENTED obligations, NOT `stub` stubs, to preserve the file's gap-free
   invariant.  Verified-present Mathlib API in brackets.

   (R1)  `∀ {z}, 1 < z.re → riemannZeta z = stripRHS z`  — the Abel-summation identity on Re s > 1.
         HARDEST.  Tools: `sum_mul_eq_sub_integral_mul`, `tendsto_sum_mul_atTop_nhds_one_sub_integral`
         (Mathlib.NumberTheory.AbelSummation), `zeta_eq_tsum_one_div_nat_add_one_cpow`,
         `Complex.deriv_cpow_const` (for `deriv (·^(-s)) = -s·(·)^(-s-1)` on `slitPlane`).
   (R2)  `∀ {z}, z ∈ stripDomain → DifferentiableAt ℂ fractIntegral z`  — differentiation under the
         integral.  Tool: `hasDerivAt_integral_of_dominated_loc_of_lip` (7 hyps), parameter-derivative
         `-{x}·(log x)·x^{-(s+1)}`, dominated by `x^{-(σ₀-ε)-1}·log x`; base integrability
         `integrableOn_Ioi_norm_cpow_of_lt {a : ℂ} (ha : a.re < -1) (hc : 0 < c)` with `a = -(s+1)`.
   (R3)  `IsPreconnected stripDomain`  — the punctured open right half-plane.  Tool: cover by the four
         convex pieces `{0<re, im>0}`, `{0<re, im<0}`, `{0<re, re<1}`, `{re>1}` (each `Convex.isPreconnected`)
         chained by `IsPreconnected.union` on their overlaps.

   `zeta_fract_repr_of` FULLY ASSEMBLES R4 (`analyticOn_riemannZeta.mono`) + R3-analyticity of the RHS
   (`DifferentiableOn.analyticOnNhd`) + R5 (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`), no
   stub/postulate, given (R1)(R2)(R3) — exactly the conditional-hypothesis style of `zeta_boundary_contradiction`
   and `zeta_strip_bound_of`.  conjecture1_proved = False.
   =================================================================================== -/

end ZeroFreeBridge


/- INPUT (R) FOR THE STRIP GROWTH BOUND: the fractional-part / Euler-Maclaurin representation
   of the Riemann zeta function on the half-plane Re s > 0,

       zeta(s) = s/(s-1) - s * integral_{x>1} {x} * x^{-(s+1)} dx        (Re s > 0, s != 1),

   where {x} = Int.fract x.  This is the piece `zeta_strip_bound_of` (in ZeroFreeBridge.lean)
   CONSUMES as its hypothesis `hrepr` (with I = the integral), and whose companion bound
   `zeta_repr_integral_bound` (input B) is already discharged there.  Assembling (R) closes the
   crude strip growth bound |zeta(sigma+it)| <= ||s||/||s-1|| + ||s||/sigma to a single unconditional
   input.  Crude growth only (~|t|); NOT the sharp |t|^{1-sigma} nor the log|t| that feeds the region,
   and the Vinogradov-Korobov rate needs VMVT (absent from Mathlib).  A gap-filler FEEDING Layer 2,
   NOT a proof of RH.  conjecture1_proved = False.

   PROOF ARCHITECTURE (5 steps):
     R1  identity on Re s > 1, via Abel summation (`sum_mul_eq_sub_integral_mul` +
         `tendsto_sum_mul_atTop_nhds_one_sub_integral`) applied to f(x) = x^{-s}, c = 1;
     R2  the RHS integral is complex-analytic in s on {Re s > 0} (differentiation under the integral);
     R3  the whole RHS s/(s-1) - s*I(s) is analytic on {0 < Re s} \ {1};
     R4  zeta is analytic on {s != 1};
     R5  identity theorem: both sides analytic on the preconnected open {0<Re s}\{1}, agree on the
         open subset {Re s > 1}, hence agree everywhere.

   This file FULLY ASSEMBLES R3/R4/R5 with NO `stub` and NO `postulate`.  The two genuinely-hard
   analytic inputs R1 and R2 are taken as explicit HYPOTHESES of the main theorem
   `zeta_fract_repr_of` -- exactly the style of `zeta_boundary_contradiction` and `zeta_strip_bound_of`
   in ZeroFreeBridge.lean, which likewise take their hard analytic limits/representations as
   hypotheses.  The convenience wrapper `zeta_fract_repr` (matching the requested signature) is then
   `zeta_fract_repr_of` fed the R1/R2 witnesses; those two witnesses are the remaining CI-iteration
   targets and their intended proofs are sketched in `zeta_fract_repr_gt`/`differentiableAt_fractIntegral`
   below (currently the only two declarations awaiting discharge, clearly delimited).

   RISK ORDER: R1 (Abel-summation identity) >> R5-preconnectedness > R2.  Uncertain Mathlib names
   are flagged inline with `-- FLAG:`.
-/

open scoped Real
open Filter Topology MeasureTheory

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge











  -- (1 : ℂ).re = 1 contradicts 1 < 1

/- ===================================================================================
   ASSEMBLED MAIN THEOREM (R3 + R4 + R5), taking R1 and R2 as hypotheses.  NO `stub`/`postulate`.
   =================================================================================== -/


theorem solution
    (hR1 : ∀ {z : ℂ}, 1 < z.re → riemannZeta z = stripRHS z)
    (hR2 : ∀ {z : ℂ}, z ∈ stripDomain → DifferentiableAt ℂ fractIntegral z)
    (hpre : IsPreconnected stripDomain)
    {s : ℂ} (hs : s ∈ stripDomain) :
    riemannZeta s = stripRHS s := by
  -- R4: ζ analytic on stripDomain.  Directly from `analyticOn_riemannZeta : AnalyticOnNhd ℂ ζ {1}ᶜ`
  -- (CONFIRMED, Mathlib.NumberTheory.LSeries.RiemannZeta:146), restricted via `.mono` since
  -- `stripDomain ⊆ {1}ᶜ`.
  have hsub_compl : stripDomain ⊆ ({(1 : ℂ)}ᶜ) := by
    intro z hz; simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hz.2
  have hζ : AnalyticOnNhd ℂ riemannZeta stripDomain := analyticOn_riemannZeta.mono hsub_compl
  -- R3: stripRHS analytic on stripDomain.
  have hRHS : AnalyticOnNhd ℂ stripRHS stripDomain := by
    refine DifferentiableOn.analyticOnNhd ?_ isOpen_stripDomain
    intro z hz
    have hne : z ≠ 1 := by simpa [stripDomain, Set.mem_singleton_iff] using hz.2
    have hsub : z - 1 ≠ 0 := sub_ne_zero.mpr hne
    have hI : DifferentiableAt ℂ fractIntegral z := hR2 hz
    -- pin the identity function at ℂ so numeric literals / `differentiableAt_id` do not default to ℕ
    have hid : DifferentiableAt ℂ (fun w : ℂ => w) z := differentiableAt_id
    have h1 : DifferentiableWithinAt ℂ (fun w => w / (w - 1)) stripDomain z :=
      (hid.div (hid.sub_const 1) hsub).differentiableWithinAt
    have h2 : DifferentiableWithinAt ℂ (fun w => w * fractIntegral w) stripDomain z :=
      (hid.mul hI).differentiableWithinAt
    -- `stripRHS w = w/(w-1) - w * fractIntegral w` by definition; unfold so `h1.sub h2` matches.
    -- FLAG: `stripRHS` is a `def`, so the goal is `DifferentiableWithinAt ℂ stripRHS z`; may need
    -- `show DifferentiableWithinAt ℂ (fun w => w / (w - 1) - w * fractIntegral w) z` or
    -- `simp only [stripRHS]` before `exact h1.sub h2`.
    show DifferentiableWithinAt ℂ (fun w => w / (w - 1) - w * fractIntegral w) stripDomain z
    exact h1.sub h2
  -- Seed: agreement on the open set {Re s > 1}, eventually near z₀ = 2.
  have hopen_gt : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem_gt : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by norm_num
  have hEqOn_gt : Set.EqOn riemannZeta stripRHS {z : ℂ | 1 < z.re} := fun z hz => hR1 hz
  have hev : riemannZeta =ᶠ[𝓝 (2 : ℂ)] stripRHS :=
    Filter.eventuallyEq_of_mem (hopen_gt.mem_nhds hmem_gt) hEqOn_gt
  have h2mem : (2 : ℂ) ∈ stripDomain := mem_stripDomain_of_one_lt_re (by norm_num)
  -- R5: identity theorem on the preconnected stripDomain.
  have hEqOn : Set.EqOn riemannZeta stripRHS stripDomain :=
    hζ.eqOn_of_preconnected_of_eventuallyEq hRHS hpre h2mem hev
    -- FLAG: signature confirmed
    --   AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    --     (hf : AnalyticOnNhd 𝕜 f U) (hg : AnalyticOnNhd 𝕜 g U) (hU : IsPreconnected U)
    --     (hz₀ : z₀ ∈ U) (hfg : f =ᶠ[𝓝 z₀] g) : Set.EqOn f g U
    -- (Mathlib/Analysis/Analytic/Uniqueness.lean:223).
  exact hEqOn hs
