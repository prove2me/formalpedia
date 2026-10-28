-- Prove2me | solution 1 for ZeroFreeBridge.zeta_logDeriv_comb_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:42:10.505127+00:00
-- url     : https://prove2.me/submissions/80cc926f-92ac-4494-a725-f4d0206e0dac

import Mathlib
/- THE BRIDGE: 3 Re L(s) + 4 Re L(s+it) + Re L(s+2it) >= 0 for Re s > 1,
   where L(Lambda, .) = -zeta'/zeta is the von Mangoldt L-series.
   The Mertens nonnegative-cosine certificate (3 + 4 cos + cos 2 = 2(1+cos)^2, from
   TrigNonneg), proven in-kernel to meet the actual Dirichlet series of -zeta'/zeta.
   This is the KEY INEQUALITY of the classical zero-free region -- the positivity that,
   combined with an (unformalized, research-scale) zeta growth bound, yields
   zeta(s) != 0 for Re s > 1 - c/log|t|.  A certificate FEEDING the region, NOT the
   region and NOT a proof of RH.  conjecture1_proved = False. -/

open scoped Real
open Filter Topology MeasureTheory

namespace ZeroFreeBridge

/- ===================================================================================
   RESIDUE OF THE LOGARITHMIC DERIVATIVE = ORDER.  A general complex-analysis lemma
   (NOT RH-specific): for f meromorphic at z0 of order n (a zero if n>0, a pole if n<0),
   (z - z0) * logDeriv f z -> n as z -> z0 within the punctured neighbourhood.
   Mathlib v4.32.0 has ONLY the analytic simple-zero case
   (AnalyticAt.tendsto_mul_logDeriv_simple_zero, n=1); the general-order version is a
   genuine gap here (present only on Mathlib master).  Built from the local factorization
   meromorphicOrderAt_eq_int_iff  (f =ᶠ (z-z0)^n • g, g analytic, g z0 != 0).
   =================================================================================== -/









theorem mertens_three_four_one (θ : ℝ) : 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  have h := Real.cos_two_mul θ; nlinarith [h, sq_nonneg (Real.cos θ + 1)]

theorem cpow_re (n : ℕ) (hn : 1 ≤ n) (s : ℂ) :
    (((n : ℂ)) ^ (-s)).re = (n : ℝ) ^ (-s.re) * Real.cos (s.im * Real.log n) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hre : ((↑(Real.log (n : ℝ)) : ℂ) * (-s)).re = -s.re * Real.log n := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  have him : ((↑(Real.log (n : ℝ)) : ℂ) * (-s)).im = -(s.im * Real.log n) := by
    simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log, Complex.exp_re, hre, him,
      Real.cos_neg, show -s.re * Real.log (n : ℝ) = Real.log (n : ℝ) * -s.re from by ring,
      ← Real.rpow_def_of_pos hnpos]

theorem term_re (n : ℕ) (hn : 1 ≤ n) (s : ℂ) :
    (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) s n).re
      = ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-s.re) * Real.cos (s.im * Real.log n) := by
  rw [LSeries.term_of_ne_zero (by omega : n ≠ 0), div_eq_mul_inv, ← Complex.cpow_neg,
      Complex.re_ofReal_mul, cpow_re n hn s, mul_assoc]

theorem term_comb_nonneg (n : ℕ) (σ t : ℝ) :
    0 ≤ 3 * (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (σ : ℂ) n).re
      + 4 * (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I) n).re
      + (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) n).re := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp [LSeries.term]
  · have hn : 1 ≤ n := hpos
    rw [term_re n hn (σ : ℂ), term_re n hn ((σ : ℂ) + (t : ℂ) * Complex.I),
        term_re n hn ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_mul, sub_zero, add_zero, zero_add, Real.cos_zero]
    rw [mul_assoc (2 : ℝ) t (Real.log (n : ℝ))]
    have hp : (0:ℝ) < (n:ℝ) ^ (-σ) := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
    have hM : (0:ℝ) ≤ ArithmeticFunction.vonMangoldt n * (n:ℝ) ^ (-σ) :=
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg hp.le
    nlinarith [mul_nonneg hM (mertens_three_four_one (t * Real.log n)), hM]

theorem vonMangoldt_re_comb_nonneg (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ 3 * (LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (σ : ℂ)).re
      + 4 * (LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I)).re
      + (LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re := by
  have hf : Summable (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (σ : ℂ)) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have hg : Summable (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have hh : Summable (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have hA : Summable (fun n => (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (σ : ℂ) n).re) := hf.map Complex.reCLM Complex.reCLM.cont
  have hB : Summable (fun n => (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I) n).re) := hg.map Complex.reCLM Complex.reCLM.cont
  have hC : Summable (fun n => (LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) n).re) := hh.map Complex.reCLM Complex.reCLM.cont
  show 0 ≤ 3 * (∑' n, LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (σ : ℂ) n).re
      + 4 * (∑' n, LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I) n).re
      + (∑' n, LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) n).re
  rw [Complex.re_tsum hf, Complex.re_tsum hg, Complex.re_tsum hh,
      (((hA.hasSum.mul_left 3).add (hB.hasSum.mul_left 4)).add hC.hasSum).tsum_eq.symm]
  exact tsum_nonneg (fun n => term_comb_nonneg n σ t)

/- The same positivity, restated LITERALLY about zeta's logarithmic derivative -zeta'/zeta,
   via Mathlib's  LSeries(vonMangoldt) s = -zeta'(s)/zeta(s)  (Re s > 1).  This is the exact
   form the classical zero-free-region argument uses: 3 Re(-zeta'/zeta)(sigma) + 4 Re(...)(sigma+it)
   + Re(...)(sigma+2it) >= 0.  Still NOT a proof of RH -- the region needs the log-derivative ->
   product step and the zeta growth bound (both unformalized, research-scale). -/


/- ===================================================================================
   THE BRIDGE-POWERED BOUNDARY CONTRADICTION (classical de la Vallee Poussin core).
   The Mertens positivity 3 Re(-zeta'/zeta)(sigma) + 4 Re(...)(sigma+it) + Re(...)(sigma+2it) >= 0
   (proven above), multiplied by (sigma-1) > 0 and taken to sigma -> 1+, forces
   3*1 - 4k - k' >= 0, where +1 is the residue of -zeta'/zeta at the simple pole s=1 and
   -k, -k' are the residues at 1+it, 1+2it (k = order of a zero at 1+it, k' >= 0 at 1+2it).
   With k >= 1 this is 3 - 4k - k' <= -1 < 0, impossible: so zeta has NO zero of order >= 1
   at 1+it.  This is exactly how the classical zero-free-region boundary (zeta(1+it) != 0)
   is forced by the 3-4-1 inequality -- routed here through -zeta'/zeta (a different internal
   path from Mathlib's product-route riemannZeta_ne_zero_of_one_le_re).

   The three residue LIMITS are taken as hypotheses (hpole/hz1/hz2): each is the real-line
   restriction of  residue_logDeriv  (proven above: (z-z0)*logDeriv f z -> order) applied to
   zeta at 1, 1+it, 1+2it -- given zeta's meromorphy/orders there.  Discharging them fully needs
   zeta's simple-pole handle at s=1 (a v4.32.0 API gap, via completedRiemannZeta) + order
   extraction + the .re/real-ray plumbing.  conjecture1_proved = False; NOT a proof of RH --
   this is the boundary (c=0) edge of the classical region, which Mathlib already has. -/


/- ===================================================================================
   IMPROVED ZERO-FREE CERTIFICATE (degree 3).  The de la Vallee Poussin polynomial
   3 + 4cos + cos2 = 2(1+cos)^2 is NOT optimal.  Optimizing the leading-order zero-free
   functional  F(P) = (sqrt a_1 - sqrt a_0)^2 / sum_{k>=1} a_k  over NONNEGATIVE cosine
   polynomials (a_k >= 0) is exactly the Mossinghoff-Trudgian 2015 program (J. Number
   Theory 157; improved region constant R_0 = 5.573412).  The (1+cos)^n family gives clean
   Fejer-Riesz certificates capturing most of the gain.  Here n = 3:
       20 + 30 cos + 12 cos2 + 2 cos3  =  8 (1 + cos)^3  >= 0,   a_1 = 30 > a_0 = 20,
   with F = 0.02296 vs 0.01436 for de la Vallee Poussin (1.60x wider region, leading order).
   Generator UNTRUSTED, Lean kernel sole arbiter.  This still only FEEDS the classical region
   CONSTANT -- it improves the constant, NOT the Vinogradov-Korobov rate 1/(log t)^{2/3}, and
   is NOT a proof of RH.  conjecture1_proved = False.
   =================================================================================== -/











/- ===================================================================================
   GENERAL DEGREE-n CERTIFICATE.  Everything above is the n=2 (Mertens) and n=3 instances of
   a single statement: ANY pointwise-nonnegative cosine polynomial
       P(φ) = sum_{k < N} a k * cos (k φ) >= 0
   yields the zero-free-region positivity on -zeta'/zeta.  This subsumes the (1+cos)^n family
   (`one_add_cos_pow_nonneg`, whose cosine coefficients are all >= 0) and every Mossinghoff-Trudgian
   optimal polynomial -- the whole certificate cone, at once, for arbitrary degree.
   Generator UNTRUSTED, Lean kernel sole arbiter.  Still FEEDS the classical region constant only,
   NOT the Vinogradov-Korobov rate, NOT a proof of RH.  conjecture1_proved = False.
   =================================================================================== -/







/- ===================================================================================
   THE HINGE.  The general positivity feeds the classical boundary conclusion: ANY admissible
   certificate forces `ζ(1+it) ≠ 0`.  "Admissible" = coefficients `a_k ≥ 0` (residue upper bounds),
   pointwise-nonnegative cosine polynomial (positivity), and the single inequality `a 0 < a 1`.
   That last condition is EXACTLY the hinge: the pole residue `+a 0` at `s=1` loses to a zero
   residue `-a 1·m` (m ≥ 1) at `1+it` precisely when `a 1 > a 0`.  The Fejer bound `a_1 < 2 a_0`
   caps how far this can be pushed.  Still the c=0 boundary (`ζ(1+it) ≠ 0` is already in Mathlib),
   NOT a proof of RH.  conjecture1_proved = False.
   =================================================================================== -/


/- ===================================================================================
   MAGNITUDE LAYER (Layer 2) -- first brick.  The reassessment
   (docs/RH_ZERO_FREE_REASSESSMENT_2026-08-30) located the frontier BEYOND the (Fejer-capped)
   positivity layer in the MAGNITUDE bound |zeta(sigma+it)|.  This is the sigma>1 BASE CASE: the
   elementary Dirichlet-triangle bound  |zeta(s)| <= sum_n (n+1)^{-Re s} = zeta(Re s).  It is NOT
   the frontier -- the zero-free-region improvement needs |zeta| growth INSIDE the critical strip
   (|zeta(sigma+it)| << |t|^{1-sigma}, or << log|t| near sigma=1), which needs Euler-Maclaurin / the
   {x}-integral continuation (the harder next piece, Mathlib-API dependent).  This brick is the honest
   base: |zeta| is finite for sigma>1, and the RHS blows up like 1/(sigma-1) as sigma->1+, which is
   exactly why the strip needs the finer bound.  A different KIND of object from the positivity certs
   (a magnitude bound, not a positivity), opening Layer 2.  conjecture1_proved = False. -/





/- The STRIP growth bound, reduced to its two analytic inputs.  Research (agentic campaign,
   docs/RH_ZERO_FREE_REASSESSMENT §8) confirmed Mathlib v4.32.0 has NO strip |zeta| bound and NO
   complex fractional-part integral representation, so the crude strip growth bound
       |zeta(sigma+it)| <= ||s||/||s-1|| + ||s||/sigma   (<< |t|, for 0 < sigma < 1)
   must be assembled from two analytic facts still to be formalized (the identified remaining work):
     (R) the representation  zeta(s) = s/(s-1) - s * I  with  I = integral_1^inf {x} x^{-s-1} dx
         (Re s > 0; via Abel summation + the identity theorem -- a genuine Mathlib gap-filler), and
     (B) the integral bound  ||I|| <= 1/Re s  (from |{x}| <= 1 and integral_1^inf x^{-sigma-1} = 1/sigma).
   This theorem does the (high-confidence) ASSEMBLY, taking (R),(B) as hypotheses -- exactly the style
   of `zeta_boundary_contradiction`, which likewise takes its analytic limits as hypotheses.  Crude
   growth only (~|t|), NOT the sharp |t|^{1-sigma} nor the log|t| that feeds the region; and the VK rate
   needs VMVT (absent from Mathlib).  conjecture1_proved = False. -/




end ZeroFreeBridge


/- THE BRIDGE: 3 Re L(s) + 4 Re L(s+it) + Re L(s+2it) >= 0 for Re s > 1,
   where L(Lambda, .) = -zeta'/zeta is the von Mangoldt L-series.
   The Mertens nonnegative-cosine certificate (3 + 4 cos + cos 2 = 2(1+cos)^2, from
   TrigNonneg), proven in-kernel to meet the actual Dirichlet series of -zeta'/zeta.
   This is the KEY INEQUALITY of the classical zero-free region -- the positivity that,
   combined with an (unformalized, research-scale) zeta growth bound, yields
   zeta(s) != 0 for Re s > 1 - c/log|t|.  A certificate FEEDING the region, NOT the
   region and NOT a proof of RH.  conjecture1_proved = False. -/

open scoped Real
open Filter Topology MeasureTheory

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge

/- ===================================================================================
   RESIDUE OF THE LOGARITHMIC DERIVATIVE = ORDER.  A general complex-analysis lemma
   (NOT RH-specific): for f meromorphic at z0 of order n (a zero if n>0, a pole if n<0),
   (z - z0) * logDeriv f z -> n as z -> z0 within the punctured neighbourhood.
   Mathlib v4.32.0 has ONLY the analytic simple-zero case
   (AnalyticAt.tendsto_mul_logDeriv_simple_zero, n=1); the general-order version is a
   genuine gap here (present only on Mathlib master).  Built from the local factorization
   meromorphicOrderAt_eq_int_iff  (f =ᶠ (z-z0)^n • g, g analytic, g z0 != 0).
   =================================================================================== -/



















/- The same positivity, restated LITERALLY about zeta's logarithmic derivative -zeta'/zeta,
   via Mathlib's  LSeries(vonMangoldt) s = -zeta'(s)/zeta(s)  (Re s > 1).  This is the exact
   form the classical zero-free-region argument uses: 3 Re(-zeta'/zeta)(sigma) + 4 Re(...)(sigma+it)
   + Re(...)(sigma+2it) >= 0.  Still NOT a proof of RH -- the region needs the log-derivative ->
   product step and the zeta growth bound (both unformalized, research-scale). -/
theorem solution (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ 3 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
      + 4 * (-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) / riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)).re
      + (-deriv riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) / riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re := by
  have e1 : -deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)
      = LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (σ : ℂ) :=
    (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hσ)).symm
  have e2 : -deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) / riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
      = LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I) :=
    (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hσ)).symm
  have e3 : -deriv riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) / riemannZeta ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)
      = LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) :=
    (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hσ)).symm
  rw [e1, e2, e3]
  exact vonMangoldt_re_comb_nonneg σ t hσ
