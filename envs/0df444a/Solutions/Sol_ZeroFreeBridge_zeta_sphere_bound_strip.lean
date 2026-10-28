-- Prove2me | solution 1 for ZeroFreeBridge.zeta_sphere_bound_strip
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:57:02.945932+00:00
-- url     : https://prove2.me/submissions/ed1be725-9200-4748-b5a2-a91e5f57cd6d

import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
import Theorems.Thm_ZeroFreeBridge_differentiableAt_fractIntegral
import Theorems.Thm_ZeroFreeBridge_isPreconnected_stripDomain
import Theorems.Thm_ZeroFreeBridge_zeta_fract_repr_of
import Theorems.Thm_ZeroFreeBridge_zeta_repr_R1
import Theorems.Thm_ZeroFreeBridge_zeta_repr_integral_bound
/- UNCONDITIONAL strip representation, assembled from the discharged inputs R1 + R2 + R3.

     riemannZeta s = s/(s-1) - s · ∫_{x>1} {x} x^{-(s+1)} dx = stripRHS s,   for s ∈ {0<Re s}\{1}.

   All three inputs of `zeta_fract_repr_of` (the identity-theorem assembly in StripRepr) are now
   kernel-verified:
     R1  `zeta_repr_R1`                    (StripReprR1) -- Abel-summation identity on Re s > 1,
     R2  `differentiableAt_fractIntegral`  (StripReprR2) -- differentiation under the integral,
     R3  `isPreconnected_stripDomain`      (StripReprR3) -- 4-convex-cover preconnectedness.
   Feeding them to `zeta_fract_repr_of` gives the fully-UNCONDITIONAL strip representation on the
   punctured right half-plane.  Together with `zeta_repr_integral_bound` (input B) and
   `zeta_strip_bound_of` (both in ZeroFreeBridge), this closes the crude strip growth bound
   |ζ(σ+it)| ≤ ‖s‖/‖s-1‖ + ‖s‖/σ to a single unconditional input.  Crude growth only (~|t|); NOT
   the sharp |t|^{1-σ} nor the log|t| region rate (which needs the Vinogradov-Korobov machinery
   absent from Mathlib).  A gap-filler FEEDING Layer 2, NOT a proof of RH.  conjecture1_proved = False.
-/




namespace ZeroFreeBridge

/-- The UNCONDITIONAL fractional-part strip representation of `riemannZeta` on the punctured right
    half-plane `stripDomain = {s | 0 < Re s} \ {1}`, assembled from the discharged R1/R2/R3 via
    `zeta_fract_repr_of`.  This is the input (R) that `zeta_strip_bound_of` consumes. -/
theorem zeta_fract_repr {s : ℂ} (hs : s ∈ stripDomain) : riemannZeta s = stripRHS s :=
  zeta_fract_repr_of
    (fun {z} hz => zeta_repr_R1 hz)
    (fun {z} hz => differentiableAt_fractIntegral (show (0 : ℝ) < z.re from hz.1))
    isPreconnected_stripDomain hs

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
theorem zeta_strip_bound_of {s I : ℂ}
    (hrepr : riemannZeta s = s / (s - 1) - s * I) (hI : ‖I‖ ≤ 1 / s.re) :
    ‖riemannZeta s‖ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ / s.re := by
  rw [hrepr]
  calc ‖s / (s - 1) - s * I‖
      ≤ ‖s / (s - 1)‖ + ‖s * I‖ := norm_sub_le _ _
    _ = ‖s‖ / ‖s - 1‖ + ‖s‖ * ‖I‖ := by rw [norm_div, norm_mul]
    _ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ * (1 / s.re) := by
        have := mul_le_mul_of_nonneg_left hI (norm_nonneg s); linarith
    _ = ‖s‖ / ‖s - 1‖ + ‖s‖ / s.re := by rw [mul_one_div]



end ZeroFreeBridge


/- PHASE 2: the UNCONDITIONAL crude strip growth bound for `riemannZeta`.

     ‖riemannZeta s‖ ≤ ‖s‖/‖s-1‖ + ‖s‖/Re s,     for s ∈ stripDomain = {0 < Re s} \ {1}.

   Assembled from the two now-discharged inputs of `zeta_strip_bound_of` (ZeroFreeBridge):
     input (R)  `zeta_fract_repr`          (StripReprAssembled) -- the fractional-part representation
                                            `ζ(s) = s/(s-1) - s·fractIntegral s`, and
     input (B)  `zeta_repr_integral_bound` (ZeroFreeBridge)     -- `‖fractIntegral s‖ ≤ 1/Re s`.
   `zeta_repr_integral_bound`'s inline integrand is DEFINITIONALLY `fractIntegral s` (StripRepr's def),
   and `stripRHS s` unfolds to `s/(s-1) - s·fractIntegral s`, so the two inputs slot straight in.

   This closes Layer 2's crude magnitude tier to a single UNCONDITIONAL theorem.  Crude growth only
   (grows like `|t|`); NOT the sharp `|t|^{1-σ}` nor the `log|t|` that feeds the zero-free region, and
   the Vinogradov-Korobov rate needs VMVT (absent from Mathlib).  Feeds Layer 3 (the region), NOT a
   proof of RH.  conjecture1_proved = False.
-/



namespace ZeroFreeBridge

/-- The UNCONDITIONAL crude strip growth bound: on the punctured right half-plane,
    `‖ζ(s)‖ ≤ ‖s‖/‖s-1‖ + ‖s‖/Re s`.  Assembled from input (R) `zeta_fract_repr` and input (B)
    `zeta_repr_integral_bound` via `zeta_strip_bound_of`. -/
theorem zeta_strip_bound {s : ℂ} (hs : s ∈ stripDomain) :
    ‖riemannZeta s‖ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ / s.re := by
  have hs0 : 0 < s.re := hs.1
  exact zeta_strip_bound_of (I := fractIntegral s) (zeta_fract_repr hs)
    (zeta_repr_integral_bound hs0)

end ZeroFreeBridge


/- PHASE 4 (dVP frontier, item 3 input — strip-capable Jensen zero count): the version of
   `zeta_zero_count_unconditional` (`DlvpZetaDisk`) that survives the disk DIPPING BELOW `Re = 1`.

   The count `∑ divisor ≤ log(M/‖ζ c‖)/log(R/r)` (`zeta_zero_count_le`) takes the boundary bound `M`
   as a HYPOTHESIS and only needs `1 < c.re` at the CENTER plus `1 ∉ closedBall c |R|` — ζ is
   analytic on ANY disk avoiding `s = 1`, even one reaching `Re < 1`.  The original
   `zeta_zero_count_unconditional` supplies `M` via `zeta_sphere_bound` (`Re > 1`), forcing
   `|R| + 1 < c.re`.  Here we supply `M` via `zeta_strip_bound` (valid on the FULL strip
   `Re > 0`, `s ≠ 1`), so the disk may enclose a nontrivial zero `ρ₀` (`Re < 1`).

   This delivers the `O(L)` zero-count bound `∑ |divisor| ≤ Ccount·L` that `hAL_arith` (`DlvpHALArith`)
   consumes.  conjecture1_proved = False (NOT a proof of RH).
-/



open Complex Metric MeromorphicOn

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge


theorem solution (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hRlt : R < c.re - 1/2) (himc : R + 2 ≤ |c.im|)
    {z : ℂ} (hz : z ∈ sphere c R) :
    ‖riemannZeta z‖ ≤ (‖c‖ + R) / (|c.im| - R) + (‖c‖ + R) / (c.re - R) := by
  have hnorm : ‖z - c‖ = R := by rw [← Complex.dist_eq]; exact Metric.mem_sphere.mp hz
  have hzre : c.re - R ≤ z.re := by
    have h1 : |(z - c).re| ≤ ‖z - c‖ := Complex.abs_re_le_norm _
    rw [hnorm] at h1
    have h2 : (z - c).re = z.re - c.re := by simp
    rw [h2] at h1; have := (abs_le.mp h1).1; linarith
  have hd_re : (0 : ℝ) < c.re - R := by linarith
  have hzrepos : (0 : ℝ) < z.re := by linarith
  have himz : |c.im| - R ≤ |z.im| := by
    have h1 : |(z - c).im| ≤ ‖z - c‖ := Complex.abs_im_le_norm _
    rw [hnorm] at h1
    have h2 : (z - c).im = z.im - c.im := by simp
    rw [h2] at h1
    have h4 : |c.im| - |z.im| ≤ |c.im - z.im| := abs_sub_abs_le_abs_sub c.im z.im
    rw [abs_sub_comm c.im z.im] at h4; linarith
  have hd_im : (0 : ℝ) < |c.im| - R := by linarith
  have hzne1 : z ≠ 1 := by
    intro h; rw [h] at himz; simp only [Complex.one_im, abs_zero] at himz; linarith
  have hmem : z ∈ stripDomain := ⟨hzrepos, by simpa using hzne1⟩
  have hznorm : ‖z‖ ≤ ‖c‖ + R := by
    calc ‖z‖ ≤ ‖c‖ + ‖z - c‖ := by simpa using norm_le_norm_add_norm_sub' z c
      _ = ‖c‖ + R := by rw [hnorm]
  have hz1_lb : |c.im| - R ≤ ‖z - 1‖ := by
    calc |c.im| - R ≤ |z.im| := himz
      _ = |(z - 1).im| := by rw [Complex.sub_im]; simp
      _ ≤ ‖z - 1‖ := Complex.abs_im_le_norm _
  have hd1 : (0 : ℝ) < ‖z - 1‖ := by linarith
  have hsb := zeta_strip_bound hmem
  have hU1 : ‖z‖ / ‖z - 1‖ ≤ (‖c‖ + R) / (|c.im| - R) := by gcongr
  have hU2 : ‖z‖ / z.re ≤ (‖c‖ + R) / (c.re - R) := by gcongr
  linarith [hsb, hU1, hU2]
