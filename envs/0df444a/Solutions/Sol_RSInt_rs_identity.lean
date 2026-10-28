-- Prove2me | solution 1 for RSInt.rs_identity
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:30:49.617359+00:00
-- url     : https://prove2.me/submissions/32f21093-59bb-4464-8aff-54ca2673f4eb

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_differentiableAt_rsChi
import Theorems.Thm_RSInt_differentiable_rsA
import Theorems.Thm_RSInt_differentiable_rsB
import Theorems.Thm_RSInt_rs_identity_re_gt_two
/-  RS_Kernel.lean -- lane RS, ANDURIL brick B2 (the Riemann-Siegel integral), part 2:
    Riemann's kernels, their difference equations, Gaussian bounds, the Fresnel line integral,
    the pole-crossing lemmas and the Mordell closed form.

    Mathlib-only (imports `RS_Strip` only).

    ## The kernels

        rsD x = e^{i pi x} - e^{-i pi x}          (= 2 i sin(pi x); zeros exactly at the integers)
        rsG x = e^{ i pi x^2} / rsD x              (Riemann's kernel of the zeta integral)
        rsH x = e^{-i pi x^2} / rsD x              (the kernel of the chi-side integral)

    ## Contents (no `sorry`, no `native_decide`, no new axioms)

      * `rsD_eq_zero_iff`, `rsD_add_one`, `rsG_add_one`, `rsH_add_one` : zeros and the difference
        equations  rsG(x+1) = rsG x + e^{i pi (x^2+x)},  rsH(x+1) = rsH x - e^{-i pi (x^2+x)}.
      * `norm_rsG_le`, `norm_rsH_le` : on a slanted strip, away from the real axis (|Im x| >= 1), the
        kernels are bounded by exp(-2 pi (Im x)^2 + 2 pi D |Im x|)  (Gaussian decay).
      * `lineUp_fresnel`, `lineUp_gauss` : the Gaussian line integrals, e.g.
            lineUp c (x |-> e^{i pi (x^2+x) - x y}) = e^{y/2 + i y^2/(4 pi)}     (every c, every y).
      * `lineUp_same_gap`, `lineUp_cross` : moving the slope-(+1) line inside a gap (n, n+1) changes
        nothing; moving it across the pole at the integer n adds phi(n):
            lineUp c2 (rsG * phi) = lineUp c1 (rsG * phi) + phi n,   n-1 < c1 < n < c2 < n+1,
        for every phi holomorphic on the strip with at most exponential growth.  No residue theorem
        is used: the pole is removed by `dslope`, and the jump of the bare kernel is computed from
        the difference equation and the Fresnel integral.
      * `lineDn_same_gap`, `lineDn_cross` : the slope-(-1) analogues for rsH (by conjugation).
      * `lineUp_mordell` : the Mordell closed form, for 0 < c < 1 and every y:
            lineUp c (x |-> rsG x e^{-x y}) (e^{-y/2} - e^{y/2}) = e^{-y/2} - e^{i y^2/(4 pi)}.

    conjecture1_proved = False.  Contour identities for one explicit kernel; nothing here bears
    on RH.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real

noncomputable section

namespace RSInt

/-! ## 1. The kernels and their algebra -/







theorem pi_ne_zero' : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero



















/-! ## 2. Norm bounds -/

























/-! ## 3. The Fresnel line integral -/











/-! ## 4. Gaussian tails, line integrability, and the strip wrappers -/























/-! ## 5. Linearity and translation of line integrals -/













/-! ## 6. Holomorphy of the kernels off the integers -/











theorem notInt_of_Ioo {c : ℝ} {n : ℤ} (h₁ : (n : ℝ) < c) (h₂ : c < n + 1) :
    ∀ m : ℤ, (m : ℝ) ≠ c := by
  intro m hm
  rw [← hm] at h₁ h₂
  have a : n < m := by exact_mod_cast h₁
  have b : m < n + 1 := by exact_mod_cast h₂
  omega

/-! ## 7. The Fresnel/Gaussian integrands are integrable along the lines -/









/-! ## 8. Moving the line inside a gap, and across a pole -/











/-! ## 9. The slope-(-1) side by conjugation -/

















/-! ## 10. The Mordell closed form -/



end RSInt

end

/-  RS_B2.lean -- lane RS, ANDURIL brick B2: RIEMANN'S INTEGRAL REPRESENTATION OF zeta(s) for
    general complex s, with the residue bookkeeping (the exact Riemann-Siegel formula).
    Mathlib-only (imports `RS_Entire`).

    ## The headline (`riemann_siegel_integral`)

    For every complex s that is not an odd positive integer (s ∉ {1, 3, 5, ...}), all N, M ∈ ℕ and
    every c1 ∈ (N, N+1), c2 ∈ (M, M+1):

      zeta(s) = sum_{n=1}^{N} n^(-s) + chi(s) sum_{m=1}^{M} m^(s-1)
                - lineUp c1 (x |-> rsG x x^(-s)) + chi(s) lineDn c2 (x |-> rsH x x^(s-1)),

      rsG x = e^{i pi x^2}/(e^{i pi x} - e^{-i pi x}),  rsH x = e^{-i pi x^2}/(e^{i pi x} - e^{-i pi x}),
      chi(s) = pi^(s-1/2) Gamma((1-s)/2) / Gamma(s/2),
      lineUp c F = int F(c + v(1+i))(1+i) dv,   lineDn c F = int F(c + v(1-i))(1-i) dv.

    This is Riemann's integral (Siegel 1932; Edwards ch. 7; Titchmarsh 2.10) in exactly the form
    used for the Riemann-Siegel saddle-point analysis: the remainder integrals run along the
    steepest-descent directions of e^{+-i pi x^2} and may cross the real axis anywhere in the gap.
    (At s = 3, 5, ... Mathlib's Gamma((1-s)/2) takes the junk value 0 at its pole, so those points
    are excluded; s = 1 is the pole of zeta.)

    ## How it is proved (no residue theorem, no Hankel contour)

      1. N = M = 0, Re s > 2 (`rs_identity_re_gt_two`): the Mellin identity (RS_Mellin: Fubini with
         the complex Gamma integral, the Mordell closed form, the Bose integral = Gamma zeta) and the
         folding of the chi-side line (RS_Fold), assembled with the Gamma identity for chi.
      2. All s ∉ {1,3,5,...} (`rs_identity`): identity theorem on the connected open set
         ℂ \ {1,3,5,...}; both sides are holomorphic there (RS_Entire).
      3. General N, M (`lineUp_book`, `lineDn_book`): induction, crossing one pole at a time
         (`lineUp_cross`, `lineDn_cross` in RS_Kernel).

    ## Critical line (`completedRiemannZeta_eq_rs`, `completed_re_eq_rs_cos`)

    For s = 1/2 + it and c ∈ (N, N+1), with S = sum_{n<=N} n^(-s) and R = -lineUp c (rsG x^(-s)):
        completedRiemannZeta s = 2 Re( Gammaℝ(s) (S + R) )        (a real number),
    and, whenever Gammaℝ(s) = M e^{i phi} with M > 0 (the island's polar form),
        Re completedRiemannZeta(s) = 2M ( sum_{n<=N} n^(-1/2) cos(phi - t log n) + Re(e^{i phi} R) ).
    So Z(t) = 2 sum n^(-1/2) cos(theta - t log n) + 2 Re(e^{i theta} R_N(t)) EXACTLY: the only
    analytic input left for sign certification is a bound on the remainder R_N(t) (brick B3).

    conjecture1_proved = False.  An exact integral identity for zeta; nothing here bears on RH.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

namespace RSInt

/-! ## 1. The identity for Re s > 2 -/

theorem one_add_exp_ne_zero {s : ℂ} (h : ∀ k : ℤ, s ≠ 2 * k + 1) : 1 + cexp (↑π * I * s) ≠ 0 := by
  intro h0
  have h1 : cexp (↑π * I * s) = cexp (↑π * I) := by
    rw [Complex.exp_pi_mul_I]; linear_combination h0
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h1
  apply h n
  have h2 : (↑π * I : ℂ) * s = (↑π * I) * (2 * n + 1) := by linear_combination hn
  exact mul_left_cancel₀ (mul_ne_zero pi_ne_zero' I_ne_zero) h2



/-! ## 2. The domain ℂ \ {1, 3, 5, ...} -/



theorem mem_oddSet_compl {s : ℂ} : s ∈ oddSetᶜ ↔ ∀ k : ℕ, s ≠ 2 * k + 1 := by
  simp only [oddSet, mem_compl_iff, mem_range, not_exists]
  exact forall_congr' fun k => ne_comm

theorem isClosed_oddSet : IsClosed oddSet := by
  apply Metric.isClosed_of_pairwise_le_dist (ε := 1) one_pos
  rintro _ ⟨j, rfl⟩ _ ⟨k, rfl⟩ hne
  have hjk : (j : ℤ) - k ≠ 0 := by
    intro h; apply hne; have : j = k := by omega
    rw [this]
  rw [Complex.dist_eq, show ((2 * j + 1 : ℂ) - (2 * k + 1)) = ((2 * ((j : ℤ) - k) : ℤ) : ℂ) by
    push_cast; ring, Complex.norm_intCast]
  have h1 : (1 : ℤ) ≤ |2 * ((j : ℤ) - k)| := by
    have := Int.one_le_abs hjk
    rw [abs_mul]; simp; omega
  exact_mod_cast h1

theorem isPreconnected_oddSet_compl : IsPreconnected oddSetᶜ :=
  ((Set.countable_range _).isConnected_compl_of_one_lt_rank (by simp)).isPreconnected

/-! ## 3. Riemann's integral for every s ∉ {1, 3, 5, ...} (N = M = 0) -/



/-! ## 4. Residue bookkeeping -/



















/-! ## 5. THE HEADLINE: Riemann's integral with the residue bookkeeping -/



/-! ## 6. The critical line -/















end RSInt

end

/-  RS_B2.lean -- lane RS, ANDURIL brick B2: RIEMANN'S INTEGRAL REPRESENTATION OF zeta(s) for
    general complex s, with the residue bookkeeping (the exact Riemann-Siegel formula).
    Mathlib-only (imports `RS_Entire`).

    ## The headline (`riemann_siegel_integral`)

    For every complex s that is not an odd positive integer (s ∉ {1, 3, 5, ...}), all N, M ∈ ℕ and
    every c1 ∈ (N, N+1), c2 ∈ (M, M+1):

      zeta(s) = sum_{n=1}^{N} n^(-s) + chi(s) sum_{m=1}^{M} m^(s-1)
                - lineUp c1 (x |-> rsG x x^(-s)) + chi(s) lineDn c2 (x |-> rsH x x^(s-1)),

      rsG x = e^{i pi x^2}/(e^{i pi x} - e^{-i pi x}),  rsH x = e^{-i pi x^2}/(e^{i pi x} - e^{-i pi x}),
      chi(s) = pi^(s-1/2) Gamma((1-s)/2) / Gamma(s/2),
      lineUp c F = int F(c + v(1+i))(1+i) dv,   lineDn c F = int F(c + v(1-i))(1-i) dv.

    This is Riemann's integral (Siegel 1932; Edwards ch. 7; Titchmarsh 2.10) in exactly the form
    used for the Riemann-Siegel saddle-point analysis: the remainder integrals run along the
    steepest-descent directions of e^{+-i pi x^2} and may cross the real axis anywhere in the gap.
    (At s = 3, 5, ... Mathlib's Gamma((1-s)/2) takes the junk value 0 at its pole, so those points
    are excluded; s = 1 is the pole of zeta.)

    ## How it is proved (no residue theorem, no Hankel contour)

      1. N = M = 0, Re s > 2 (`rs_identity_re_gt_two`): the Mellin identity (RS_Mellin: Fubini with
         the complex Gamma integral, the Mordell closed form, the Bose integral = Gamma zeta) and the
         folding of the chi-side line (RS_Fold), assembled with the Gamma identity for chi.
      2. All s ∉ {1,3,5,...} (`rs_identity`): identity theorem on the connected open set
         ℂ \ {1,3,5,...}; both sides are holomorphic there (RS_Entire).
      3. General N, M (`lineUp_book`, `lineDn_book`): induction, crossing one pole at a time
         (`lineUp_cross`, `lineDn_cross` in RS_Kernel).

    ## Critical line (`completedRiemannZeta_eq_rs`, `completed_re_eq_rs_cos`)

    For s = 1/2 + it and c ∈ (N, N+1), with S = sum_{n<=N} n^(-s) and R = -lineUp c (rsG x^(-s)):
        completedRiemannZeta s = 2 Re( Gammaℝ(s) (S + R) )        (a real number),
    and, whenever Gammaℝ(s) = M e^{i phi} with M > 0 (the island's polar form),
        Re completedRiemannZeta(s) = 2M ( sum_{n<=N} n^(-1/2) cos(phi - t log n) + Re(e^{i phi} R) ).
    So Z(t) = 2 sum n^(-1/2) cos(theta - t log n) + 2 Re(e^{i theta} R_N(t)) EXACTLY: the only
    analytic input left for sign certification is a bound on the remainder R_N(t) (brick B3).

    conjecture1_proved = False.  An exact integral identity for zeta; nothing here bears on RH.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

section
namespace RSInt
end RSInt
open RSInt

/-! ## 1. The identity for Re s > 2 -/





/-! ## 2. The domain ℂ \ {1, 3, 5, ...} -/









/-! ## 3. Riemann's integral for every s ∉ {1, 3, 5, ...} (N = M = 0) -/

theorem solution {s : ℂ} (hs : ∀ k : ℕ, s ≠ 2 * k + 1) {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    riemannZeta s = -lineUp c (fun x => rsG x * x ^ (-s)) +
      rsChi s * lineDn c (fun x => rsH x * x ^ (s - 1)) := by
  have hcl : ∀ m : ℤ, (m : ℝ) ≠ c :=
    notInt_of_Ioo (n := 0) (by simpa using hc) (by simpa using hc1)
  have hUo : IsOpen oddSetᶜ := isClosed_oddSet.isOpen_compl
  have hf : DifferentiableOn ℂ riemannZeta oddSetᶜ := by
    intro z hz
    refine (differentiableAt_riemannZeta ?_).differentiableWithinAt
    intro h1
    exact mem_oddSet_compl.mp hz 0 (by rw [h1]; simp)
  have hg : DifferentiableOn ℂ (fun z : ℂ => -lineUp c (fun x => rsG x * x ^ (-z)) +
      rsChi z * lineDn c (fun x => rsH x * x ^ (z - 1))) oddSetᶜ := by
    intro z hz
    exact ((differentiable_rsA hc hcl z).neg.add
      ((differentiableAt_rsChi (mem_oddSet_compl.mp hz)).mul
        (differentiable_rsB hc hcl z))).differentiableWithinAt
  have h52 : (5 / 2 : ℂ) ∈ oddSetᶜ := by
    rw [mem_oddSet_compl]
    intro k hk
    have := congrArg Complex.re hk
    simp at this
    have h1 : (0 : ℝ) < k := by linarith
    have h2 : (k : ℝ) < 1 := by linarith
    have h1' : 0 < k := by exact_mod_cast h1
    have h2' : k < 1 := by exact_mod_cast h2
    omega
  have hev : riemannZeta =ᶠ[𝓝 (5 / 2 : ℂ)] (fun z : ℂ => -lineUp c (fun x => rsG x * x ^ (-z)) +
      rsChi z * lineDn c (fun x => rsH x * x ^ (z - 1))) := by
    filter_upwards [Metric.ball_mem_nhds (5 / 2 : ℂ) (by norm_num : (0 : ℝ) < 1 / 4)] with z hz
    have hre : |z.re - 5 / 2| < 1 / 4 := by
      have h1 := Metric.mem_ball.mp hz
      rw [Complex.dist_eq] at h1
      have h2 := Complex.abs_re_le_norm (z - 5 / 2)
      simp at h2
      linarith
    rw [abs_lt] at hre
    refine rs_identity_re_gt_two (by linarith [hre.1]) (one_add_exp_ne_zero ?_) hc hc1
    intro k hk
    have := congrArg Complex.re hk
    simp at this
    have h1 : (0 : ℝ) < k := by linarith [hre.1]
    have h2 : (k : ℝ) < 1 := by linarith [hre.2]
    have h1' : 0 < k := by exact_mod_cast h1
    have h2' : k < 1 := by exact_mod_cast h2
    omega
  exact (hf.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hUo)
    isPreconnected_oddSet_compl h52 hev (mem_oddSet_compl.mpr hs)
