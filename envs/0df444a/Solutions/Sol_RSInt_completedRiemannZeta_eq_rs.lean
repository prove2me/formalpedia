-- Prove2me | solution 1 for RSInt.completedRiemannZeta_eq_rs
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:33:59.460634+00:00
-- url     : https://prove2.me/submissions/90c2ad49-2c22-4127-8863-6adf6ef65523

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_lineDn_book
import Theorems.Thm_RSInt_lineDn_eq_conj_neg_lineUp
import Theorems.Thm_RSInt_lineUp_book
import Theorems.Thm_RSInt_rs_identity
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





/-! ## 2. The domain ℂ \ {1, 3, 5, ...} -/









/-! ## 3. Riemann's integral for every s ∉ {1, 3, 5, ...} (N = M = 0) -/



/-! ## 4. Residue bookkeeping -/



















/-! ## 5. THE HEADLINE: Riemann's integral with the residue bookkeeping -/

/-- **Riemann's integral representation of `zeta(s)` (the exact Riemann-Siegel formula).**
    For every complex `s ∉ {1, 3, 5, ...}`, all `N M : ℕ` and all crossing points
    `c1 ∈ (N, N+1)`, `c2 ∈ (M, M+1)`:
        zeta(s) = sum_{n=1}^{N} n^(-s) + chi(s) sum_{m=1}^{M} m^(s-1)
                  - lineUp c1 (rsG x^(-s)) + chi(s) lineDn c2 (rsH x^(s-1)). -/
theorem riemann_siegel_integral (s : ℂ) (hs : ∀ k : ℕ, s ≠ 2 * k + 1) (N M : ℕ) {c₁ c₂ : ℝ}
    (h₁ : (N : ℝ) < c₁) (h₁' : c₁ < N + 1) (h₂ : (M : ℝ) < c₂) (h₂' : c₂ < M + 1) :
    riemannZeta s =
      (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) + rsChi s * (∑ m ∈ Finset.Icc 1 M, (m : ℂ) ^ (s - 1))
        - lineUp c₁ (fun x => rsG x * x ^ (-s))
        + rsChi s * lineDn c₂ (fun x => rsH x * x ^ (s - 1)) := by
  rw [rs_identity hs (c := 1 / 2) (by norm_num) (by norm_num),
    lineUp_book s N (c := 1 / 2) (by norm_num) (by norm_num) h₁ h₁',
    lineDn_book s M (c := 1 / 2) (by norm_num) (by norm_num) h₂ h₂']
  ring

/-! ## 6. The critical line -/

theorem conj_ofReal_cpow {r : ℝ} (hr : 0 < r) (w : ℂ) :
    conj ((r : ℂ) ^ w) = (r : ℂ) ^ (conj w) := by
  have harg : (r : ℂ).arg ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg hr.le]; exact Real.pi_ne_zero.symm
  have h := Complex.conj_cpow (r : ℂ) (conj w) harg
  rw [Complex.conj_ofReal, Complex.conj_conj] at h
  exact h.symm



theorem conj_natCast_cpow_crit {s : ℂ} (hs : s.re = 1 / 2) (n : ℕ) (hn : 1 ≤ n) :
    conj ((n : ℂ) ^ (-s)) = (n : ℂ) ^ (s - 1) := by
  have hr : (0 : ℝ) < n := by exact_mod_cast hn
  have := conj_ofReal_cpow hr (-s)
  push_cast at this
  rw [this]
  congr 1
  apply Complex.ext <;> simp [hs]
  linarith

theorem Gammaℝ_mul_rsChi {s : ℂ} (hs : 0 < s.re) : Gammaℝ s * rsChi s = Gammaℝ (1 - s) := by
  have hG : Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  unfold rsChi
  rw [Gammaℝ_def, Gammaℝ_def]
  have hpi := pi_ne_zero'
  have hc : (↑π : ℂ) ^ (-s / 2) * (↑π : ℂ) ^ (s - 1 / 2) = (↑π : ℂ) ^ (-(1 - s) / 2) := by
    rw [← Complex.cpow_add _ _ hpi]; congr 1; ring
  rw [show (↑π : ℂ) ^ (-s / 2) * Gamma (s / 2) * ((↑π : ℂ) ^ (s - 1 / 2) * Gamma ((1 - s) / 2) *
      (Gamma (s / 2))⁻¹) = ((↑π : ℂ) ^ (-s / 2) * (↑π : ℂ) ^ (s - 1 / 2)) * Gamma ((1 - s) / 2) *
      (Gamma (s / 2) * (Gamma (s / 2))⁻¹) by ring, hc, mul_inv_cancel₀ hG, mul_one]

theorem Gammaℝ_conj (s : ℂ) : Gammaℝ (conj s) = conj (Gammaℝ s) := by
  have e1 : conj (-s / 2) = -conj s / 2 := by rw [map_div₀, map_neg, map_ofNat]
  have e2 : conj (s / 2) = conj s / 2 := by rw [map_div₀, map_ofNat]
  rw [Gammaℝ_def, Gammaℝ_def, map_mul, conj_ofReal_cpow Real.pi_pos, ← Complex.Gamma_conj, e1, e2]





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



/-! ## 4. Residue bookkeeping -/



















/-! ## 5. THE HEADLINE: Riemann's integral with the residue bookkeeping -/



/-! ## 6. The critical line -/












theorem solution (t : ℝ) (N : ℕ) {c : ℝ} (h : (N : ℝ) < c) (h' : c < N + 1) :
    completedRiemannZeta ((1 / 2 : ℂ) + t * I) =
      ((2 * (Gammaℝ ((1 / 2 : ℂ) + t * I) *
        ((∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-((1 / 2 : ℂ) + t * I))) -
          lineUp c (fun x => rsG x * x ^ (-((1 / 2 : ℂ) + t * I))))).re : ℝ) : ℂ) := by
  set s : ℂ := (1 / 2 : ℂ) + t * I with hsdef
  have hsre : s.re = 1 / 2 := by simp [hsdef]
  have hc : 0 < c := lt_of_le_of_lt (Nat.cast_nonneg N) h
  have hodd : ∀ k : ℕ, s ≠ 2 * k + 1 := by
    intro k hk; have := congrArg Complex.re hk; simp [hsdef] at this
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  have hs0 : s ≠ 0 := by intro h0; have := congrArg Complex.re h0; simp [hsdef] at this
  have hGne : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [hsre]; norm_num)
  have hZ := riemann_siegel_integral s hodd N N h h' h h'
  have hcompl : completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
    rw [riemannZeta_def_of_ne_zero hs0, mul_div_cancel₀ _ hGne]
  set S := ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) with hS
  set R := -lineUp c (fun x => rsG x * x ^ (-s)) with hR
  have hS' : ∑ m ∈ Finset.Icc 1 N, (m : ℂ) ^ (s - 1) = conj S := by
    rw [hS, map_sum]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [conj_natCast_cpow_crit hsre n (Finset.mem_Icc.mp hn).1]
  have hB : lineDn c (fun x => rsH x * x ^ (s - 1)) = conj R := lineDn_eq_conj_neg_lineUp hsre hc
  have hχ : Gammaℝ s * rsChi s = conj (Gammaℝ s) := by
    rw [Gammaℝ_mul_rsChi (by rw [hsre]; norm_num), ← Gammaℝ_conj]
    congr 1
    apply Complex.ext <;> simp [hsdef]; norm_num
  rw [hcompl, hZ, hS', hB]
  have : Gammaℝ s * (S + rsChi s * conj S - lineUp c (fun x => rsG x * x ^ (-s)) +
      rsChi s * conj R) = Gammaℝ s * (S + R) + conj (Gammaℝ s * (S + R)) := by
    rw [map_mul, map_add, ← hχ, hR]; ring
  rw [this, Complex.add_conj, hR, ← sub_eq_add_neg]
