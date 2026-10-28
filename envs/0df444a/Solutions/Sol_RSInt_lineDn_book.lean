-- Prove2me | solution 1 for RSInt.lineDn_book
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:20:17.964123+00:00
-- url     : https://prove2.me/submissions/36780a1e-fc72-4dcc-a3a0-1e4d4e25b55d

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_integrable_of_continuous_of_tail
import Theorems.Thm_RSInt_lineUp_cross
import Theorems.Thm_RSInt_lineUp_eq_of_strip
import Theorems.Thm_RSInt_norm_cpow_le_of_ge
import Theorems.Thm_RSInt_norm_rsG_mul_le
/-  RS_Strip.lean -- lane RS, ANDURIL brick B2 (the Riemann-Siegel integral), part 1:
    contour tools.

    Mathlib-only (no corpus import), so the file can serve the dbn island's M5 layer L6 as well.

    ## Contents (no `sorry`, no `native_decide`, no new axioms)

      * `integrable_exp_quad`, `integrable_of_continuous_of_tail` : integrability of a continuous
        function from a Gaussian-type tail bound `C exp(-a v^2 + b |v|)`.
      * `strip_integral_eq` : Cauchy's theorem on a HORIZONTAL STRIP y1 <= Im z <= y2 with decay at
        both ends: the integrals along the two edges agree.  (Mathlib's rectangle theorem
        `integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn` plus two limits.)
      * `lineUp c F`, `lineDn c F` : the oriented integrals along the slanted lines through the real
        point `c` with directions `1 + I` (slope +1) and `1 - I` (slope -1).
      * `lineUp_eq_of_strip`, `lineDn_eq_of_strip` : line independence -- the integral along the line
        through `c1` equals the one through `c2` when `F` is continuous on the closed slanted strip,
        holomorphic inside, and tends to 0 at infinity in the strip.

    conjecture1_proved = False.  Contour-integration infrastructure; nothing here bears on RH.
-/


open Complex MeasureTheory Filter Topology Set

noncomputable section

namespace RSInt

/-! ## 1. Integrability from a Gaussian tail -/

theorem exp_quad_le (a b v : ℝ) (ha : 0 < a) :
    Real.exp (-a * v ^ 2 + b * |v|) ≤ Real.exp (b ^ 2 / (2 * a)) * Real.exp (-(a / 2) * v ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h2a : 0 < 2 * a := by positivity
  have key : 2 * a * (-a * v ^ 2 + b * |v|) ≤ 2 * a * (b ^ 2 / (2 * a) + -(a / 2) * v ^ 2) := by
    rw [mul_add (2 * a) (b ^ 2 / (2 * a)), mul_div_cancel₀ _ h2a.ne']
    nlinarith [sq_nonneg (a * |v| - b), show a ^ 2 * |v| ^ 2 = a ^ 2 * v ^ 2 by rw [sq_abs]]
  exact le_of_mul_le_mul_left key h2a





/-! ## 2. Cauchy's theorem on a horizontal strip -/



/-! ## 3. Slanted lines -/



























end RSInt

end

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









theorem rsD_eq_zero_iff (x : ℂ) : rsD x = 0 ↔ ∃ n : ℤ, x = n := by
  unfold rsD
  rw [sub_eq_zero, Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h2 : (2 * ↑π * I : ℂ) * x = (2 * ↑π * I) * n := by linear_combination hn
    exact mul_left_cancel₀ (by simp [I_ne_zero]) h2
  · rintro ⟨n, rfl⟩
    exact ⟨n, by ring⟩



theorem differentiable_rsD : Differentiable ℂ rsD := by
  unfold rsD; fun_prop













/-! ## 2. Norm bounds -/

















/-- On the slanted strip `c1 <= Re x - Im x <= c2`, `‖x‖ <= 2 |Im x| + D`, `D = |c1| + |c2|`. -/
theorem norm_le_of_upStrip {x : ℂ} {c₁ c₂ : ℝ} (hx : x.re - x.im ∈ Icc c₁ c₂) :
    ‖x‖ ≤ 2 * |x.im| + (|c₁| + |c₂|) := by
  have h1 := Complex.norm_le_abs_re_add_abs_im x
  have hd : |x.re - x.im| ≤ |c₁| + |c₂| := by
    rw [abs_le]; constructor
    · linarith [hx.1, neg_abs_le c₁, abs_nonneg c₂]
    · linarith [hx.2, le_abs_self c₂, abs_nonneg c₁]
  have h2 : |x.re| ≤ |x.im| + |x.re - x.im| := by
    calc |x.re| = |x.im + (x.re - x.im)| := by ring_nf
      _ ≤ |x.im| + |x.re - x.im| := abs_add_le _ _
  linarith







/-! ## 3. The Fresnel line integral -/











/-! ## 4. Gaussian tails, line integrability, and the strip wrappers -/

theorem gauss_tail_small {C a b : ℝ} (ha : 0 < a) :
    ∀ ε > 0, ∃ Y : ℝ, 1 ≤ Y ∧ ∀ y : ℝ, Y ≤ |y| → C * Real.exp (-a * y ^ 2 + b * |y|) ≤ ε := by
  intro ε hε
  set K := Real.exp (b ^ 2 / (2 * a)) with hK
  set M := |C| * K + 1 with hM
  have hMpos : 0 < M := by positivity
  refine ⟨max 1 (2 / a * |Real.log (M / ε)|), le_max_left _ _, fun y hy => ?_⟩
  have hy1 : 1 ≤ |y| := le_trans (le_max_left _ _) hy
  have hy2 : 2 / a * |Real.log (M / ε)| ≤ |y| := le_trans (le_max_right _ _) hy
  have h1 : C * Real.exp (-a * y ^ 2 + b * |y|) ≤ |C| * (K * Real.exp (-(a / 2) * y ^ 2)) := by
    calc C * Real.exp (-a * y ^ 2 + b * |y|) ≤ |C| * Real.exp (-a * y ^ 2 + b * |y|) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
      _ ≤ |C| * (K * Real.exp (-(a / 2) * y ^ 2)) :=
          mul_le_mul_of_nonneg_left (exp_quad_le a b y ha) (abs_nonneg C)
  have h2 : Real.exp (-(a / 2) * y ^ 2) ≤ Real.exp (-(a / 2) * |y|) := by
    apply Real.exp_le_exp.mpr
    have : |y| ≤ y ^ 2 := by
      rw [← sq_abs]; nlinarith
    nlinarith
  have h3 : Real.exp (-(a / 2) * |y|) ≤ ε / M := by
    have hl : |Real.log (M / ε)| ≤ a / 2 * |y| := by
      have := mul_le_mul_of_nonneg_left hy2 (le_of_lt (half_pos ha))
      rwa [← mul_assoc, show a / 2 * (2 / a) = 1 by field_simp, one_mul] at this
    calc Real.exp (-(a / 2) * |y|) ≤ Real.exp (-Real.log (M / ε)) := by
          apply Real.exp_le_exp.mpr
          have := le_abs_self (Real.log (M / ε))
          nlinarith
      _ = ε / M := by
          rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  have hK0 : 0 ≤ K := (Real.exp_pos _).le
  calc C * Real.exp (-a * y ^ 2 + b * |y|) ≤ |C| * (K * Real.exp (-(a / 2) * y ^ 2)) := h1
    _ ≤ M * Real.exp (-(a / 2) * |y|) := by
        have : |C| * (K * Real.exp (-(a / 2) * y ^ 2)) ≤ |C| * K * Real.exp (-(a / 2) * |y|) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
        have h4 : |C| * K * Real.exp (-(a / 2) * |y|) ≤ M * Real.exp (-(a / 2) * |y|) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
        linarith
    _ ≤ M * (ε / M) := mul_le_mul_of_nonneg_left h3 hMpos.le
    _ = ε := by field_simp



theorem lineUp_pt_im (c v : ℝ) : ((c : ℂ) + v * (1 + I)).im = v := by simp





theorem integrable_lineUp {F : ℂ → ℂ} {c₁ c₂ c : ℝ} (hc : c ∈ Icc c₁ c₂)
    (hcont : ContinuousOn F {x : ℂ | x.re - x.im ∈ Icc c₁ c₂})
    {C a b : ℝ} (ha : 0 < a)
    (hbound : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → 1 ≤ |x.im| →
      ‖F x‖ ≤ C * Real.exp (-a * x.im ^ 2 + b * |x.im|)) :
    Integrable (fun v : ℝ => F (c + v * (1 + I))) := by
  have hmem : ∀ v : ℝ, ((c : ℂ) + v * (1 + I)) ∈ {x : ℂ | x.re - x.im ∈ Icc c₁ c₂} := by
    intro v
    simp only [mem_setOf_eq]
    have e : ((c : ℂ) + v * (1 + I)).re - ((c : ℂ) + v * (1 + I)).im = c := by simp
    rw [e]; exact hc
  refine integrable_of_continuous_of_tail (a := a) (b := b) (C := C) (R := 1)
    (hcont.comp_continuous (by fun_prop) hmem) ha (fun v hv => ?_)
  have := hbound _ (hmem v) (by rw [lineUp_pt_im]; exact hv)
  rwa [lineUp_pt_im] at this



/-- `lineUp_eq_of_strip` with the integrability and decay hypotheses replaced by one Gaussian
    bound in `Im x` (valid for `|Im x| >= 1`). -/
theorem lineUp_eq_of_strip' {F : ℂ → ℂ} {c₁ c₂ : ℝ} (hc : c₁ ≤ c₂)
    (hcont : ContinuousOn F {x : ℂ | x.re - x.im ∈ Icc c₁ c₂})
    (hdiff : DifferentiableOn ℂ F {x : ℂ | x.re - x.im ∈ Ioo c₁ c₂})
    {C a b : ℝ} (ha : 0 < a)
    (hbound : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → 1 ≤ |x.im| →
      ‖F x‖ ≤ C * Real.exp (-a * x.im ^ 2 + b * |x.im|)) :
    lineUp c₁ F = lineUp c₂ F := by
  refine lineUp_eq_of_strip hc hcont hdiff
    (integrable_lineUp ⟨le_rfl, hc⟩ hcont ha hbound)
    (integrable_lineUp ⟨hc, le_rfl⟩ hcont ha hbound) (fun ε hε => ?_)
  obtain ⟨Y, hY1, hY⟩ := gauss_tail_small (C := C) (b := b) ha ε hε
  refine ⟨2 * Y + (|c₁| + |c₂|), fun x hx hR => ?_⟩
  have hn := norm_le_of_upStrip hx
  have him : Y ≤ |x.im| := by linarith
  exact (hbound x hx (le_trans hY1 him)).trans (hY _ him)







/-! ## 5. Linearity and translation of line integrals -/





theorem lineUp_const_mul (k : ℂ) (F : ℂ → ℂ) (c : ℝ) :
    lineUp c (fun x => k * F x) = k * lineUp c F := by
  unfold lineUp; rw [← integral_const_mul]; congr 1; ext v; ring







/-! ## 6. Holomorphy of the kernels off the integers -/

theorem rsD_ne_zero_of_ne {x : ℂ} (h : ∀ n : ℤ, x ≠ n) : rsD x ≠ 0 := by
  intro h0; obtain ⟨n, hn⟩ := (rsD_eq_zero_iff x).mp h0; exact h n hn

theorem differentiableAt_rsG {x : ℂ} (h : rsD x ≠ 0) : DifferentiableAt ℂ rsG x := by
  unfold rsG
  exact ((by fun_prop : Differentiable ℂ (fun x : ℂ => cexp (↑π * I * x ^ 2))) x).div
    (differentiable_rsD x) h









/-! ## 7. The Fresnel/Gaussian integrands are integrable along the lines -/









/-! ## 8. Moving the line inside a gap, and across a pole -/

/-- **Same gap.**  If the closed crossing interval `[c1, c2]` contains no integer, the slope-(+1)
    integral of `rsG * phi` does not depend on the crossing point. -/
theorem lineUp_same_gap {φ : ℂ → ℂ} {c₁ c₂ : ℝ} (hc : c₁ ≤ c₂)
    (hno : ∀ m : ℤ, (m : ℝ) ∉ Icc c₁ c₂)
    (hφ : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → DifferentiableAt ℂ φ x)
    {A B : ℝ} (hgrow : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → ‖φ x‖ ≤ A * Real.exp (B * ‖x‖)) :
    lineUp c₁ (fun x => rsG x * φ x) = lineUp c₂ (fun x => rsG x * φ x) := by
  have hD : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → rsD x ≠ 0 := by
    intro x hx
    refine rsD_ne_zero_of_ne fun n hn => hno n ?_
    rw [hn] at hx; simpa using hx
  have hdA : ∀ x : ℂ, x.re - x.im ∈ Icc c₁ c₂ → DifferentiableAt ℂ (fun x => rsG x * φ x) x :=
    fun x hx => (differentiableAt_rsG (hD x hx)).mul (hφ x hx)
  exact lineUp_eq_of_strip' hc (fun x hx => (hdA x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hdA x ⟨hx.1.le, hx.2.le⟩).differentiableWithinAt) (a := 2 * π)
    (by positivity) (fun x hx h1 => norm_rsG_mul_le hx h1 (hgrow x hx))









/-! ## 9. The slope-(-1) side by conjugation -/

open ComplexConjugate in
theorem conj_lineUp_pt (c v : ℝ) : conj ((c : ℂ) + v * (1 + I)) = (c : ℂ) + v * (1 - I) := by
  simp only [map_add, map_mul, Complex.conj_ofReal, map_one, Complex.conj_I]; ring

open ComplexConjugate in
theorem lineDn_eq_conj (c : ℝ) (F : ℂ → ℂ) :
    lineDn c F = conj (lineUp c (fun x => conj (F (conj x)))) := by
  unfold lineDn lineUp
  rw [← integral_conj]
  congr 1; ext v
  rw [map_mul, Complex.conj_conj, conj_lineUp_pt]
  congr 1
  simp only [map_add, map_one, Complex.conj_I]; ring

open ComplexConjugate in
theorem conj_rsD_conj (x : ℂ) : conj (rsD (conj x)) = -rsD x := by
  unfold rsD
  rw [map_sub, ← Complex.exp_conj, ← Complex.exp_conj]
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.conj_conj]
  ring_nf

open ComplexConjugate in
theorem conj_rsH_conj (x : ℂ) : conj (rsH (conj x)) = -rsG x := by
  unfold rsH rsG
  rw [map_div₀, conj_rsD_conj, ← Complex.exp_conj]
  simp only [map_neg, map_mul, map_pow, Complex.conj_ofReal, Complex.conj_I, Complex.conj_conj]
  rw [div_neg]
  ring_nf

open ComplexConjugate in
theorem lineDn_rsH_eq (c : ℝ) (ψ : ℂ → ℂ) :
    lineDn c (fun x => rsH x * ψ x) =
      -conj (lineUp c (fun x => rsG x * conj (ψ (conj x)))) := by
  rw [lineDn_eq_conj, ← map_neg]
  congr 1
  have : (fun x => conj (rsH (conj x) * ψ (conj x))) =
      fun x => (-1) * (rsG x * conj (ψ (conj x))) := by
    ext x; rw [map_mul, conj_rsH_conj]; ring
  rw [this, lineUp_const_mul]; ring

open ComplexConjugate in
theorem conj_mem_dnStrip {x : ℂ} {c₁ c₂ : ℝ} (hx : x.re - x.im ∈ Icc c₁ c₂) :
    (conj x).re + (conj x).im ∈ Icc c₁ c₂ := by
  simpa [sub_eq_add_neg] using hx

/-- **Crossing a pole, slope (-1).**  For `n - 1 < c1 < n < c2 < n + 1` and `psi` holomorphic on the
    closed slope-(-1) strip with at most exponential growth:
        lineDn c2 (rsH * psi) = lineDn c1 (rsH * psi) - psi n. -/
theorem lineDn_cross {ψ : ℂ → ℂ} {n : ℤ} {c₁ c₂ : ℝ}
    (h₁ : (n : ℝ) - 1 < c₁) (h₁' : c₁ < n) (h₂ : (n : ℝ) < c₂) (h₂' : c₂ < n + 1)
    (hψ : ∀ x : ℂ, x.re + x.im ∈ Icc c₁ c₂ → DifferentiableAt ℂ ψ x)
    {A B : ℝ} (hgrow : ∀ x : ℂ, x.re + x.im ∈ Icc c₁ c₂ → ‖ψ x‖ ≤ A * Real.exp (B * ‖x‖)) :
    lineDn c₂ (fun x => rsH x * ψ x) = lineDn c₁ (fun x => rsH x * ψ x) - ψ n := by
  open ComplexConjugate in
  rw [lineDn_rsH_eq, lineDn_rsH_eq]
  have hc := lineUp_cross (φ := fun x => (starRingEnd ℂ) (ψ ((starRingEnd ℂ) x))) h₁ h₁' h₂ h₂'
    (fun x hx => differentiableAt_conj_conj_iff.mpr (hψ _ (conj_mem_dnStrip hx))) (A := A) (B := B)
    (fun x hx => by
      rw [RCLike.norm_conj]
      have := hgrow _ (conj_mem_dnStrip hx)
      rwa [RCLike.norm_conj] at this)
  rw [hc, map_add, Complex.conj_conj, map_intCast]
  ring

theorem lineDn_same_gap {ψ : ℂ → ℂ} {c₁ c₂ : ℝ} (hc : c₁ ≤ c₂)
    (hno : ∀ m : ℤ, (m : ℝ) ∉ Icc c₁ c₂)
    (hψ : ∀ x : ℂ, x.re + x.im ∈ Icc c₁ c₂ → DifferentiableAt ℂ ψ x)
    {A B : ℝ} (hgrow : ∀ x : ℂ, x.re + x.im ∈ Icc c₁ c₂ → ‖ψ x‖ ≤ A * Real.exp (B * ‖x‖)) :
    lineDn c₁ (fun x => rsH x * ψ x) = lineDn c₂ (fun x => rsH x * ψ x) := by
  rw [lineDn_rsH_eq, lineDn_rsH_eq]
  congr 2
  exact lineUp_same_gap (φ := fun x => (starRingEnd ℂ) (ψ ((starRingEnd ℂ) x))) hc hno
    (fun x hx => differentiableAt_conj_conj_iff.mpr (hψ _ (conj_mem_dnStrip hx))) (A := A) (B := B)
    (fun x hx => by
      rw [RCLike.norm_conj]
      have := hgrow _ (conj_mem_dnStrip hx)
      rwa [RCLike.norm_conj] at this)

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





theorem slit_of_dnStrip {x : ℂ} {a b : ℝ} (ha : 0 < a) (hx : x.re + x.im ∈ Icc a b) :
    x ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases h : x.im = 0
  · left; have := hx.1; rw [h] at this; linarith
  · right; exact h



theorem norm_ge_of_dnStrip {x : ℂ} {a b : ℝ} (hx : x.re + x.im ∈ Icc a b) (_ha : 0 < a) :
    a / 2 ≤ ‖x‖ := by
  have h1 := Complex.abs_re_le_norm x
  have h2 := Complex.abs_im_le_norm x
  have := hx.1
  have h3 : x.re + x.im ≤ |x.re| + |x.im| := by
    linarith [le_abs_self x.re, le_abs_self x.im]
  linarith



theorem lineDn_cpow_same_gap (s : ℂ) {n : ℕ} {c c' : ℝ} (h : (n : ℝ) < c) (h' : c < n + 1)
    (k : (n : ℝ) < c') (k' : c' < n + 1) :
    lineDn c (fun x => rsH x * x ^ (s - 1)) = lineDn c' (fun x => rsH x * x ^ (s - 1)) := by
  have key : ∀ a b : ℝ, a ≤ b → (n : ℝ) < a → b < n + 1 →
      lineDn a (fun x => rsH x * x ^ (s - 1)) = lineDn b (fun x => rsH x * x ^ (s - 1)) := by
    intro a b hab ha hb
    have ha0 : 0 < a := lt_of_le_of_lt (Nat.cast_nonneg n) ha
    refine lineDn_same_gap hab (fun m hm => ?_) (fun x hx => ?_) (A := ((a / 2) ^ (s - 1).re + 1) *
      Real.exp (π * |(s - 1).im|)) (B := |(s - 1).re|) (fun x hx => norm_cpow_le_of_ge
        (by positivity) (norm_ge_of_dnStrip hx ha0))
    · have h1 : (n : ℝ) < m := lt_of_lt_of_le ha hm.1
      have h2 : (m : ℝ) < n + 1 := lt_of_le_of_lt hm.2 hb
      have h1' : (n : ℤ) < m := by exact_mod_cast h1
      have h2' : m < (n : ℤ) + 1 := by exact_mod_cast h2
      omega
    · exact (differentiableAt_id).cpow (differentiableAt_const _) (slit_of_dnStrip ha0 hx)
  rcases le_total c c' with hcc | hcc
  · exact key c c' hcc h k'
  · exact (key c' c hcc k h').symm





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



/-! ## 4. Residue bookkeeping -/


















theorem solution (s : ℂ) (M : ℕ) {c c₂ : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (h₂ : (M : ℝ) < c₂) (h₂' : c₂ < M + 1) :
    lineDn c (fun x => rsH x * x ^ (s - 1)) =
      (∑ m ∈ Finset.Icc 1 M, (m : ℂ) ^ (s - 1)) + lineDn c₂ (fun x => rsH x * x ^ (s - 1)) := by
  induction M generalizing c₂ with
  | zero =>
    simp only [Finset.Icc_eq_empty_of_lt (by norm_num : (0 : ℕ) < 1), Finset.sum_empty, zero_add]
    exact lineDn_cpow_same_gap s (n := 0) (by simpa using hc) (by simpa using hc1)
      (by simpa using h₂) (by simpa using h₂')
  | succ M ih =>
    have hM := ih (c₂ := (M : ℝ) + 1 / 2) (by linarith) (by linarith)
    have hc₂ : 0 < c₂ := lt_of_le_of_lt (by positivity) h₂
    have hcross := lineDn_cross (ψ := fun x => x ^ (s - 1)) (n := (M : ℤ) + 1)
      (c₁ := (M : ℝ) + 1 / 2) (c₂ := c₂) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; push_cast at h₂; linarith) (by push_cast; push_cast at h₂'; linarith)
      (fun x hx => (differentiableAt_id).cpow (differentiableAt_const _)
        (slit_of_dnStrip (by positivity) hx))
      (A := ((((M : ℝ) + 1 / 2) / 2) ^ (s - 1).re + 1) * Real.exp (π * |(s - 1).im|))
      (B := |(s - 1).re|) (fun x hx => norm_cpow_le_of_ge (by positivity)
        (norm_ge_of_dnStrip hx (by positivity)))
    rw [hM, Finset.sum_Icc_succ_top (by omega)]
    rw [hcross]
    push_cast
    ring
