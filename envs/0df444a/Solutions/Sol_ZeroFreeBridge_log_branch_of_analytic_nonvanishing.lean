-- Prove2me | solution 1 for ZeroFreeBridge.log_branch_of_analytic_nonvanishing
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:46:16.04449+00:00
-- url     : https://prove2.me/submissions/08e59a53-e886-490d-a04f-5f119795db5a

import Mathlib

/- PHASE 4 (dVP frontier, obligation (i-b') FOUNDATION): the analytic log branch of a
   zero-free function on a disk.

   The entire part `E = logDeriv g = g'/g` (from obligation (i-a)) is bounded via
   Borel-Caratheodory + Cauchy, but BC works with the REAL PART of a holomorphic function,
   and Cauchy bounds a DERIVATIVE by VALUES.  Both need `E` realised as the derivative of an
   analytic `h` with `Re h = log‖g‖`.  On a DISK a zero-free holomorphic `g` admits exactly
   such an `h` (a global branch of `log g`), built here WITHOUT the covering-map machinery:

     * `logDeriv g = g'/g` is holomorphic on the disk (denominator nonvanishing), so by Morera
       (`DifferentiableOn.isExactOn_ball`) it has a PRIMITIVE `h` with `h' = logDeriv g`;
     * pin `h c = Complex.log (g c)`;
     * `φ = g · exp(-h)` has `φ' = exp(-h)·(g' - g·(g'/g)) = 0`, so `φ` is constant on the
       convex disk, `= φ c = g c / g c = 1`; hence `exp∘h = g`;
     * `‖g‖ = ‖exp h‖ = exp(Re h)` gives `Re h = log‖g‖`.

   Output packages `h` differentiable, `deriv h = logDeriv g`, `exp∘h = g`, `Re h = log‖g‖` —
   the object BC and Cauchy consume to bound `‖E‖ ≤ A·L`.  Function-agnostic (any analytic
   zero-free `g`).  conjecture1_proved = False (NOT a proof of RH).
-/


open Complex Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge


theorem solution {g : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (ball c r)) (hne : ∀ z ∈ ball c r, g z ≠ 0) :
    ∃ h : ℂ → ℂ, (∀ z ∈ ball c r, HasDerivAt h (logDeriv g z) z) ∧
      h c = Complex.log (g c) ∧
      (∀ z ∈ ball c r, Complex.exp (h z) = g z) ∧
      (∀ z ∈ ball c r, (h z).re = Real.log ‖g z‖) := by
  have hcball : c ∈ ball c r := mem_ball_self hr
  have hg_an : AnalyticOnNhd ℂ g (ball c r) := hg.analyticOnNhd isOpen_ball
  -- logDeriv g = deriv g / g is holomorphic on the open disk.
  have hlog_diff : DifferentiableOn ℂ (logDeriv g) (ball c r) := by
    intro z hz
    have hderivg : DifferentiableAt ℂ (deriv g) z := (hg_an z hz).deriv.differentiableAt
    have hgz : DifferentiableAt ℂ g z := (hg_an z hz).differentiableAt
    exact (hderivg.div hgz (hne z hz)).differentiableWithinAt
  -- primitive h with h' = logDeriv g, pinned at c.
  obtain ⟨h, hhc, hh⟩ := (hlog_diff.isExactOn_ball).with_val_at c (Complex.log (g c))
  -- φ = g · exp(-h) has zero derivative on the disk.
  have hφ : ∀ z ∈ ball c r, HasDerivAt (fun w => g w * Complex.exp (-h w)) 0 z := by
    intro z hz
    have hgz : HasDerivAt g (deriv g z) z := (hg_an z hz).differentiableAt.hasDerivAt
    have hexp : HasDerivAt (fun w => Complex.exp (-h w))
        (Complex.exp (-h z) * (-(logDeriv g z))) z := ((hh z hz).neg).cexp
    have hprod := hgz.mul hexp
    have hgz0 := hne z hz
    have hderiv0 : deriv g z * Complex.exp (-h z)
        + g z * (Complex.exp (-h z) * (-(logDeriv g z))) = 0 := by
      rw [logDeriv_apply]; field_simp; ring
    rw [hderiv0] at hprod
    exact hprod
  -- hence φ is constant = φ c = 1 on the convex disk.
  have hconst : ∀ z ∈ ball c r,
      (fun w => g w * Complex.exp (-h w)) z = (fun w => g w * Complex.exp (-h w)) c := by
    intro z hz
    refine (convex_ball c r).is_const_of_fderivWithin_eq_zero
      (fun x hx => (hφ x hx).differentiableAt.differentiableWithinAt) ?_ hz hcball
    intro x hx
    rw [fderivWithin_of_isOpen isOpen_ball hx]
    simpa using (hφ x hx).hasFDerivAt.fderiv
  have hφc : g c * Complex.exp (-h c) = 1 := by
    rw [hhc, Complex.exp_neg, Complex.exp_log (hne c hcball), mul_inv_cancel₀ (hne c hcball)]
  -- exp (h z) = g z.
  have hexp_eq : ∀ z ∈ ball c r, Complex.exp (h z) = g z := by
    intro z hz
    have key : g z * Complex.exp (-h z) = 1 := (hconst z hz).trans hφc
    rw [Complex.exp_neg] at key
    have hexpne : Complex.exp (h z) ≠ 0 := Complex.exp_ne_zero _
    field_simp [hexpne] at key
    exact key.symm
  refine ⟨h, hh, hhc, hexp_eq, ?_⟩
  -- Re (h z) = log ‖g z‖.
  intro z hz
  have hnorm : ‖g z‖ = Real.exp (h z).re := by rw [← hexp_eq z hz, Complex.norm_exp]
  rw [hnorm, Real.log_exp]
