-- Prove2me | solution 1 for ZetaZeroLocalization.completedRiemannZeta0_conj
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:27:10.639364+00:00
-- url     : https://prove2.me/submissions/0bab9d0a-7ce3-4cae-8dbb-b2d08c8b7fbc

import Mathlib



/-!
# Λ(1/2 + it) is real on the critical line (Stage-1 real-on-line prelude)

This is the one genuine analytic sub-lemma of Stage 1 of the zeta-zero-localization
project.  It establishes that the completed Riemann zeta function
`Λ = completedRiemannZeta` takes real values on the critical line `Re s = 1/2`,
so that sign-changes of `Λ(1/2 + it)` certify zeros on the critical line.

The proof derives the conjugation symmetry
`completedRiemannZeta (conj s) = conj (completedRiemannZeta s)` from the fact that
`Λ` has real Dirichlet/Mellin coefficients.  Concretely we conjugate the termwise
representation
`Λ s = π^(-s/2) · Γ(s/2) · Σ 1/n^s`  (valid for `1 < re s`)
and propagate the resulting identity to all of `ℂ` by the identity principle for the
entire function `Λ₀`.  Combined with the functional equation
`Λ(1 - s) = Λ(s)` and the observation that at `s = 1/2 + t·I` one has
`conj s = 1 - s`, this forces `Λ(1/2 + t·I)` to be fixed by conjugation, hence real.

Note: `conjecture1_proved = False`.  This lemma is a kernel prelude only; it does NOT
prove RH.  It records the real-on-line symmetry that downstream sign-change arguments
consume.
-/

open Complex Filter Topology ComplexConjugate

section
namespace ZetaZeroLocalization
end ZetaZeroLocalization
open ZetaZeroLocalization


theorem solution (s : ℂ) :
    completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) := by
  -- `g z := conj (Λ₀ (conj z))` is entire (composition of entire `Λ₀` with conjugation).
  have hg_an : AnalyticOnNhd ℂ (fun z ↦ conj (completedRiemannZeta₀ (conj z))) Set.univ :=
    DifferentiableOn.analyticOnNhd
      (fun z _ ↦
        (differentiableAt_conj_conj_iff.mpr
          differentiable_completedZeta₀.differentiableAt).differentiableWithinAt)
      isOpen_univ
  have hf_an : AnalyticOnNhd ℂ completedRiemannZeta₀ Set.univ :=
    analyticOnNhd_univ_iff_differentiable.mpr differentiable_completedZeta₀
  -- On `1 < re z`, conjugating the Mellin representation of `Λ` gives `conj (Λ (conj z)) = Λ z`.
  have hΛ (z : ℂ) (hz : 1 < z.re) :
      conj (completedRiemannZeta (conj z)) = completedRiemannZeta z := by
    rw [completedZeta_eq_tsum_of_one_lt_re (by rwa [conj_re]),
      completedZeta_eq_tsum_of_one_lt_re hz]
    have hπ : (Real.pi : ℂ).arg ≠ Real.pi := by
      rw [arg_ofReal_of_nonneg Real.pi_pos.le]; exact fun h => Real.pi_ne_zero h.symm
    rw [map_mul, map_mul, conj_tsum]
    congr 1
    · congr 1
      · -- `conj (π ^ (-(conj z) / 2)) = π ^ (-z / 2)`
        rw [show (-(conj z) / 2) = conj (-z / 2) by
              simp only [map_div₀, map_neg, map_ofNat],
          ← conj_cpow _ _ hπ, conj_ofReal]
      · -- `conj (Γ (conj z / 2)) = Γ (z / 2)`
        rw [show (conj z / 2) = conj (z / 2) by simp only [map_div₀, map_ofNat],
          Gamma_conj, conj_conj]
    · -- termwise: `conj (1 / (n : ℂ) ^ conj z) = 1 / (n : ℂ) ^ z`
      refine tsum_congr (fun n => ?_)
      have hn : (n : ℂ).arg ≠ Real.pi := by
        rw [natCast_arg]; exact fun h => Real.pi_ne_zero h.symm
      rw [map_div₀, map_one, ← conj_cpow _ _ hn, conj_natCast]
  -- Transfer to `Λ₀` on `1 < re z` using `Λ₀ z = Λ z + 1/z + 1/(1 - z)`.
  have hΛ₀ (z : ℂ) (hz : 1 < z.re) :
      conj (completedRiemannZeta₀ (conj z)) = completedRiemannZeta₀ z := by
    -- Expand both `Λ₀` via `Λ₀ w = Λ w + 1/w + 1/(1 - w)`, then conjugate the pieces.
    rw [show completedRiemannZeta₀ (conj z)
          = completedRiemannZeta (conj z) + 1 / (conj z) + 1 / (1 - conj z) by
            rw [completedRiemannZeta_eq]; ring,
      show completedRiemannZeta₀ z
          = completedRiemannZeta z + 1 / z + 1 / (1 - z) by
            rw [completedRiemannZeta_eq]; ring,
      map_add, map_add, hΛ z hz, map_div₀, map_one, map_div₀, map_one, map_sub, map_one,
      conj_conj]
  -- Identity principle: the two entire functions agree on the preconnected set `univ`.
  have heq : Set.EqOn (fun z ↦ conj (completedRiemannZeta₀ (conj z)))
      completedRiemannZeta₀ Set.univ := by
    apply hg_an.eqOn_of_preconnected_of_eventuallyEq hf_an isPreconnected_univ
      (Set.mem_univ 2)
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz using hΛ₀ z hz
  -- Evaluate at `s`, then conjugate both sides.
  have hval := heq (Set.mem_univ s)
  simp only at hval
  have := congrArg (starRingEnd ℂ) hval
  simpa [conj_conj] using this
