-- Prove2me | solution 1 for ParameterizedCalculus.smooth_scalar_linear_transport
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T18:44:06.052202+00:00
-- url     : https://prove2.me/submissions/6dd5b337-d727-4aed-99e4-85d0daa88a21

import Theorems.Thm_ParameterizedCalculus_smooth_unit_interval_integral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring

open scoped ContDiff
open Set MeasureTheory

theorem solution {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (q : ℝ → P → ℝ)
    (hq : ContDiff ℝ ∞ (fun p : ℝ × P => q p.1 p.2)) :
    ∃ lam : ℝ → P → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × P => lam p.1 p.2) ∧
      (∀ y, lam 0 y = 1) ∧ (∀ t y, 0 < lam t y) ∧
      ∀ y (f : ℝ → ℝ),
        (∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (q t y * f t) t) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, f t = lam t y * f 0 := by
  let A : ℝ → P → ℝ := fun t y => ∫ s in (0 : ℝ)..t, q s y
  have hscaled : ContDiff ℝ ∞ (fun z : (ℝ × P) × ℝ => q (z.1.1 * z.2) z.1.2) :=
    hq.comp ((contDiff_fst.fst.mul contDiff_snd).prodMk contDiff_fst.snd)
  have hint := ParameterizedCalculus.smooth_unit_interval_integral
    (fun p : ℝ × P => fun s => q (p.1 * s) p.2) hscaled
  have hA : ContDiff ℝ ∞ (fun p : ℝ × P => A p.1 p.2) := by
    have heq : (fun p : ℝ × P => A p.1 p.2) =
        (fun p : ℝ × P => p.1 * ∫ s in (0 : ℝ)..1, q (p.1 * s) p.2) := by
      funext p
      simpa [A, smul_eq_mul] using
        (intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1)
          (fun s => q s p.2) p.1).symm
    rw [heq]
    exact contDiff_fst.mul hint
  have hAd : ∀ t y, HasDerivAt (fun s => A s y) (q t y) t := by
    intro t y
    exact (hq.continuous.comp (continuous_id.prodMk continuous_const)).integral_hasStrictDerivAt
      0 t |>.hasDerivAt
  refine ⟨fun t y => Real.exp (A t y), hA.exp, ?_, ?_, ?_⟩
  · intro y
    simp [A]
  · intro t y
    exact Real.exp_pos _
  · intro y f hf t ht
    have hd : ∀ s ∈ Icc (0 : ℝ) 1,
        HasDerivAt (fun r => f r * Real.exp (-A r y)) 0 s := by
      intro s hs
      have hm : HasDerivAt (fun r => f r * Real.exp (-A r y))
          (q s y * f s * Real.exp (-A s y) +
            f s * (Real.exp (-A s y) * -q s y)) s := by
        convert! (hf s hs).mul ((hAd s y).neg.exp) using 1
      have hz : q s y * f s * Real.exp (-A s y) +
          f s * (Real.exp (-A s y) * -q s y) = 0 := by ring
      rw [hz] at hm
      exact hm
    have hc : ContinuousOn (fun r => f r * Real.exp (-A r y)) (Icc (0 : ℝ) 1) := by
      intro s hs
      exact (hd s hs).continuousAt.continuousWithinAt
    have heq := constant_of_has_deriv_right_zero hc
      (fun s hs => (hd s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt) t ht
    have hr : f t / Real.exp (A t y) = f 0 := by
      simpa [A, Real.exp_neg, div_eq_mul_inv] using heq
    simpa [mul_comm] using (div_eq_iff (Real.exp_ne_zero _)).mp hr
