-- Prove2me | solution 1 for WardTakahashi.noether_current_conservation
-- status  : ACCEPTED   (prove)
-- author  : @37720879
-- created : 2026-09-28T08:48:19.457978+00:00
-- url     : https://prove2.me/submissions/3f58732e-1c01-439e-9cfe-9bc646930027

import Mathlib
import Definitions.Def_WardTakahashi_LatticeU1

open MeasureTheory Complex WardTakahashi

theorem solution {N : ℕ} (S : FieldConfig N → ℝ)
    (hS : Differentiable ℝ S) (hinv : IsU1Invariant S) (φ : FieldConfig N) :
    ∑ x, localVar x S φ = 0 := by
  have harg : HasDerivAt (fun t : ℝ => (t : ℂ) * I) I 0 := by
    simpa using (HasDerivAt.ofReal_comp (hasDerivAt_id (0 : ℝ))).mul_const I
  have hcurve : HasDerivAt (fun t : ℝ => phaseRotate t φ)
      (fun y => I * φ y) 0 := by
    apply hasDerivAt_pi.mpr
    intro y
    simpa [phaseRotate] using (harg.cexp.mul_const (φ y))
  have hzero : phaseRotate (N := N) 0 φ = φ := by
    funext y
    simp [phaseRotate]
  have hderiv : fderiv ℝ S φ (fun y => I * φ y) = 0 := by
    have hs' : HasFDerivAt S (fderiv ℝ S φ) (phaseRotate 0 φ) := by
      simpa [hzero] using (hS φ).hasFDerivAt
    have hcomp := hs'.comp_hasDerivAt 0 hcurve
    change HasDerivAt (fun t : ℝ => S (phaseRotate t φ))
      (fderiv ℝ S φ (fun y => I * φ y)) 0 at hcomp
    have hfun : (fun t : ℝ => S (phaseRotate t φ)) = (fun _ => S φ) := by
      funext t
      exact hinv t φ
    rw [hfun] at hcomp
    exact hcomp.unique (hasDerivAt_const (0 : ℝ) (S φ))
  have hgen : (∑ x : Fin N, localGen x φ) = (fun y => I * φ y) := by
    funext y
    simp [localGen, Finset.sum_apply]
  calc
    ∑ x, localVar x S φ = fderiv ℝ S φ (∑ x, localGen x φ) := by
      simp [localVar, map_sum]
    _ = 0 := by rw [hgen]; exact hderiv
