-- Prove2me | solution 1 for WardTakahashi.phaseRotate_measurePreserving
-- status  : ACCEPTED   (prove)
-- author  : @37720879
-- created : 2026-09-28T08:50:02.793036+00:00
-- url     : https://prove2.me/submissions/2b72d24a-4798-4382-b333-1eafd3ce5b7c

import Mathlib
import Definitions.Def_WardTakahashi_LatticeU1

open MeasureTheory Complex WardTakahashi

theorem solution {N : ℕ} (θ : ℝ) :
    MeasurePreserving (phaseRotate (N := N) θ) volume volume := by
  have h : MeasurePreserving
      (fun (φ : Fin N → ℂ) y => rotation (Circle.exp θ) (φ y)) :=
    volume_preserving_pi fun _ =>
      LinearIsometryEquiv.measurePreserving (rotation (Circle.exp θ))
  change @MeasurePreserving (Fin N → ℂ) (Fin N → ℂ)
    MeasurableSpace.pi MeasurableSpace.pi
    (fun φ y => Complex.exp ((θ : ℂ) * I) * φ y) volume volume
  simpa only [rotation_apply, Circle.coe_exp] using h
