-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.hardcore_tilted_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:44:56.187195+00:00
-- url     : https://prove2.me/submissions/b8c2ab64-f87f-4bb5-b283-09b22e76d5db

import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal

theorem solution (η : Measure ℝ) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hb : ∀ᵐ h ∂η, -1 ≤ h ∧ h ≤ 1)
    (hn : ¬ (∀ᵐ h ∂η, h = 0)) :
    Measure.map (fun h : ℝ => (1-h)/(1+θ*h))
      (η.withDensity (fun h : ℝ => ENNReal.ofReal (1+θ*h))) ≠ Measure.dirac 1 := by
  let W := fun h : ℝ => (1-h)/(1+θ*h)
  let tilt := η.withDensity (fun h : ℝ => ENNReal.ofReal (1+θ*h))
  have hW : Measurable W := by dsimp [W]; fun_prop
  have hdens : Measurable (fun h : ℝ => ENNReal.ofReal (1+θ*h)) := by fun_prop
  have hpos : ∀ᵐ h ∂η, ENNReal.ofReal (1+θ*h) ≠ 0 := by
    filter_upwards [hb] with h hh
    have hd : 0 < 1+θ*h := by
      nlinarith [mul_nonneg hθ (show 1+h ≥ 0 by linarith)]
    exact (ENNReal.ofReal_pos.mpr hd).ne'
  intro h
  apply hn
  have heq : ∀ᵐ w ∂Measure.map W tilt, w = 1 := by
    rw [h]
    exact (ae_dirac_iff (measurableSet_singleton (1:ℝ))).2 rfl
  have ht : ∀ᵐ h ∂tilt, W h = 1 :=
    (ae_map_iff hW.aemeasurable (measurableSet_singleton (1:ℝ))).1 heq
  have he : ∀ᵐ h ∂η, W h = 1 :=
    (withDensity_absolutelyContinuous' hdens.aemeasurable hpos).ae_le ht
  filter_upwards [hb,he] with h hh he'
  have hd : 0 < 1+θ*h := by
    nlinarith [mul_nonneg hθ (show 1+h ≥ 0 by linarith)]
  dsimp [W] at he'
  have hmul := (div_eq_iff hd.ne').1 he'
  have ht : 0 < 1+θ := by linarith
  have hz : (1+θ)*h = 0 := by nlinarith [hmul]
  exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt ht)
