-- Prove2me | solution 1 for PrivLearn.Parity.theorem_2_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:12:37.938543+00:00
-- url     : https://prove2.me/submissions/7d25475c-4aaa-4ad5-add1-7f007e0f982e

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy

set_option autoImplicit false
open MeasureTheory

namespace PLP

lemma map_laplace_apply (s c : ℝ) (S : Set ℝ) (hS : MeasurableSet S) :
    ((PrivLearn.Generic.laplace s).map (fun η => c + η)) S =
      ∫⁻ y in S, ENNReal.ofReal (Real.exp (-|y - c| / s) / (2 * s)) := by
  have hm : Measurable (fun η : ℝ => c + η) := measurable_const_add c
  rw [Measure.map_apply hm hS, PrivLearn.Generic.laplace,
    withDensity_apply _ (hm hS)]
  have hmp : MeasurePreserving (fun η : ℝ => c + η) volume volume := measurePreserving_add_left volume c
  have := hmp.setLIntegral_comp_preimage hS
    (f := fun y => ENNReal.ofReal (Real.exp (-|y - c| / s) / (2 * s)))
    (by fun_prop)
  simpa using this

end PLP

theorem solution {D : Type*} {n : ℕ} (f : (Fin n → D) → ℝ) (Δ ε : ℝ) (hΔ : 0 < Δ)
    (hε : 0 < ε) (hf : ∀ z z' : Fin n → D, PrivLearn.Generic.Neighbors z z' → |f z - f z'| ≤ Δ) :
    PrivLearn.Generic.IsDP (fun z => (PrivLearn.Generic.laplace (Δ / ε)).map (fun η => f z + η)) ε := by
  intro z z' hz S hS
  have hs : 0 < Δ / ε := div_pos hΔ hε
  simp only
  rw [PLP.map_laplace_apply _ _ _ hS, PLP.map_laplace_apply _ _ _ hS]
  rw [← lintegral_const_mul' (ENNReal.ofReal (Real.exp ε)) (fun y => ENNReal.ofReal (Real.exp (-|y - f z'| / (Δ / ε) ) / (2 * (Δ / ε)))) ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro y
  beta_reduce
  rw [← ENNReal.ofReal_mul (Real.exp_pos ε).le]
  apply ENNReal.ofReal_le_ofReal
  have h1 : |y - f z'| ≤ |y - f z| + Δ := by
    have := hf z z' hz
    calc |y - f z'| = |(y - f z) + (f z - f z')| := by ring_nf
      _ ≤ |y - f z| + |f z - f z'| := abs_add_le _ _
      _ ≤ _ := by linarith
  have h2 : -|y - f z| / (Δ / ε) ≤ -|y - f z'| / (Δ / ε) + ε := by
    have : Δ / (Δ / ε) = ε := by field_simp
    rw [div_add' _ _ _ hs.ne', div_le_div_iff_of_pos_right hs]
    calc -|y - f z| ≤ -|y - f z'| + Δ := by linarith
      _ = -|y - f z'| + ε * (Δ / ε) := by field_simp
  calc Real.exp (-|y - f z| / (Δ / ε)) / (2 * (Δ / ε)) ≤ Real.exp (-|y - f z'| / (Δ / ε) + ε) / (2 * (Δ / ε)) := by
        apply div_le_div_of_nonneg_right (Real.exp_le_exp.mpr h2) (by positivity)
    _ = _ := by rw [Real.exp_add]; ring
