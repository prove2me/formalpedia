-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.hardcore_vertex_entropy_strict_mono
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:20:16.780536+00:00
-- url     : https://prove2.me/submissions/4c108397-2a53-4f06-b7a7-5f2c43b80f08

import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_vertex_entropy_strict_derivative
import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_entropy_integral_derivative
import Mathlib
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (d : ℕ) (hd : 2 ≤ d) (η : Measure ℝ) [IsProbabilityMeasure η]
    (hb : ∀ᵐ h ∂η, -1 ≤ h ∧ h ≤ 1)
    (hint : Integrable (fun h : ℝ => h) η)
    (hmean : (∫ h : ℝ, h ∂η) = 0) (hn : ¬(∀ᵐ h ∂η, h=0)) :
    StrictMonoOn (fun t : ℝ => ∫ hs : Fin d → ℝ,
      let V := ((∏ i, (1+t*hs i)) + t*(∏ i, (1-hs i)))/(1+t)
      V * Real.log V ∂(Measure.pi fun _ : Fin d => η)) (Ioo 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 1)
  · intro t ht
    exact (hardcore_entropy_integral_derivative d η hb t ht.1 ht.2).continuousAt.continuousWithinAt
  · intro t ht
    have ht' : t ∈ Ioo (0:ℝ) 1 := interior_subset ht
    exact hardcore_vertex_entropy_strict_derivative d hd η t ht'.1 ht'.2 hb hint hmean hn
