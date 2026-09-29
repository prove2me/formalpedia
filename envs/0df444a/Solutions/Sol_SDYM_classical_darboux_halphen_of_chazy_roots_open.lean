-- Prove2me | solution 1 for SDYM.classical_darboux_halphen_of_chazy_roots_open
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T23:28:37.996955+00:00
-- url     : https://prove2.me/submissions/e4e4b21c-aa1b-407a-ac4c-b545520aec76

import Mathlib
import Definitions.Def_SDYM_ChazyEquations
import Definitions.Def_SDYM_DarbouxHalphenRamanujan

set_option autoImplicit false

theorem sdym_vieta_11ac {a b c w1 w2 w3 : ℂ}
    (h : ∀ z : ℂ, z ^ 3 + a / 2 * z ^ 2 + b / 2 * z + c / 12
      = (z - w1) * (z - w2) * (z - w3)) :
    a = -2 * (w1 + w2 + w3) ∧ b = 2 * (w1 * w2 + w2 * w3 + w3 * w1) ∧
      c = -12 * (w1 * w2 * w3) := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h (-1)
  refine ⟨?_, ?_, ?_⟩
  · linear_combination h1 + h2 - 2 * h0
  · linear_combination h1 - h2
  · linear_combination 12 * h0

theorem sdym_dh_core_11ac {w1 w2 w3 d1 d2 d3 : ℂ}
    (E1 : d1 + d2 + d3 = -(2 * (w1 * w2 + w2 * w3 + w3 * w1)) / 2)
    (E2 : d1 * w2 + w1 * d2 + (d2 * w3 + w2 * d3) + (d3 * w1 + w3 * d1)
      = -12 * (w1 * w2 * w3) / 2)
    (E3 : d1 * w2 * w3 + w1 * d2 * w3 + w1 * w2 * d3
      = -(2 * (-2 * (w1 + w2 + w3)) * (-12 * (w1 * w2 * w3))
          - 3 * (2 * (w1 * w2 + w2 * w3 + w3 * w1)) ^ 2) / 12)
    (h12 : w1 ≠ w2) (h23 : w2 ≠ w3) (h31 : w3 ≠ w1) :
    d1 = w2 * w3 - w1 * (w2 + w3) ∧ d2 = w3 * w1 - w2 * (w3 + w1) ∧
      d3 = w1 * w2 - w3 * (w1 + w2) := by
  have s12 : w1 - w2 ≠ 0 := sub_ne_zero.mpr h12
  have s23 : w2 - w3 ≠ 0 := sub_ne_zero.mpr h23
  have s31 : w3 - w1 ≠ 0 := sub_ne_zero.mpr h31
  have k1 : (d1 - (w2 * w3 - w1 * (w2 + w3))) * ((w1 - w2) * (w1 - w3)) = 0 := by
    linear_combination E3 - w1 * E2 + w1 ^ 2 * E1
  have k2 : (d2 - (w3 * w1 - w2 * (w3 + w1))) * ((w2 - w3) * (w2 - w1)) = 0 := by
    linear_combination E3 - w2 * E2 + w2 ^ 2 * E1
  have k3 : (d3 - (w1 * w2 - w3 * (w1 + w2))) * ((w3 - w1) * (w3 - w2)) = 0 := by
    linear_combination E3 - w3 * E2 + w3 ^ 2 * E1
  have n1 : (w1 - w2) * (w1 - w3) ≠ 0 :=
    mul_ne_zero s12 (by intro h; exact s31 (by linear_combination -h))
  have n2 : (w2 - w3) * (w2 - w1) ≠ 0 :=
    mul_ne_zero s23 (by intro h; exact s12 (by linear_combination -h))
  have n3 : (w3 - w1) * (w3 - w2) ≠ 0 :=
    mul_ne_zero s31 (by intro h; exact s23 (by linear_combination -h))
  refine ⟨?_, ?_, ?_⟩
  · exact sub_eq_zero.mp ((mul_eq_zero.mp k1).resolve_right n1)
  · exact sub_eq_zero.mp ((mul_eq_zero.mp k2).resolve_right n2)
  · exact sub_eq_zero.mp ((mul_eq_zero.mp k3).resolve_right n3)

open SDYM in
theorem solution
    (s : Set ℂ) (hs : IsOpen s) (y y₁ y₂ w₁ w₂ w₃ : ℂ → ℂ)
    (hy : IsChazySolution s y y₁ y₂)
    (hw₁ : ∀ t ∈ s, DifferentiableAt ℂ w₁ t)
    (hw₂ : ∀ t ∈ s, DifferentiableAt ℂ w₂ t)
    (hw₃ : ∀ t ∈ s, DifferentiableAt ℂ w₃ t)
    (hroots : ∀ t ∈ s, ∀ z : ℂ,
      z ^ 3 + y t / 2 * z ^ 2 + y₁ t / 2 * z + y₂ t / 12
        = (z - w₁ t) * (z - w₂ t) * (z - w₃ t))
    (hdist : ∀ t ∈ s, w₁ t ≠ w₂ t ∧ w₂ t ≠ w₃ t ∧ w₃ t ≠ w₁ t) :
    IsClassicalDHSolution s w₁ w₂ w₃ := by
  obtain ⟨hy0, hy1, hy2⟩ := hy
  have key : ∀ t ∈ s,
      deriv w₁ t = w₂ t * w₃ t - w₁ t * (w₂ t + w₃ t) ∧
      deriv w₂ t = w₃ t * w₁ t - w₂ t * (w₃ t + w₁ t) ∧
      deriv w₃ t = w₁ t * w₂ t - w₃ t * (w₁ t + w₂ t) := by
    intro t ht
    have ev : ∀ᶠ x in nhds t, x ∈ s := hs.mem_nhds ht
    have h1 := (hw₁ t ht).hasDerivAt
    have h2 := (hw₂ t ht).hasDerivAt
    have h3 := (hw₃ t ht).hasDerivAt
    obtain ⟨va, vb, vc⟩ := sdym_vieta_11ac (hroots t ht)
    -- first symmetric function
    have D1 : HasDerivAt (fun x => w₁ x + w₂ x + w₃ x)
        (deriv w₁ t + deriv w₂ t + deriv w₃ t) t := (h1.add h2).add h3
    have D1' : HasDerivAt (fun x => w₁ x + w₂ x + w₃ x) (-(y₁ t) / 2) t := by
      have : HasDerivAt (fun x => -(y x) / 2) (-(y₁ t) / 2) t :=
        ((hy0 t ht).neg).div_const 2
      refine this.congr_of_eventuallyEq ?_
      filter_upwards [ev] with x hx
      have := (sdym_vieta_11ac (hroots x hx)).1
      rw [this]; ring
    have D2 : HasDerivAt (fun x => w₁ x * w₂ x + w₂ x * w₃ x + w₃ x * w₁ x)
        (deriv w₁ t * w₂ t + w₁ t * deriv w₂ t + (deriv w₂ t * w₃ t + w₂ t * deriv w₃ t)
          + (deriv w₃ t * w₁ t + w₃ t * deriv w₁ t)) t :=
      ((h1.mul h2).add (h2.mul h3)).add (h3.mul h1)
    have D2' : HasDerivAt (fun x => w₁ x * w₂ x + w₂ x * w₃ x + w₃ x * w₁ x)
        (y₂ t / 2) t := by
      have : HasDerivAt (fun x => y₁ x / 2) (y₂ t / 2) t := (hy1 t ht).div_const 2
      refine this.congr_of_eventuallyEq ?_
      filter_upwards [ev] with x hx
      have := (sdym_vieta_11ac (hroots x hx)).2.1
      rw [this]; ring
    have D3 : HasDerivAt (fun x => w₁ x * w₂ x * w₃ x)
        ((deriv w₁ t * w₂ t + w₁ t * deriv w₂ t) * w₃ t + w₁ t * w₂ t * deriv w₃ t) t :=
      (h1.mul h2).mul h3
    have D3' : HasDerivAt (fun x => w₁ x * w₂ x * w₃ x)
        (-(2 * y t * y₂ t - 3 * y₁ t ^ 2) / 12) t := by
      have : HasDerivAt (fun x => -(y₂ x) / 12)
          (-(2 * y t * y₂ t - 3 * y₁ t ^ 2) / 12) t := ((hy2 t ht).neg).div_const 12
      refine this.congr_of_eventuallyEq ?_
      filter_upwards [ev] with x hx
      have := (sdym_vieta_11ac (hroots x hx)).2.2
      rw [this]; ring
    have E1 := D1.unique D1'
    have E2 := D2.unique D2'
    have E3 := D3.unique D3'
    rw [vb] at E1
    rw [vc] at E2
    rw [va, vb, vc] at E3
    obtain ⟨d12, d23, d31⟩ := hdist t ht
    exact sdym_dh_core_11ac E1 E2 (by linear_combination E3) d12 d23 d31
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · rw [← (key t ht).1]; exact (hw₁ t ht).hasDerivAt
  · rw [← (key t ht).2.1]; exact (hw₂ t ht).hasDerivAt
  · rw [← (key t ht).2.2]; exact (hw₃ t ht).hasDerivAt
