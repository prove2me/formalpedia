-- Prove2me | solution 1 for SDYM.rankin_discriminant_ode_open
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T02:29:05.44907+00:00
-- url     : https://prove2.me/submissions/10737af1-55ce-42d7-afd6-cee667a5a37c

import Mathlib
import Definitions.Def_SDYM_ChazyEquations
import Definitions.Def_SDYM_DarbouxHalphenRamanujan

set_option autoImplicit false

open SDYM in
theorem solution
    (s : Set ℂ) (hs : IsOpen s) (D D₁ D₂ D₃ D₄ y₁ y₂ : ℂ → ℂ)
    (hD : ∀ t ∈ s, HasDerivAt D (D₁ t) t)
    (hD₁ : ∀ t ∈ s, HasDerivAt D₁ (D₂ t) t)
    (hD₂ : ∀ t ∈ s, HasDerivAt D₂ (D₃ t) t)
    (hD₃ : ∀ t ∈ s, HasDerivAt D₃ (D₄ t) t)
    (hDne : ∀ t ∈ s, D t ≠ 0)
    (hchazy : IsChazySolution s (fun z => D₁ z / (2 * D z)) y₁ y₂) :
    ∀ t ∈ s, D t ^ 3 * D₄ t - 5 * D t ^ 2 * D₁ t * D₃ t
      - 3 / 2 * D t ^ 2 * D₂ t ^ 2 + 12 * D t * D₁ t ^ 2 * D₂ t
      - 13 / 2 * D₁ t ^ 4 = 0 := by
  obtain ⟨hc1, hc2, hc3⟩ := hchazy
  -- E1 : y₁ on s
  have E1 : ∀ t ∈ s, y₁ t = (D t * D₂ t - D₁ t ^ 2) / (2 * D t ^ 2) := by
    intro t ht
    have hne := hDne t ht
    have h := (hD₁ t ht).div ((hD t ht).const_mul 2) (mul_ne_zero two_ne_zero hne)
    have h' : HasDerivAt (fun z => D₁ z / (2 * D z))
        ((D t * D₂ t - D₁ t ^ 2) / (2 * D t ^ 2)) t := by
      refine h.congr_deriv ?_
      field_simp
    exact (hc1 t ht).unique h'
  -- E2 : y₂ on s
  have E2 : ∀ t ∈ s, y₂ t = (D t ^ 2 * D₃ t - 3 * D t * D₁ t * D₂ t + 2 * D₁ t ^ 3)
      / (2 * D t ^ 3) := by
    intro t ht
    have hne := hDne t ht
    have h := (((hD t ht).mul (hD₂ t ht)).sub ((hD₁ t ht).pow 2)).div
      (((hD t ht).pow 2).const_mul 2) (mul_ne_zero two_ne_zero (pow_ne_zero 2 hne))
    have h' : HasDerivAt (fun z => (D z * D₂ z - D₁ z ^ 2) / (2 * D z ^ 2))
        ((D t ^ 2 * D₃ t - 3 * D t * D₁ t * D₂ t + 2 * D₁ t ^ 3) / (2 * D t ^ 3)) t := by
      refine h.congr_deriv ?_
      simp only [Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, Nat.cast_ofNat,
        Nat.reduceSub, pow_one]
      field_simp
      try ring
    have hev : (fun z => (D z * D₂ z - D₁ z ^ 2) / (2 * D z ^ 2)) =ᶠ[nhds t] y₁ := by
      filter_upwards [hs.mem_nhds ht] with z hz
      exact (E1 z hz).symm
    exact ((hc2 t ht).congr_of_eventuallyEq hev).unique h'
  intro t ht
  have hne := hDne t ht
  have h := ((((((hD t ht).pow 2).mul (hD₃ t ht)).sub
      ((((hD t ht).mul (hD₁ t ht)).mul (hD₂ t ht)).const_mul 3)).add
      (((hD₁ t ht).pow 3).const_mul 2))).div
    (((hD t ht).pow 3).const_mul 2) (mul_ne_zero two_ne_zero (pow_ne_zero 3 hne))
  have h' : HasDerivAt
      (fun z => (D z ^ 2 * D₃ z - 3 * (D z * D₁ z * D₂ z) + 2 * D₁ z ^ 3) / (2 * D z ^ 3))
      (((D t ^ 2 * D₄ t - D t * D₁ t * D₃ t - 3 * D t * D₂ t ^ 2 + 3 * D₁ t ^ 2 * D₂ t) * D t
        - 3 * (D t ^ 2 * D₃ t - 3 * D t * D₁ t * D₂ t + 2 * D₁ t ^ 3) * D₁ t)
        / (2 * D t ^ 4)) t := by
    refine h.congr_deriv ?_
    simp only [Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Nat.cast_ofNat,
      Nat.reduceSub, pow_one]
    field_simp
    try ring
  have hev : (fun z => (D z ^ 2 * D₃ z - 3 * (D z * D₁ z * D₂ z) + 2 * D₁ z ^ 3) / (2 * D z ^ 3))
      =ᶠ[nhds t] y₂ := by
    filter_upwards [hs.mem_nhds ht] with z hz
    rw [E2 z hz]
    ring
  have E3 := ((hc3 t ht).congr_of_eventuallyEq hev).unique h'
  rw [E1 t ht, E2 t ht] at E3
  have key : D t ^ 3 * D₄ t - 5 * D t ^ 2 * D₁ t * D₃ t
      - 3 / 2 * D t ^ 2 * D₂ t ^ 2 + 12 * D t * D₁ t ^ 2 * D₂ t
      - 13 / 2 * D₁ t ^ 4 =
      -(2 * D t ^ 4) * ((2 * (D₁ t / (2 * D t)) *
          ((D t ^ 2 * D₃ t - 3 * D t * D₁ t * D₂ t + 2 * D₁ t ^ 3) / (2 * D t ^ 3)) -
          3 * ((D t * D₂ t - D₁ t ^ 2) / (2 * D t ^ 2)) ^ 2) -
        ((D t ^ 2 * D₄ t - D t * D₁ t * D₃ t - 3 * D t * D₂ t ^ 2 + 3 * D₁ t ^ 2 * D₂ t) * D t
          - 3 * (D t ^ 2 * D₃ t - 3 * D t * D₁ t * D₂ t + 2 * D₁ t ^ 3) * D₁ t)
          / (2 * D t ^ 4)) := by
    field_simp
    ring
  rw [key, E3, sub_self, mul_zero]
