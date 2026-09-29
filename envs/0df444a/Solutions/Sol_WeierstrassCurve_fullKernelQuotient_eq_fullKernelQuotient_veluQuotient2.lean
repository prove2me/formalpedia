-- Prove2me | solution 1 for WeierstrassCurve.fullKernelQuotient_eq_fullKernelQuotient_veluQuotient2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/832bbd6c-5080-541b-9f9f-b901557c28e6

import Mathlib
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_WeierstrassCurve_VeluPointMap2
import Theorems.Thm_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_fullKernelQuotient_eq_fullKernelQuotient_veluQuotient2

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_fullKernelQuotient_eq_fullKernelQuotient_veluQuotient2.WeierstrassCurve WeierstrassCurve.Affine"

set_option autoImplicit false

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY Affine.slope_of_X_ne a₃ a₁ map a₄ a₂ a₆ Affine.Point.some Affine.negAddY Affine.Point.zero_def toAffine Affine.Point Affine.addX Affine.Point.some_ne_zero Δ Affine.addY Affine.Y_eq_of_X_eq Affine.Point.add_of_X_ne Affine.equation_iff j fullKernelQuotient eq_of_coordsOrZero_eq Affine.Point.coordsOrZero_some oddOrderSummingSet mem_oddOrderSummingSet veluQuotientOfSums_a₄ veluQuotientOfSums_a₆ veluGx veluGy veluQuotient2 veluQuotient2_a₁ veluQuotient2_a₂ veluQuotient2_a₃ veluQuotient2_a₄ veluQuotient2_a₆ veluQuotient2_b₂ velu2XNum velu2YNum velu2X velu2Y velu2X_eq_div velu2Y_eq_div veluPointMap2 veluPointMap2_some_of_ne exists_addMonoidHom_coe_eq_veluPointMap2"
p2m_open "WeierstrassCurve"

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in

private theorem _root_.WeierstrassCurve.veluGx_velu2_chord {x₀ y₀ e L : R}
    (hP : W.toAffine.Equation (x₀ + e) (y₀ + L * e)) (hT : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) :
    3 * W.velu2XNum x₀ y₀ (x₀ + e) ^ 2 + 2 * W.a₂ * W.velu2XNum x₀ y₀ (x₀ + e) * e ^ 2
        + (W.a₄ - 5 * W.veluGx x₀ y₀) * e ^ 4
        - W.a₁ * W.velu2YNum x₀ y₀ (x₀ + e) (y₀ + L * e) * e
      = e ^ 4 * (W.veluGx (x₀ + e) (y₀ + L * e)
          + W.veluGx (W.toAffine.addX (x₀ + e) x₀ L)
              (W.toAffine.addY (x₀ + e) x₀ (y₀ + L * e) L)) := by
  rw [Affine.equation_iff] at hP hT
  simp only [veluGy] at hgy
  simp only [velu2XNum, velu2YNum, veluGx, Affine.addX, Affine.addY, Affine.negAddY,
    Affine.negY]
  linear_combination (-3*L^2*e^2 - 4*L*W.a₁*e^2 - W.a₁^2*e^2 + 3*W.a₁*e*y₀ + W.a₂*e^2 - 6*W.a₂*e*x₀ - 3*W.a₄*e + 3*e^3
      + 3*e^2*x₀ - 9*e*x₀^2) * hP + (3*L^2*e^2 + 4*L*W.a₁*e^2 + W.a₁^2*e^2 - 3*W.a₁*e*y₀ - W.a₂*e^2 + 6*W.a₂*e*x₀ + 3*W.a₄*e - 3*e^3
      - 3*e^2*x₀ + 9*e*x₀^2) * hT + ((-(3*L^3*e^3 + 4*L^2*W.a₁*e^3 + L*W.a₁^2*e^3 - 3*L*W.a₁*e^2*y₀ - L*W.a₂*e^3 + 6*L*W.a₂*e^2*x₀
      + 3*L*W.a₄*e^2 - 3*L*e^4 - 3*L*e^3*x₀ + 9*L*e^2*x₀^2 - W.a₁*e^4))) * hgy

p2m_export "WeierstrassCurve" "veluGx_velu2_chord"
set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in

private theorem _root_.WeierstrassCurve.veluAsym_velu2_chord_reduced {x₀ y₀ e L : R}
    (hP : W.toAffine.Equation (x₀ + e) (y₀ + L * e)) (hT : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) :
    W.velu2XNum x₀ y₀ (x₀ + e) * e ^ 4
          * (W.veluGx (x₀ + e) (y₀ + L * e)
            + W.veluGx (W.toAffine.addX (x₀ + e) x₀ L)
                (W.toAffine.addY (x₀ + e) x₀ (y₀ + L * e) L))
        + W.velu2YNum x₀ y₀ (x₀ + e) (y₀ + L * e)
          * (2 * W.velu2YNum x₀ y₀ (x₀ + e) (y₀ + L * e)
            + W.a₁ * W.velu2XNum x₀ y₀ (x₀ + e) * e + W.a₃ * e ^ 3)
      = e ^ 6 * (((x₀ + e) * W.veluGx (x₀ + e) (y₀ + L * e)
            - (y₀ + L * e) * W.veluGy (x₀ + e) (y₀ + L * e))
          + (W.toAffine.addX (x₀ + e) x₀ L
              * W.veluGx (W.toAffine.addX (x₀ + e) x₀ L)
                  (W.toAffine.addY (x₀ + e) x₀ (y₀ + L * e) L)
            - W.toAffine.addY (x₀ + e) x₀ (y₀ + L * e) L
              * W.veluGy (W.toAffine.addX (x₀ + e) x₀ L)
                  (W.toAffine.addY (x₀ + e) x₀ (y₀ + L * e) L))) := by
  rw [Affine.equation_iff] at hP hT
  simp only [veluGy] at hgy
  simp only [velu2XNum, velu2YNum, veluGx, veluGy, Affine.addX, Affine.addY, Affine.negAddY,
    Affine.negY]
  linear_combination (-5*L^4*e^4 - 12*L^3*W.a₁*e^4 - 9*L^2*W.a₁^2*e^4 + 2*L^2*W.a₁*e^3*y₀ + 6*L^2*W.a₂*e^4
      - 4*L^2*W.a₂*e^3*x₀ - 2*L^2*W.a₄*e^3 + 11*L^2*e^5 + 18*L^2*e^4*x₀ - 6*L^2*e^3*x₀^2
      - 2*L*W.a₁^3*e^4 + 3*L*W.a₁^2*e^3*y₀ + 8*L*W.a₁*W.a₂*e^4 - 6*L*W.a₁*W.a₂*e^3*x₀
      - 3*L*W.a₁*W.a₄*e^3 + 14*L*W.a₁*e^5 + 24*L*W.a₁*e^4*x₀ - 9*L*W.a₁*e^3*x₀^2 + 2*L*e^4*y₀
      + W.a₁^3*e^3*y₀ + 2*W.a₁^2*W.a₂*e^4 - 2*W.a₁^2*W.a₂*e^3*x₀ - W.a₁^2*W.a₄*e^3
      + 3*W.a₁^2*e^5 + 6*W.a₁^2*e^4*x₀ - 3*W.a₁^2*e^3*x₀^2 + 3*W.a₁*e^4*y₀ - W.a₂^2*e^4
      - 5*W.a₂*e^5 - 10*W.a₂*e^4*x₀ - 2*W.a₄*e^4 - 6*e^6 - 15*e^5*x₀ - 15*e^4*x₀^2) * hP + (5*L^4*e^4 + 12*L^3*W.a₁*e^4 + 9*L^2*W.a₁^2*e^4 - 2*L^2*W.a₁*e^3*y₀ - 6*L^2*W.a₂*e^4
      + 4*L^2*W.a₂*e^3*x₀ + 2*L^2*W.a₄*e^3 - 11*L^2*e^5 - 18*L^2*e^4*x₀ + 6*L^2*e^3*x₀^2
      + 2*L*W.a₁^3*e^4 - 3*L*W.a₁^2*e^3*y₀ - 8*L*W.a₁*W.a₂*e^4 + 6*L*W.a₁*W.a₂*e^3*x₀
      + 3*L*W.a₁*W.a₄*e^3 - 14*L*W.a₁*e^5 - 24*L*W.a₁*e^4*x₀ + 9*L*W.a₁*e^3*x₀^2 - 2*L*e^4*y₀
      - W.a₁^3*e^3*y₀ - 2*W.a₁^2*W.a₂*e^4 + 2*W.a₁^2*W.a₂*e^3*x₀ + W.a₁^2*W.a₄*e^3
      - 3*W.a₁^2*e^5 - 6*W.a₁^2*e^4*x₀ + 3*W.a₁^2*e^3*x₀^2 - 3*W.a₁*e^4*y₀ + W.a₂^2*e^4
      + 5*W.a₂*e^5 + 10*W.a₂*e^4*x₀ + 2*W.a₄*e^4 + 6*e^6 + 15*e^5*x₀ + 15*e^4*x₀^2) * hT + ((-(5*L^5*e^5 + 12*L^4*W.a₁*e^5 + 9*L^3*W.a₁^2*e^5 - 2*L^3*W.a₁*e^4*y₀ - 6*L^3*W.a₂*e^5
      + 4*L^3*W.a₂*e^4*x₀ + 2*L^3*W.a₄*e^4 - 14*L^3*e^6 - 18*L^3*e^5*x₀ + 6*L^3*e^4*x₀^2
      + 2*L^2*W.a₁^3*e^5 - 3*L^2*W.a₁^2*e^4*y₀ - 8*L^2*W.a₁*W.a₂*e^5 + 6*L^2*W.a₁*W.a₂*e^4*x₀
      + 3*L^2*W.a₁*W.a₄*e^4 - 20*L^2*W.a₁*e^6 - 24*L^2*W.a₁*e^5*x₀ + 9*L^2*W.a₁*e^4*x₀^2
      - 2*L^2*e^5*y₀ - L*W.a₁^3*e^4*y₀ - 2*L*W.a₁^2*W.a₂*e^5 + 2*L*W.a₁^2*W.a₂*e^4*x₀
      + L*W.a₁^2*W.a₄*e^4 - 6*L*W.a₁^2*e^6 - 6*L*W.a₁^2*e^5*x₀ + 3*L*W.a₁^2*e^4*x₀^2
      - 2*L*W.a₁*e^5*y₀ + L*W.a₂^2*e^5 + 8*L*W.a₂*e^6 + 8*L*W.a₂*e^5*x₀ + L*W.a₄*e^5 + 9*L*e^7
      + 24*L*e^6*x₀ + 12*L*e^5*x₀^2 + 3*W.a₁*W.a₂*e^6 + 4*W.a₁*e^7 + 8*W.a₁*e^6*x₀ - W.a₃*e^6
      - e^6*y₀))) * hgy

p2m_export "WeierstrassCurve" "veluAsym_velu2_chord_reduced"

section Field

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

private theorem _root_.WeierstrassCurve.chord_param {x₀ y₀ x y : F} (hx : x ≠ x₀) :
    ∃ e L : F, e ≠ 0 ∧ x = x₀ + e ∧ y = y₀ + L * e ∧ W.toAffine.slope x x₀ y y₀ = L := by
  refine ⟨x - x₀, W.toAffine.slope x x₀ y y₀, sub_ne_zero.mpr hx, by ring, ?_, rfl⟩
  rw [Affine.slope_of_X_ne hx]
  field_simp [sub_ne_zero.mpr hx]
  ring

p2m_export "WeierstrassCurve" "chord_param"

private theorem _root_.WeierstrassCurve.veluGx_velu2 {x₀ y₀ x y : F} (hP : W.toAffine.Equation x y)
    (hT : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) (hx : x ≠ x₀) :
    (W.veluQuotient2 x₀ y₀).veluGx (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y)
      = W.veluGx x y
        + W.veluGx (W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y y₀))
            (W.toAffine.addY x x₀ y (W.toAffine.slope x x₀ y y₀)) := by
  obtain ⟨e, L, he, rfl, rfl, hL⟩ := W.chord_param (y₀ := y₀) (y := y) hx
  rw [hL]
  have key := W.veluGx_velu2_chord hP hT hgy
  have hsub : x₀ + e - x₀ = e := by ring
  have hX : W.velu2X x₀ y₀ (x₀ + e) = W.velu2XNum x₀ y₀ (x₀ + e) / e ^ 2 := by
    rw [W.velu2X_eq_div x₀ y₀ hx, hsub]
  have hY : W.velu2Y x₀ y₀ (x₀ + e) (y₀ + L * e)
      = W.velu2YNum x₀ y₀ (x₀ + e) (y₀ + L * e) / e ^ 3 := by
    rw [W.velu2Y_eq_div x₀ y₀ _ hx, hsub]
  rw [hX, hY]
  simp only [veluGx, velu2XNum, velu2YNum, Affine.addX, Affine.addY, Affine.negAddY,
    Affine.negY, veluQuotient2_a₁, veluQuotient2_a₂, veluQuotient2_a₄] at key ⊢
  field_simp
  linear_combination key

p2m_export "WeierstrassCurve" "veluGx_velu2"

private theorem _root_.WeierstrassCurve.veluAsym_velu2 {x₀ y₀ x y : F} (hP : W.toAffine.Equation x y)
    (hT : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) (hx : x ≠ x₀) :
    (W.velu2X x₀ y₀ x * (W.veluQuotient2 x₀ y₀).veluGx (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y)
        - W.velu2Y x₀ y₀ x y
          * (W.veluQuotient2 x₀ y₀).veluGy (W.velu2X x₀ y₀ x) (W.velu2Y x₀ y₀ x y))
      = (x * W.veluGx x y - y * W.veluGy x y)
        + (W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y y₀)
            * W.veluGx (W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y y₀))
                (W.toAffine.addY x x₀ y (W.toAffine.slope x x₀ y y₀))
          - W.toAffine.addY x x₀ y (W.toAffine.slope x x₀ y y₀)
            * W.veluGy (W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y y₀))
                (W.toAffine.addY x x₀ y (W.toAffine.slope x x₀ y y₀))) := by
  have hx' := hx
  obtain ⟨e, L, he, rfl, rfl, hL⟩ := W.chord_param (y₀ := y₀) (y := y) hx
  rw [W.veluGx_velu2 hP hT hgy hx, hL]
  have keyW := W.veluAsym_velu2_chord_reduced hP hT hgy
  have hsub : x₀ + e - x₀ = e := by ring
  have hX : W.velu2X x₀ y₀ (x₀ + e) = W.velu2XNum x₀ y₀ (x₀ + e) / e ^ 2 := by
    rw [W.velu2X_eq_div x₀ y₀ hx, hsub]
  have hY : W.velu2Y x₀ y₀ (x₀ + e) (y₀ + L * e)
      = W.velu2YNum x₀ y₀ (x₀ + e) (y₀ + L * e) / e ^ 3 := by
    rw [W.velu2Y_eq_div x₀ y₀ _ hx, hsub]
  have hGY : (W.veluQuotient2 x₀ y₀).veluGy (W.velu2X x₀ y₀ (x₀ + e))
        (W.velu2Y x₀ y₀ (x₀ + e) (y₀ + L * e))
      = -(2 * W.velu2YNum x₀ y₀ (x₀ + e) (y₀ + L * e)
          + W.a₁ * W.velu2XNum x₀ y₀ (x₀ + e) * e + W.a₃ * e ^ 3) / e ^ 3 := by
    rw [hX, hY]
    simp only [veluGy, veluQuotient2_a₁, veluQuotient2_a₃]
    field_simp
  rw [hGY, hX, hY]
  set XN := W.velu2XNum x₀ y₀ (x₀ + e) with hXN
  set YN := W.velu2YNum x₀ y₀ (x₀ + e) (y₀ + L * e) with hYN
  set S' := W.veluGx (x₀ + e) (y₀ + L * e)
    + W.veluGx (W.toAffine.addX (x₀ + e) x₀ L) (W.toAffine.addY (x₀ + e) x₀ (y₀ + L * e) L) with hS'
  set G := 2 * YN + W.a₁ * XN * e + W.a₃ * e ^ 3 with hG
  have hre : XN / e ^ 2 * S' - YN / e ^ 3 * (-G / e ^ 3) = (XN * e ^ 4 * S' + YN * G) / e ^ 6 := by
    field_simp
    ring
  rw [hre, div_eq_iff (pow_ne_zero 6 he)]
  linear_combination keyW

p2m_export "WeierstrassCurve" "veluAsym_velu2"

private theorem oddOrderSummingSet_eq_image_range (Q : W.toAffine.Point) (n : ℕ) :
    W.oddOrderSummingSet Q n = (Finset.range n).image fun i => ((i + 1) • Q).coordsOrZero := by
  ext P
  simp only [mem_oddOrderSummingSet, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, hk1, hk2, rfl⟩
    exact ⟨k - 1, by omega, by rw [Nat.sub_add_cancel hk1]⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i + 1, by omega, by omega, rfl⟩

private theorem _root_.WeierstrassCurve.sum_oddOrderSummingSet_eq_sum_range (Q : W.toAffine.Point) {n : ℕ}
    (hn : n < addOrderOf Q) (g : F × F → F) :
    ∑ P ∈ W.oddOrderSummingSet Q n, g P = ∑ i ∈ Finset.range n, g (((i + 1) • Q).coordsOrZero) := by
  rw [oddOrderSummingSet_eq_image_range, Finset.sum_image]
  intro i hi j hj h
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  have hne : ∀ k, k < n → (k + 1) • Q ≠ 0 := fun k hk =>
    nsmul_ne_zero_of_lt_addOrderOf (by omega) (by omega)
  have hpt : (i + 1) • Q = (j + 1) • Q := eq_of_coordsOrZero_eq (hne i hi) (hne j hj) h
  have := nsmul_injOn_Iio_addOrderOf (x := Q) (by simp only [Set.mem_Iio]; omega)
    (by simp only [Set.mem_Iio]; omega) hpt
  omega

p2m_export "WeierstrassCurve" "sum_oddOrderSummingSet_eq_sum_range"
omit [DecidableEq F] in

private theorem _root_.WeierstrassCurve.some_eq_of_X_eq_of_veluGy_eq_zero {x₀ y₀ y : F} (h₀ : W.toAffine.Nonsingular x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (h : W.toAffine.Nonsingular x₀ y) :
    (Affine.Point.some x₀ y h : W.toAffine.Point) = Affine.Point.some x₀ y₀ h₀ := by
  have hneg : W.toAffine.negY x₀ y₀ = y₀ := by
    simp only [veluGy] at hgy
    simp only [Affine.negY]
    linear_combination hgy
  have hy : y = y₀ := by
    rcases Affine.Y_eq_of_X_eq h.1 h₀.1 rfl with hy | hy
    · exact hy
    · rw [hy, hneg]
  subst hy
  rfl

p2m_export "WeierstrassCurve" "some_eq_of_X_eq_of_veluGy_eq_zero"

private theorem _root_.WeierstrassCurve.fullKernelQuotient_comp_veluQuotient2 [W.IsElliptic] (h2 : (2 : F) ≠ 0)
    {m : ℕ} (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * (m + 1))
    {x₀ y₀ : F} {h₀ : W.toAffine.Nonsingular x₀ y₀}
    (hT : (m + 1) • Q = Affine.Point.some x₀ y₀ h₀) (hgy : W.veluGy x₀ y₀ = 0)
    (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0) :
    W.fullKernelQuotient Q (2 * (m + 1))
      = (W.veluQuotient2 x₀ y₀).fullKernelQuotient (veluPointMap2 h2 h₀.1 hgy hΔ Q) (m + 1) := by
  obtain ⟨φ, hφ⟩ := W.exists_addMonoidHom_coe_eq_veluPointMap2 h2 h₀.1 hgy hΔ

  have hne : ∀ k, 0 < k → k < 2 * (m + 1) → k • Q ≠ 0 := fun k hk1 hk2 =>
    nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; exact hk2)
  have hcoords : ∀ i, i < m → ∃ (x y : F) (h : W.toAffine.Nonsingular x y),
      (i + 1) • Q = Affine.Point.some x y h ∧ x ≠ x₀ := by
    intro i hi
    rcases hP : (i + 1) • Q with _ | ⟨x, y, h⟩
    · exact absurd (hP.trans Affine.Point.zero_def.symm) (hne (i + 1) (by omega) (by omega))
    · refine ⟨x, y, h, rfl, fun hx => ?_⟩
      subst hx
      have hPT : (i + 1) • Q = (m + 1) • Q := by
        rw [hP, hT, W.some_eq_of_X_eq_of_veluGy_eq_zero h₀ hgy h]
      have := nsmul_injOn_Iio_addOrderOf (x := Q) (by simp only [Set.mem_Iio]; omega)
        (by simp only [Set.mem_Iio]; omega) hPT
      omega

  have hpair : ∀ i, i < m → ∀ g : F × F → F, ∀ g₁ : F × F → F,
      (∀ (x y : F), W.toAffine.Equation x y → x ≠ x₀ →
        g₁ (W.velu2X x₀ y₀ x, W.velu2Y x₀ y₀ x y)
          = g (x, y) + g (W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y y₀),
              W.toAffine.addY x x₀ y (W.toAffine.slope x x₀ y y₀))) →
      g (((i + 1) • Q).coordsOrZero) + g (((m + (i + 1) + 1) • Q).coordsOrZero)
        = g₁ (((i + 1) • φ Q).coordsOrZero) := by
    intro i hi g g₁ hg
    obtain ⟨x, y, h, hP, hx⟩ := hcoords i hi
    have hsum : (m + (i + 1) + 1) • Q = (i + 1) • Q + (m + 1) • Q := by
      rw [← add_nsmul]; congr 1; omega
    rw [← map_nsmul φ (i + 1) Q, hφ, hsum, hP, hT, Affine.Point.add_of_X_ne hx,
      veluPointMap2_some_of_ne h2 h₀.1 hgy hΔ h hx]
    simp only [Affine.Point.coordsOrZero_some]
    exact (hg x y h.1 hx).symm

  have hsplit : ∀ g : F × F → F,
      ∑ P ∈ W.oddOrderSummingSet Q (2 * (m + 1) - 1), g P
        = g (x₀, y₀) + ∑ i ∈ Finset.range m,
            (g (((i + 1) • Q).coordsOrZero) + g (((m + (i + 1) + 1) • Q).coordsOrZero)) := by
    intro g
    rw [W.sum_oddOrderSummingSet_eq_sum_range Q (by rw [hQ]; omega) g,
      show 2 * (m + 1) - 1 = m + (m + 1) by omega, Finset.sum_range_add, Finset.sum_range_succ',
      Finset.sum_add_distrib]
    have hTc : ((m + 0 + 1) • Q).coordsOrZero = (x₀, y₀) := by
      rw [show m + 0 + 1 = m + 1 by omega, hT, Affine.Point.coordsOrZero_some]
    rw [hTc]
    ring

  have hφQ_order : m < addOrderOf (φ Q) := by

    by_contra hlt
    push Not at hlt
    have hfin : IsOfFinAddOrder (φ Q) :=
      φ.isOfFinAddOrder (addOrderOf_pos_iff.mp (by rw [hQ]; omega))
    have hk : 0 < addOrderOf (φ Q) := addOrderOf_pos_iff.mpr hfin
    obtain ⟨x, y, h, hP, hx⟩ := hcoords (addOrderOf (φ Q) - 1) (by omega)
    have h0 : (addOrderOf (φ Q) - 1 + 1) • φ Q = 0 := by
      rw [Nat.sub_add_cancel hk, addOrderOf_nsmul_eq_zero]
    rw [← map_nsmul φ (addOrderOf (φ Q) - 1 + 1) Q, hP, hφ,
      veluPointMap2_some_of_ne h2 h₀.1 hgy hΔ h hx] at h0
    exact Affine.Point.some_ne_zero _ h0
  have hdown : ∀ g₁ : F × F → F,
      ∑ P ∈ (W.veluQuotient2 x₀ y₀).oddOrderSummingSet (veluPointMap2 h2 h₀.1 hgy hΔ Q) (m + 1 - 1),
          g₁ P
        = ∑ i ∈ Finset.range m, g₁ (((i + 1) • φ Q).coordsOrZero) := by
    intro g₁
    rw [show m + 1 - 1 = m by omega, ← hφ,
      (W.veluQuotient2 x₀ y₀).sum_oddOrderSummingSet_eq_sum_range (φ Q) hφQ_order g₁]

  have ht := hsplit (fun P => W.veluGx P.1 P.2)
  have hw := hsplit (fun P => P.1 * W.veluGx P.1 P.2 - P.2 * W.veluGy P.1 P.2)
  have ht₁ := hdown (fun P => (W.veluQuotient2 x₀ y₀).veluGx P.1 P.2)
  have hw₁ := hdown (fun P => P.1 * (W.veluQuotient2 x₀ y₀).veluGx P.1 P.2
      - P.2 * (W.veluQuotient2 x₀ y₀).veluGy P.1 P.2)
  beta_reduce at ht hw ht₁ hw₁
  have hsumt : ∑ i ∈ Finset.range m, (W.veluGx ((i + 1) • Q).coordsOrZero.1 ((i + 1) • Q).coordsOrZero.2
        + W.veluGx ((m + (i + 1) + 1) • Q).coordsOrZero.1 ((m + (i + 1) + 1) • Q).coordsOrZero.2)
      = ∑ i ∈ Finset.range m,
          (W.veluQuotient2 x₀ y₀).veluGx ((i + 1) • φ Q).coordsOrZero.1
            ((i + 1) • φ Q).coordsOrZero.2 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    exact hpair i (Finset.mem_range.mp hi) (fun P => W.veluGx P.1 P.2)
      (fun P => (W.veluQuotient2 x₀ y₀).veluGx P.1 P.2)
      (fun x y hP hx => W.veluGx_velu2 hP h₀.1 hgy hx)
  have hsumw : ∑ i ∈ Finset.range m,
        ((((i + 1) • Q).coordsOrZero.1 * W.veluGx ((i + 1) • Q).coordsOrZero.1 ((i + 1) • Q).coordsOrZero.2
            - ((i + 1) • Q).coordsOrZero.2
              * W.veluGy ((i + 1) • Q).coordsOrZero.1 ((i + 1) • Q).coordsOrZero.2)
          + (((m + (i + 1) + 1) • Q).coordsOrZero.1
              * W.veluGx ((m + (i + 1) + 1) • Q).coordsOrZero.1 ((m + (i + 1) + 1) • Q).coordsOrZero.2
            - ((m + (i + 1) + 1) • Q).coordsOrZero.2
              * W.veluGy ((m + (i + 1) + 1) • Q).coordsOrZero.1
                  ((m + (i + 1) + 1) • Q).coordsOrZero.2))
      = ∑ i ∈ Finset.range m,
          (((i + 1) • φ Q).coordsOrZero.1
              * (W.veluQuotient2 x₀ y₀).veluGx ((i + 1) • φ Q).coordsOrZero.1
                  ((i + 1) • φ Q).coordsOrZero.2
            - ((i + 1) • φ Q).coordsOrZero.2
              * (W.veluQuotient2 x₀ y₀).veluGy ((i + 1) • φ Q).coordsOrZero.1
                  ((i + 1) • φ Q).coordsOrZero.2) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    exact hpair i (Finset.mem_range.mp hi)
      (fun P => P.1 * W.veluGx P.1 P.2 - P.2 * W.veluGy P.1 P.2)
      (fun P => P.1 * (W.veluQuotient2 x₀ y₀).veluGx P.1 P.2
        - P.2 * (W.veluQuotient2 x₀ y₀).veluGy P.1 P.2)
      (fun x y hP hx => W.veluAsym_velu2 hP h₀.1 hgy hx)
  have hgyT : W.veluGy x₀ y₀ = 0 := hgy
  ext
  · rfl
  · rfl
  · rfl
  · simp only [fullKernelQuotient, veluQuotientOfSums_a₄, veluQuotient2_a₄]
    rw [ht, ht₁, hsumt]
    dsimp only
    ring
  · simp only [fullKernelQuotient, veluQuotientOfSums_a₆, veluQuotient2_a₆, veluQuotient2_b₂]
    rw [hw, hw₁, hsumw, ht, ht₁, hsumt, hgyT]
    dsimp only
    ring

p2m_export "WeierstrassCurve" "fullKernelQuotient_comp_veluQuotient2"
end Field

end WeierstrassCurve

theorem solution
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    (h2 : (2 : F) ≠ 0) {m : ℕ} (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * (m + 1))
    {x₀ y₀ : F} {h₀ : W.toAffine.Nonsingular x₀ y₀}
    (hT : (m + 1) • Q = Affine.Point.some x₀ y₀ h₀) (hgy : W.veluGy x₀ y₀ = 0)
    (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0) :
    W.fullKernelQuotient Q (2 * (m + 1)) =
      (W.veluQuotient2 x₀ y₀).fullKernelQuotient (veluPointMap2 h2 h₀.1 hgy hΔ Q) (m + 1) :=
  W.fullKernelQuotient_comp_veluQuotient2 h2 Q hQ hT hgy hΔ

end S_WeierstrassCurve_fullKernelQuotient_eq_fullKernelQuotient_veluQuotient2
end P2MW
export P2MW.S_WeierstrassCurve_fullKernelQuotient_eq_fullKernelQuotient_veluQuotient2 (solution)
