-- Prove2me | solution 1 for WeierstrassCurve.mem_valuationSubring_of_equation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/3fc98000-d5b6-5844-961b-a373aa895a06

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_mem_valuationSubring_of_equation

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace M4cP2
namespace G4

theorem baseChange_map_intCast_eq_map {K : Type*} [CommRing K] [Algebra ℚ K]
    (W : WeierstrassCurve ℤ) : (W.map (Int.castRingHom ℚ))⁄K = W.map (Int.castRingHom K) := by
  show (W.map (Int.castRingHom ℚ)).map (algebraMap ℚ K) = _
  rw [WeierstrassCurve.map_map]
  congr 1
  exact RingHom.ext_int _ _

theorem equation_baseChange_map_intCast_iff {K : Type*} [CommRing K] [Algebra ℚ K]
    (W : WeierstrassCurve ℤ) (x y : K) :
    ((W.map (Int.castRingHom ℚ))⁄K).toAffine.Equation x y ↔
      y ^ 2 + (W.a₁ : K) * x * y + (W.a₃ : K) * y
        = x ^ 3 + (W.a₂ : K) * x ^ 2 + (W.a₄ : K) * x + (W.a₆ : K) := by
  rw [baseChange_map_intCast_eq_map W, Affine.equation_iff]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, eq_intCast]

theorem mem_valuationSubring_of_equation {K : Type*} [Field K] [Algebra ℚ K]
    (W : WeierstrassCurve ℤ) (A : ValuationSubring K) {x y : K}
    (h : ((W.map (Int.castRingHom ℚ))⁄K).toAffine.Equation x y) (hx : x ∈ A) : y ∈ A := by
  have heqn := (equation_baseChange_map_intCast_iff W x y).mp h
  by_contra hy
  have hy1 : 1 < A.valuation y :=
    not_le.mp (fun hle => hy (A.mem_of_valuation_le_one y hle))
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy A.zero_mem
  have hyi : A.valuation y⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hy1
  set c : K := (W.a₁ : K) * x + (W.a₃ : K) with hc
  set d : K := x ^ 3 + (W.a₂ : K) * x ^ 2 + (W.a₄ : K) * x + (W.a₆ : K) with hd
  have hcA : c ∈ A := A.add_mem _ _ (A.mul_mem _ _ (intCast_mem A _) hx) (intCast_mem A _)
  have hdA : d ∈ A := by
    refine A.add_mem _ _ (A.add_mem _ _ (A.add_mem _ _ ?_ ?_) ?_) (intCast_mem A _)
    · exact A.pow_mem hx 3
    · exact A.mul_mem _ _ (intCast_mem A _) (A.pow_mem hx 2)
    · exact A.mul_mem _ _ (intCast_mem A _) hx
  have key : (1 : K) = d * y⁻¹ ^ 2 - c * y⁻¹ := by
    field_simp
    linear_combination heqn
  have hub : A.valuation (d * y⁻¹ ^ 2 - c * y⁻¹) < 1 := by
    refine lt_of_le_of_lt (A.valuation.map_sub _ _) (max_lt ?_ ?_)
    · rw [map_mul, map_pow]
      calc A.valuation d * A.valuation y⁻¹ ^ 2
          ≤ 1 * A.valuation y⁻¹ ^ 2 :=
            mul_le_mul' ((A.valuation_le_one_iff _).mpr hdA) le_rfl
        _ = A.valuation y⁻¹ * A.valuation y⁻¹ := by rw [one_mul, pow_two]
        _ ≤ 1 * A.valuation y⁻¹ := mul_le_mul' hyi.le le_rfl
        _ = A.valuation y⁻¹ := one_mul _
        _ < 1 := hyi
    · rw [map_mul]
      calc A.valuation c * A.valuation y⁻¹
          ≤ 1 * A.valuation y⁻¹ :=
            mul_le_mul' ((A.valuation_le_one_iff _).mpr hcA) le_rfl
        _ = A.valuation y⁻¹ := one_mul _
        _ < 1 := hyi
  rw [← key, _root_.map_one] at hub
  exact absurd hub (lt_irrefl 1)

end M4cP2.G4

theorem solution {K : Type*} [Field K] [Algebra ℚ K] (W : WeierstrassCurve ℤ) (A : ValuationSubring K) {x y : K} (h : ((W.map (Int.castRingHom ℚ))⁄K).toAffine.Equation x y) (hx : x ∈ A) : y ∈ A :=
  M4cP2.G4.mem_valuationSubring_of_equation W A h hx

end S_WeierstrassCurve_mem_valuationSubring_of_equation
end P2MW
export P2MW.S_WeierstrassCurve_mem_valuationSubring_of_equation (solution)
