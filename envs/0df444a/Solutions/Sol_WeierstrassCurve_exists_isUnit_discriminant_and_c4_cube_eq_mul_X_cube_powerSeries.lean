-- Prove2me | solution 1 for WeierstrassCurve.exists_isUnit_discriminant_and_c4_cube_eq_mul_X_cube_powerSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/f225b1e5-63af-5806-b136-701c20c6fbdc

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_isUnit_discriminant_and_c4_cube_eq_mul_X_cube_powerSeries

set_option autoImplicit false

open PowerSeries

namespace P2MWs13
namespace GoodRedModels

variable (K : Type*) [Field K]

theorem isUnit_1728_sub_X_cube (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    IsUnit ((1728 : PowerSeries K) - PowerSeries.X ^ 3) := by
  refine PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr ?_)
  simp only [map_sub, map_ofNat, map_pow, PowerSeries.constantCoeff_X]
  have hfac : (1728 : K) = 2 ^ 6 * 3 ^ 3 := by norm_num
  norm_num
  rw [hfac]; exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)

theorem isUnit_1728_add_X_sq (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    IsUnit ((1728 : PowerSeries K) + PowerSeries.X ^ 2) := by
  refine PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr ?_)
  simp only [map_add, map_ofNat, map_pow, PowerSeries.constantCoeff_X]
  have hfac : (1728 : K) = 2 ^ 6 * 3 ^ 3 := by norm_num
  norm_num
  rw [hfac]; exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)

theorem isUnit_const (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (a b : ℕ) :
    IsUnit ((2 : PowerSeries K) ^ a * 3 ^ b) := by
  refine PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr ?_)
  simp only [map_mul, map_pow, map_ofNat]
  exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)

end P2MWs13.GoodRedModels

open P2MWs13.GoodRedModels in
theorem solution
    (K : Type*) [Field K] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    ∃ E : WeierstrassCurve (PowerSeries K), IsUnit E.Δ ∧ E.c₄ ^ 3 = E.Δ * PowerSeries.X ^ 3 := by
  set s : PowerSeries K := 1728 - PowerSeries.X ^ 3 with hs
  let E : WeierstrassCurve (PowerSeries K) := ⟨0, 0, 0, 3 * PowerSeries.X * s, 2 * s ^ 2⟩
  have hΔ : E.Δ = -(2 ^ 12 * 3 ^ 6) * s ^ 3 := by
    simp only [E, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    rw [hs]; ring
  have hc₄ : E.c₄ = -144 * PowerSeries.X * s := by
    simp only [E, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]; ring
  refine ⟨E, ?_, ?_⟩
  · rw [hΔ]
    exact ((isUnit_const K h2 h3 12 6).neg).mul ((isUnit_1728_sub_X_cube K h2 h3).pow 3)
  · rw [hc₄, hΔ]; ring

end S_WeierstrassCurve_exists_isUnit_discriminant_and_c4_cube_eq_mul_X_cube_powerSeries
end P2MW
export P2MW.S_WeierstrassCurve_exists_isUnit_discriminant_and_c4_cube_eq_mul_X_cube_powerSeries (solution)
