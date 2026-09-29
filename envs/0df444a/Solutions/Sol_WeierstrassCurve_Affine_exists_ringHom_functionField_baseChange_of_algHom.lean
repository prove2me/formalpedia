-- Prove2me | solution 1 for WeierstrassCurve.Affine.exists_ringHom_functionField_baseChange_of_algHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/bd14ad23-ab27-5a42-913b-7865fa4241b6

import Mathlib
import Definitions.Def_EllipticCurve_WeilPairingFun
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_exists_ringHom_functionField_baseChange_of_algHom

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain WithZero
open Polynomial
open scoped Polynomial.Bivariate

theorem solution
    {F K K' : Type*} [Field F] [Field K] [Field K'] [Algebra F K] [Algebra F K']
    (W : WeierstrassCurve F) (f : K →ₐ[F] K') :
    ∃ Φ : (W⁄K).FunctionField →+* (W⁄K').FunctionField,
      ∀ p : K[X][Y], Φ (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) p)) =
        algebraMap (W⁄K').CoordinateRing (W⁄K').FunctionField
          (CoordinateRing.mk (W⁄K') (p.map (mapRingHom (f : K →+* K')))) := by
  classical

  have hcurve : (W⁄K).map (f : K →+* K') = W⁄K' := W.map_baseChange f
  let φ₀ : (W⁄K).CoordinateRing →+* ((W⁄K).map (f : K →+* K')).CoordinateRing :=
    WeierstrassCurve.Affine.CoordinateRing.map (W⁄K) (f : K →+* K')
  have hspan : (Ideal.span {((W⁄K).map (f : K →+* K')).polynomial} : Ideal K'[X][Y]) = Ideal.span {(W⁄K').polynomial} := by
    rw [hcurve]
  let ι : ((W⁄K).map (f : K →+* K')).CoordinateRing ≃+* (W⁄K').CoordinateRing := Ideal.quotEquivOfEq hspan
  let φ : (W⁄K).CoordinateRing →+* (W⁄K').CoordinateRing := ι.toRingHom.comp φ₀
  have hφmk : ∀ p : K[X][Y], φ (CoordinateRing.mk (W⁄K) p) = CoordinateRing.mk (W⁄K') (p.map (mapRingHom (f : K →+* K'))) := by
    intro p
    simp only [φ, φ₀, ι, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      WeierstrassCurve.Affine.CoordinateRing.map_mk]
    exact Ideal.quotEquivOfEq_mk _ _
  have hφinj : Function.Injective φ :=
    ι.injective.comp (WeierstrassCurve.Affine.CoordinateRing.map_injective (W' := W⁄K) (f : K →+* K').injective)

  have hle : nonZeroDivisors (W⁄K).CoordinateRing ≤ (nonZeroDivisors (W⁄K').CoordinateRing).comap φ := by
    intro x hx
    rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
    rw [mem_nonZeroDivisors_iff_ne_zero] at hx
    exact fun h => hx (hφinj (by rw [h, map_zero]))
  refine ⟨IsLocalization.map (M := nonZeroDivisors (W⁄K).CoordinateRing) (W⁄K').FunctionField φ hle, fun p => ?_⟩
  rw [IsLocalization.map_eq, hφmk]

end S_WeierstrassCurve_Affine_exists_ringHom_functionField_baseChange_of_algHom
end P2MW
export P2MW.S_WeierstrassCurve_Affine_exists_ringHom_functionField_baseChange_of_algHom (solution)
