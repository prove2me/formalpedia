-- Prove2me | solution 1 for WeierstrassCurve.reducePoint_some_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/20a3bb48-5876-5b7f-bbf0-77fa0ac91b03

import Theorems.Thm_WeierstrassCurve_valuation_le_one_of_equation
import Theorems.Thm_WeierstrassCurve_reducePoint_some
import Definitions.Def_EllipticCurve_PointReduction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_reducePoint_some_eq_zero_iff

set_option autoImplicit false

open WeierstrassCurve IsDiscreteValuationRing IsLocalRing IsDedekindDomain.HeightOneSpectrum

theorem solution
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) [W.HasGoodReduction R] {x y : K} (h : W.toAffine.Nonsingular x y) :
    WeierstrassCurve.reducePoint_alt R W (.some x y h) = .zero ↔
      ¬ IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) x ≤ 1 := by
  classical
  constructor
  · intro h0 hx
    have hy : valuation K (IsDiscreteValuationRing.maximalIdeal R) y ≤ 1 :=
      WeierstrassCurve.valuation_le_one_of_equation R W h.left hx
    obtain ⟨h', hsome⟩ := WeierstrassCurve.reducePoint_some R W h hx hy
    rw [hsome] at h0
    exact Affine.Point.some_ne_zero h' (h0.trans (Affine.Point.zero_def).symm)
  · intro hx
    show (if _ : valuation K (IsDiscreteValuationRing.maximalIdeal R) x ≤ 1 ∧
        valuation K (IsDiscreteValuationRing.maximalIdeal R) y ≤ 1
        then _ else Affine.Point.zero) = Affine.Point.zero
    rw [dif_neg (fun hc => hx hc.1)]

end S_WeierstrassCurve_reducePoint_some_eq_zero_iff
end P2MW
export P2MW.S_WeierstrassCurve_reducePoint_some_eq_zero_iff (solution)
