-- Prove2me | solution 1 for WeierstrassCurve.veluGx_ne_zero_of_two_torsion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/02f2372d-bbff-5e6f-9967-f9ba04f8a26a

import Mathlib
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import Theorems.Thm_WeierstrassCurve_Delta_eq_veluGx_sq_mul_velu2QuadDisc
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_veluGx_ne_zero_of_two_torsion

open WeierstrassCurve WeierstrassCurve.Affine in
theorem solution {R : Type*} [CommRing R] {W : WeierstrassCurve R} {x₀ y₀ : R} (hΔ : W.Δ ≠ 0)
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) :
    W.veluGx x₀ y₀ ≠ 0 := by
  intro h
  exact hΔ (by rw [Delta_eq_veluGx_sq_mul_velu2QuadDisc hQ hgy, h]; ring)

end S_WeierstrassCurve_veluGx_ne_zero_of_two_torsion
end P2MW
export P2MW.S_WeierstrassCurve_veluGx_ne_zero_of_two_torsion (solution)
