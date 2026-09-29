-- Prove2me | solution 1 for WeierstrassCurve.veluQuotient2_Delta_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/18408a7d-4df7-513f-b981-4c3e770f7944

import Mathlib
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_veluQuotient2_Delta_eq

open WeierstrassCurve WeierstrassCurve.Affine in
theorem solution {R : Type*} [CommRing R] {W : WeierstrassCurve R} {x₀ y₀ : R}
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) :
    (W.veluQuotient2 x₀ y₀).Δ = W.veluGx x₀ y₀ * W.velu2QuadDisc x₀ ^ 2 := by
  rw [Affine.equation_iff] at hQ
  simp only [veluGy] at hgy
  simp only [Δ, b₂, b₄, b₆, b₈, veluQuotient2, veluGx, velu2QuadDisc]
  linear_combination
    (W.a₁^6 + 12*W.a₁^4*W.a₂ - 36*W.a₁^3*W.a₃ + 504*W.a₁^3*y₀ + 48*W.a₁^2*W.a₂^2 - 1008*W.a₁^2*W.a₂*x₀ - 576*W.a₁^2*W.a₄ - 1512*W.a₁^2*x₀^2 - 144*W.a₁*W.a₂*W.a₃ + 2016*W.a₁*W.a₂*y₀ + 6480*W.a₁*x₀*y₀ + 64*W.a₂^3 - 4032*W.a₂^2*x₀ - 2304*W.a₂*W.a₄ - 18576*W.a₂*x₀^2 + 216*W.a₃^2 + 432*W.a₃*y₀ - 6480*W.a₄*x₀ + 432*W.a₆ - 18576*x₀^3 + 432*y₀^2) * hQ
    + (24*W.a₁^6*y₀ - 47*W.a₁^5*W.a₂*x₀ - 24*W.a₁^5*W.a₄ - 70*W.a₁^5*x₀^2 + W.a₁^4*W.a₂*W.a₃ + 194*W.a₁^4*W.a₂*y₀ + W.a₁^4*W.a₃*x₀ - 110*W.a₁^4*x₀*y₀ - 376*W.a₁^3*W.a₂^2*x₀ - 192*W.a₁^3*W.a₂*W.a₄ - 340*W.a₁^3*W.a₂*x₀^2 - W.a₁^3*W.a₃^2 - 692*W.a₁^3*W.a₃*y₀ + 112*W.a₁^3*W.a₄*x₀ + 327*W.a₁^3*x₀^3 + 4252*W.a₁^3*y₀^2 + 8*W.a₁^2*W.a₂^2*W.a₃ + 400*W.a₁^2*W.a₂^2*y₀ + 1352*W.a₁^2*W.a₂*W.a₃*x₀ - 16944*W.a₁^2*W.a₂*x₀*y₀ + 688*W.a₁^2*W.a₃*W.a₄ + 2001*W.a₁^2*W.a₃*x₀^2 - 9888*W.a₁^2*W.a₄*y₀ - 24606*W.a₁^2*x₀^2*y₀ - 752*W.a₁*W.a₂^3*x₀ - 384*W.a₁*W.a₂^2*W.a₄ + 15760*W.a₁*W.a₂^2*x₀^2 - 36*W.a₁*W.a₂*W.a₃^2 + 432*W.a₁*W.a₂*W.a₃*y₀ + 19648*W.a₁*W.a₂*W.a₄*x₀ + 49008*W.a₁*W.a₂*x₀^3 + 1008*W.a₁*W.a₂*y₀^2 - 27*W.a₁*W.a₃^2*x₀ + 1620*W.a₁*W.a₃*x₀*y₀ + 5632*W.a₁*W.a₄^2 + 28608*W.a₁*W.a₄*x₀^2 + 35568*W.a₁*x₀^4 + 3348*W.a₁*x₀*y₀^2 + 16*W.a₂^3*W.a₃ + 32*W.a₂^3*y₀ - 1008*W.a₂^2*W.a₃*x₀ - 2016*W.a₂^2*x₀*y₀ - 576*W.a₂*W.a₃*W.a₄ - 4752*W.a₂*W.a₃*x₀^2 - 1152*W.a₂*W.a₄*y₀ - 9504*W.a₂*x₀^2*y₀ + 27*W.a₃^3 + 162*W.a₃^2*y₀ - 1728*W.a₃*W.a₄*x₀ - 4752*W.a₃*x₀^3 + 324*W.a₃*y₀^2 - 3456*W.a₄*x₀*y₀ - 9504*x₀^3*y₀ + 216*y₀^3) * hgy

end S_WeierstrassCurve_veluQuotient2_Delta_eq
end P2MW
export P2MW.S_WeierstrassCurve_veluQuotient2_Delta_eq (solution)
