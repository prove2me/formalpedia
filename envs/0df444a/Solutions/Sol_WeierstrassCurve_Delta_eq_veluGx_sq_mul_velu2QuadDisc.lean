-- Prove2me | solution 1 for WeierstrassCurve.Delta_eq_veluGx_sq_mul_velu2QuadDisc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/b4ea2791-344a-50f7-9efe-5c9df5cdc09f

import Mathlib
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Delta_eq_veluGx_sq_mul_velu2QuadDisc

open WeierstrassCurve WeierstrassCurve.Affine in
theorem solution {R : Type*} [CommRing R] {W : WeierstrassCurve R} {x₀ y₀ : R}
    (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0) :
    W.Δ = W.veluGx x₀ y₀ ^ 2 * W.velu2QuadDisc x₀ := by
  rw [Affine.equation_iff] at hQ
  simp only [veluGy] at hgy
  simp only [Δ, b₂, b₄, b₆, b₈, veluGx, velu2QuadDisc]
  linear_combination
    (W.a₁^6 + 12*W.a₁^4*W.a₂ - 36*W.a₁^3*W.a₃ + 48*W.a₁^2*W.a₂^2 - 72*W.a₁^2*W.a₄ - 144*W.a₁*W.a₂*W.a₃ + 432*W.a₁*x₀*y₀ + 64*W.a₂^3 - 288*W.a₂*W.a₄ - 432*W.a₂*x₀^2 + 216*W.a₃^2 + 432*W.a₃*y₀ - 432*W.a₄*x₀ + 432*W.a₆ - 432*x₀^3 + 432*y₀^2) * hQ
    + (W.a₁^6*y₀ - W.a₁^5*W.a₂*x₀ - W.a₁^5*W.a₄ - W.a₁^5*x₀^2 + W.a₁^4*W.a₂*W.a₃ + 10*W.a₁^4*W.a₂*y₀ + W.a₁^4*W.a₃*x₀ - 4*W.a₁^4*x₀*y₀ - 8*W.a₁^3*W.a₂^2*x₀ - 8*W.a₁^3*W.a₂*W.a₄ - W.a₁^3*W.a₃^2 - 34*W.a₁^3*W.a₃*y₀ + 6*W.a₁^3*W.a₄*x₀ + 9*W.a₁^3*x₀^3 + 8*W.a₁^2*W.a₂^2*W.a₃ + 32*W.a₁^2*W.a₂^2*y₀ + 36*W.a₁^2*W.a₂*W.a₃*x₀ - 16*W.a₁^2*W.a₂*x₀*y₀ + 30*W.a₁^2*W.a₃*W.a₄ + 27*W.a₁^2*W.a₃*x₀^2 - 68*W.a₁^2*W.a₄*y₀ + 30*W.a₁^2*x₀^2*y₀ - 16*W.a₁*W.a₂^3*x₀ - 16*W.a₁*W.a₂^2*W.a₄ + 16*W.a₁*W.a₂^2*x₀^2 - 36*W.a₁*W.a₂*W.a₃^2 - 72*W.a₁*W.a₂*W.a₃*y₀ + 88*W.a₁*W.a₂*W.a₄*x₀ - 24*W.a₁*W.a₂*x₀^3 - 27*W.a₁*W.a₃^2*x₀ + 108*W.a₁*W.a₃*x₀*y₀ + 64*W.a₁*W.a₄^2 + 24*W.a₁*W.a₄*x₀^2 - 72*W.a₁*x₀^4 + 324*W.a₁*x₀*y₀^2 + 16*W.a₂^3*W.a₃ + 32*W.a₂^3*y₀ - 72*W.a₂*W.a₃*W.a₄ - 216*W.a₂*W.a₃*x₀^2 - 144*W.a₂*W.a₄*y₀ - 432*W.a₂*x₀^2*y₀ + 27*W.a₃^3 + 162*W.a₃^2*y₀ - 216*W.a₃*W.a₄*x₀ - 216*W.a₃*x₀^3 + 324*W.a₃*y₀^2 - 432*W.a₄*x₀*y₀ - 432*x₀^3*y₀ + 216*y₀^3) * hgy

end S_WeierstrassCurve_Delta_eq_veluGx_sq_mul_velu2QuadDisc
end P2MW
export P2MW.S_WeierstrassCurve_Delta_eq_veluGx_sq_mul_velu2QuadDisc (solution)
