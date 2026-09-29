-- Prove2me | solution 1 for WeierstrassCurve.velu2_tangent_addX_cleared_identity
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/8a341e90-cff7-5e41-ae8f-f83bec1ec20f

import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_velu2_tangent_addX_cleared_identity

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

private theorem velu2TangentAddX_assemble {R : Type*} [CommRing R] {A M C D t u : R}
    (h1 : A * u = t ^ 2) (h2 : C = D ^ 2) (h3 : M = t ^ 2 * u + 2 * D ^ 2) :
    A * M * u * C = (t * D) ^ 2 * (t ^ 2 * u + 2 * C) := by
  linear_combination (M * C) * h1 + (t ^ 4 * u) * h2 + (t ^ 2 * C) * h3

theorem solution
    {R : Type*} [CommRing R] {W : WeierstrassCurve R} {x₀ y₀ x y : R}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hord : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) :
    (W.a₁ ^ 2 * (x - x₀)
            + 4 * (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y₀))
          * (((x - x₀) ^ 2 - W.veluGx x₀ y₀)
                * (6 * x ^ 2 + (4 * W.a₂ + W.a₁ ^ 2) * x + 2 * W.a₄ + W.a₁ * W.a₃)
              + W.veluGx x₀ y₀
                * (W.a₁ ^ 2 * (x - x₀)
                    + 4 * (x ^ 2 + x * x₀ + x₀ ^ 2 + W.a₂ * (x + x₀) + W.a₄ - W.a₁ * y₀)))
          * (x - x₀)
          * ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) ^ 2
              + W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * (2 * y + W.a₁ * x + W.a₃)
              - (W.a₂ + 2 * x + x₀) * (2 * y + W.a₁ * x + W.a₃) ^ 2)
      = ((2 * y + W.a₁ * x + W.a₃) * ((x - x₀) ^ 2 - W.veluGx x₀ y₀)) ^ 2
        * ((2 * y + W.a₁ * x + W.a₃) ^ 2 * (x - x₀)
            + 2
              * ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) ^ 2
                  + W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)
                    * (2 * y + W.a₁ * x + W.a₃)
                  - (W.a₂ + 2 * x + x₀) * (2 * y + W.a₁ * x + W.a₃) ^ 2)) := by
  rw [Affine.equation_iff] at hP hQ
  refine velu2TangentAddX_assemble ?_ ?_ ?_
  ·
    linear_combination (-4) * hP + 4 * hQ
      + (-2 * W.a₁ * x + W.a₁ * x₀ - W.a₃ - 2 * y₀) * hord
  ·
    simp only [veluGx]
    linear_combination (-W.a₁ ^ 2 - 4 * W.a₂ - 8 * x - 4 * x₀) * hP
      + (W.a₁ ^ 2 + 4 * W.a₂ + 8 * x + 4 * x₀) * hQ
      + (-W.a₁ ^ 2 * y₀ + W.a₁ * W.a₂ * x₀ + W.a₁ * W.a₄ - W.a₁ * x ^ 2 + W.a₁ * x₀ ^ 2
          - W.a₂ * W.a₃ - 2 * W.a₂ * y₀ - 2 * W.a₃ * x - W.a₃ * x₀ - 4 * x * y₀
          - 2 * x₀ * y₀) * hord
  ·
    simp only [veluGx]
    linear_combination (-4 * x + 4 * x₀) * hP + (4 * x - 4 * x₀) * hQ
      + (W.a₁ ^ 2 * y₀ - 2 * W.a₁ * W.a₂ * x₀ - W.a₁ * W.a₄ - W.a₁ * x ^ 2 + W.a₁ * x * x₀
          - 3 * W.a₁ * x₀ ^ 2 - W.a₃ * x + W.a₃ * x₀ - 2 * x * y₀ + 2 * x₀ * y₀) * hord

end S_WeierstrassCurve_velu2_tangent_addX_cleared_identity
end P2MW
export P2MW.S_WeierstrassCurve_velu2_tangent_addX_cleared_identity (solution)
