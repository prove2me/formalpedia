-- Prove2me | solution 1 for Problem97.inner_chord_eq_two_mul_inner_midpoint
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:05:51.019342+00:00
-- url     : https://prove2.me/submissions/697e9e2a-aad5-4735-b870-e78025682598

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.Cap.ArcInscribedAngle:1249:4969. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Analysis.InnerProductSpace.Basic

section Erdos9796CountingFragment_Erdos9796Proof_P97_Cap_ArcInscribedAngle

open Problem97

/- Fragment from Erdos9796Proof.P97.Cap.ArcInscribedAngle; source SHA-256 229631a65f8abd10a13cc09e09bfa34327c4b03427c96d3053e9f4b1fef392da -/


/-!
# On-sphere chord-arc inner-product nonnegativity

For three points `c, x, y` on a 2D Euclidean sphere of center `O` and radius
`r`, if `c` lies on the closed half-plane of the chord `xy` containing `O`,
then the inscribed angle at `c` subtending `xy` is at most `π/2`; equivalently
`⟪x - c, y - c⟫_ℝ ≥ 0`.

This is the inscribed-angle / Thales-style step of the MEC arc-angle chain:
once `c` is pinned to the major-arc side (the half-plane of `xy` containing
the center `O`), the inner-product nonnegativity feeds the algebraic step
`Problem97.dist_midpoint_ge_half_of_inner_nn` to close the on-sphere version
of the cap-arc midpoint inequality.

The proof reduces the inscribed-angle theorem to a clean algebraic identity:
under the sphere hypothesis `‖x - O‖ = ‖y - O‖ = ‖c - O‖`, one has

  `⟪x - c, y - c⟫_ℝ = 2 · ⟪m - O, m - c⟫_ℝ`,

where `m := midpoint ℝ x y`.  The right-hand side is `≥ 0` exactly when `c`
lies in the closed half-plane of the chord `xy` containing the center — the
chord-side characterization of the major arc.
-/

open scoped EuclideanGeometry InnerProductSpace




theorem solution
    {O c x y : ℝ²}
    (hxO : ‖x - O‖ = ‖c - O‖) (hyO : ‖y - O‖ = ‖c - O‖) :
    ⟪x - c, y - c⟫_ℝ =
      2 * ⟪midpoint ℝ x y - O, midpoint ℝ x y - c⟫_ℝ := by
  -- Square the sphere conditions to inner-product identities.
  have hXsq : ⟪x - O, x - O⟫_ℝ = ⟪c - O, c - O⟫_ℝ := by
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hxO]
  have hYsq : ⟪y - O, y - O⟫_ℝ = ⟪c - O, c - O⟫_ℝ := by
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hyO]
  -- Rewrite `midpoint ℝ x y` as `(1/2) • (x + y)`.
  have hmid : midpoint ℝ x y = (1 / 2 : ℝ) • (x + y) := by
    rw [midpoint_eq_smul_add]; congr 1; norm_num
  rw [hmid]
  -- Expand the LHS:
  --   ⟪x - c, y - c⟫ = ⟪x,y⟫ - ⟪x,c⟫ - ⟪y,c⟫ + ⟪c,c⟫.
  have hLHS : ⟪x - c, y - c⟫_ℝ
                = ⟪x, y⟫_ℝ - ⟪x, c⟫_ℝ - ⟪y, c⟫_ℝ + ⟪c, c⟫_ℝ := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm c y]
    ring
  -- Expand the RHS:
  --   ⟪(1/2)(x+y) - O, (1/2)(x+y) - c⟫
  --     = (1/4)⟪x+y, x+y⟫ - (1/2)⟪x+y, c⟫ - (1/2)⟪O, x+y⟫ + ⟪O, c⟫
  -- Fully bilinearise into a polynomial in the inner products of `x, y, c, O`.
  have hRHS : ⟪(1 / 2 : ℝ) • (x + y) - O, (1 / 2 : ℝ) • (x + y) - c⟫_ℝ
                = (1 / 4 : ℝ) *
                    (⟪x, x⟫_ℝ + ⟪x, y⟫_ℝ + ⟪y, x⟫_ℝ + ⟪y, y⟫_ℝ)
                  - (1 / 2 : ℝ) * (⟪x, c⟫_ℝ + ⟪y, c⟫_ℝ)
                  - (1 / 2 : ℝ) * (⟪O, x⟫_ℝ + ⟪O, y⟫_ℝ)
                  + ⟪O, c⟫_ℝ := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right,
        real_inner_smul_left, real_inner_smul_left, real_inner_smul_right,
        real_inner_smul_right, inner_add_left, inner_add_left,
        inner_add_right, inner_add_right, inner_add_right]
    ring
  rw [hLHS, hRHS]
  -- Polarization expansion of the sphere conditions.
  have hXexp : ⟪x - O, x - O⟫_ℝ
                  = ⟪x, x⟫_ℝ - ⟪x, O⟫_ℝ - ⟪O, x⟫_ℝ + ⟪O, O⟫_ℝ := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]; ring
  have hYexp : ⟪y - O, y - O⟫_ℝ
                  = ⟪y, y⟫_ℝ - ⟪y, O⟫_ℝ - ⟪O, y⟫_ℝ + ⟪O, O⟫_ℝ := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]; ring
  have hCexp : ⟪c - O, c - O⟫_ℝ
                  = ⟪c, c⟫_ℝ - ⟪c, O⟫_ℝ - ⟪O, c⟫_ℝ + ⟪O, O⟫_ℝ := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]; ring
  rw [hXexp, hCexp] at hXsq
  rw [hYexp, hCexp] at hYsq
  -- Need to symmetrize ⟪y, x⟫ → ⟪x, y⟫ and ⟪_, O⟫ ↔ ⟪O, _⟫ to allow linarith.
  -- `real_inner_comm a b : ⟪b, a⟫_ℝ = ⟪a, b⟫_ℝ`.
  have hyx : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := real_inner_comm x y
  have hxO_sym : ⟪x, O⟫_ℝ = ⟪O, x⟫_ℝ := real_inner_comm O x
  have hyO_sym : ⟪y, O⟫_ℝ = ⟪O, y⟫_ℝ := real_inner_comm O y
  have hcO_sym : ⟪c, O⟫_ℝ = ⟪O, c⟫_ℝ := real_inner_comm O c
  rw [hxO_sym, hcO_sym] at hXsq
  rw [hyO_sym, hcO_sym] at hYsq
  linarith [hyx]

end Erdos9796CountingFragment_Erdos9796Proof_P97_Cap_ArcInscribedAngle
