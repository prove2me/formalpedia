-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimA.perp_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:08:09.449439+00:00
-- url     : https://prove2.me/submissions/683b6c85-bc5c-44c0-80d2-3abd72b1ca44

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PerpSurj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.DimA
open Module
variable {H : Type*} [AddCommGroup H] (B : H →ₗ[ℤ] H →ₗ[ℤ] ℤ)
variable (halt : ∀ h, B h h = 0) (e f : H) (he : B e f = 1)
include halt he
namespace ReciprocityTheory.ChartRestriction.G.I2.DimA
theorem _root_.solution (hB : ∀ φ : H →ₗ[ℤ] ℤ, ∃ x, B x = φ) (φ : perp B e f →ₗ[ℤ] ℤ) :
    ∃ x : perp B e f, B.domRestrict₁₂ (perp B e f) (perp B e f) x = φ := by
  obtain ⟨x, hx⟩ := hB (φ.comp (proj B halt e f he))
  refine ⟨proj B halt e f he x, LinearMap.ext fun ⟨p, hp⟩ => ?_⟩
  have hp' := (mem_perp B).1 hp
  have hpe : B e p = 0 := by rw [alt_swap B halt, hp'.1, neg_zero]
  have hpf : B f p = 0 := by rw [alt_swap B halt, hp'.2, neg_zero]
  have hproj : proj B halt e f he p = ⟨p, hp⟩ := by
    ext; rw [proj_apply, hp'.1, hp'.2]; simp
  have hxp : B x p = φ (proj B halt e f he p) := by
    rw [hx]; rfl
  rw [LinearMap.domRestrict₁₂_apply, proj_apply]
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, hpe, hpf, smul_eq_mul, mul_zero, sub_zero, add_zero]
  rw [hxp, hproj]
end ReciprocityTheory.ChartRestriction.G.I2.DimA
