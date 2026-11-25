-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.abs_le_qf_of_min
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:48:14.419859+00:00
-- url     : https://prove2.me/submissions/df627e68-dc70-4580-a68a-4ef4799bfd06

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_QuadTie
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_qf_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_qf_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
variable {𝕜 W : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup W] [Module 𝕜 W]
variable {B : LinearMap.BilinForm 𝕜 W}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (hB : ∀ x y, B x y = B y x) {x μ : W} (h₁ : qf B x ≤ qf B (x + μ))
    (h₂ : qf B x ≤ qf B (x - μ)) : |B x μ| ≤ qf B μ := by
  rw [qf_add hB] at h₁
  rw [sub_eq_add_neg, qf_add hB, map_neg, show -μ = (-1 : 𝕜) • μ by simp, qf_smul] at h₂
  rw [abs_le]; constructor <;> nlinarith
end ReciprocityTheory.ChartRestriction.G.DVR
