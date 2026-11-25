-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.tie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:56:20.675861+00:00
-- url     : https://prove2.me/submissions/29128f2a-5ae8-43a8-a7cf-d5fa1c97fe71

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_QuadTie
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_qf_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_qf_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_abs_le_qf_of_min

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
theorem _root_.solution (hB : ∀ x y, B x y = B y x) {x μ : W} (h₁ : qf B x ≤ qf B (x + μ)) (h₂ : qf B x ≤ qf B (x - μ))
    (k : ℕ) : (k : 𝕜) * ((k : 𝕜) - 1) * qf B μ ≤ qf B (x + (k : 𝕜) • μ) - qf B x := by
  have h := abs_le.mp (abs_le_qf_of_min hB h₁ h₂)
  rw [qf_add hB, map_smul, qf_smul, smul_eq_mul]
  have hk : (0 : 𝕜) ≤ k := Nat.cast_nonneg k
  nlinarith [mul_le_mul_of_nonneg_left h.1 hk]
end ReciprocityTheory.ChartRestriction.G.DVR
