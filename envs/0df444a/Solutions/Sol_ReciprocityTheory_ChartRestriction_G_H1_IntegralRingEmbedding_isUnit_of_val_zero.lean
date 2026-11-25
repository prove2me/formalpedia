-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding.isUnit_of_val_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:01:54.121438+00:00
-- url     : https://prove2.me/submissions/a5c47b12-136f-484b-9f15-53794940f65b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_NakayamaChar
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_IntegralRingEmbedding
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_IntegralRingEmbedding_mem_intRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding
open Module
variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))
namespace ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding
theorem _root_.solution (x : intRing v) (hx : v (x : F) = 0) : IsUnit x := by
  have hx0 : (x : F) ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hx
    simp at hx
  have hinv : 0 ≤ v (x : F)⁻¹ := by
    have h1 : v (x : F) + v (x : F)⁻¹ = 0 := by
      rw [← AddValuation.map_mul, mul_inv_cancel₀ hx0, AddValuation.map_one]
    rw [hx, zero_add] at h1
    rw [h1]
  refine isUnit_iff_exists_inv.2 ⟨⟨(x : F)⁻¹, (mem_intRing v).2 hinv⟩, ?_⟩
  apply Subtype.ext
  exact mul_inv_cancel₀ hx0
end ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding
