-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_TB_Mink_exists_small_mem_ideal__e7daf5da2ddb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:13:27.698925+00:00
-- url     : https://prove2.me/submissions/87a25689-09c0-4790-a07c-bcdeb06d9f24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExistsSmallMemIdeal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Mink_exists_small_mem_ideal

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.Mink
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory ENNReal Module
open scoped nonZeroDivisors
variable (K : Type) [Field K] [NumberField K]
namespace ReciprocityTheory.ChartRestriction.G.TB.Mink
theorem _root_.solution (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ∃ a : 𝓞 K, a ∈ I ∧ a ≠ 0 ∧ ∀ σ : K →+* ℂ,
      ‖σ (a : K)‖ < 3 * ((Ideal.absNorm I : ℝ) * Real.sqrt |(discr K : ℝ)|) ^ ((finrank ℚ K : ℝ)⁻¹) := by
  obtain ⟨a, ha, hne, hlt⟩ := exists_small_mem_ideal K I hI
  exact ⟨a, ha, hne, fun σ => (InfinitePlace.apply σ (a : K)).symm ▸ hlt (InfinitePlace.mk σ)⟩
end ReciprocityTheory.ChartRestriction.G.TB.Mink
