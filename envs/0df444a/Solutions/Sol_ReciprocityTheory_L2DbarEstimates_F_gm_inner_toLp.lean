-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.gm_inner_toLp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:54:19.977925+00:00
-- url     : https://prove2.me/submissions/cd9320ad-4bfb-4771-a82c-01a3e7a0fa68

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HilbertLemmas
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_HormanderEstimate_GmSingleIsTestForm
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_gm_integral_wvol
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (n : ℕ) (z : M → V n) (ph : M → ℝ) (hph : Measurable ph)
    (u : Lp ℂ 2 (wvol n z ph)) (g : M → ℂ) (hg : MemLp g 2 (wvol n z ph)) :
    ⟪u, hg.toLp g⟫_ℂ = ∫ x, (Real.exp (-ph x) : ℂ) * (conj (u x) * g x) ∂vol n z ∧
      Integrable (fun x => (Real.exp (-ph x) : ℂ) * (conj (u x) * g x)) (vol n z) := by
  have hpt : ∀ x, ⟪u x, g x⟫_ℂ = conj (u x) * g x := by
    intro x
    first
      | exact RCLike.inner_apply _ _
      | (simp [RCLike.inner_apply]; ring)
      | (simp; ring)
  have hint : Integrable (fun x => conj (u x) * g x) (wvol n z ph) := by
    refine (L2.integrable_inner (𝕜 := ℂ) u (hg.toLp g)).congr ?_
    filter_upwards [hg.coeFn_toLp] with x hx
    rw [hx, hpt]
  have hinner : ⟪u, hg.toLp g⟫_ℂ = ∫ x, conj (u x) * g x ∂wvol n z ph := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hg.coeFn_toLp] with x hx
    rw [hx, hpt]
  obtain ⟨h1, h2⟩ := gm_integral_wvol n z ph hph (fun x => conj (u x) * g x)
  exact ⟨hinner.trans h1, h2 hint⟩
end ReciprocityTheory.L2DbarEstimates.F
