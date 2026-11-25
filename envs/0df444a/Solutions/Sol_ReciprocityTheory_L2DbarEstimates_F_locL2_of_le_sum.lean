-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.locL2_of_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:33:38.462934+00:00
-- url     : https://prove2.me/submissions/a71ef4f4-f7aa-43a9-b4fd-d41a0d3303d7

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_LocalizeA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_loc_memLp_iff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add


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
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {M E F₁ F₂ : Type*} [TopologicalSpace M] [MeasurableSpace M]
    [NormedAddCommGroup E] [NormedAddCommGroup F₁] [NormedAddCommGroup F₂] (μ : Measure M)
    (f : M → E) (g₁ : M → F₁) (g₂ : M → F₂) (c : ℝ) (h₁ : LocalL2Isometry μ g₁) (h₂ : LocalL2Isometry μ g₂)
    (hf : AEStronglyMeasurable f μ) (hle : ∀ x, ‖f x‖ ≤ c * (‖g₁ x‖ + ‖g₂ x‖)) : LocalL2Isometry μ f := by
  refine ⟨hf, fun C hC => ?_⟩
  have m1 : MemLp g₁ 2 (μ.restrict C) := (loc_memLp_iff _ _ h₁.1.restrict).mpr (h₁.2 C hC)
  have m2 : MemLp g₂ 2 (μ.restrict C) := (loc_memLp_iff _ _ h₂.1.restrict).mpr (h₂.2 C hC)
  have m3 : MemLp (fun x => c * (‖g₁ x‖ + ‖g₂ x‖)) 2 (μ.restrict C) := (m1.norm.add m2.norm).const_mul c
  have m4 : MemLp f 2 (μ.restrict C) := m3.of_le hf.restrict (Filter.Eventually.of_forall fun x => by
    show ‖f x‖ ≤ ‖c * (‖g₁ x‖ + ‖g₂ x‖)‖
    rw [Real.norm_eq_abs]
    exact (hle x).trans (le_abs_self _))
  exact (loc_memLp_iff _ _ hf.restrict).mp m4
end ReciprocityTheory.L2DbarEstimates.F
