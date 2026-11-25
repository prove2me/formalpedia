-- Prove2me | solution 1 for PI.ProdFormulaE.HaarBox.image_eq_of_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:20:50.238877+00:00
-- url     : https://prove2.me/submissions/34ab484b-7dc7-452f-9837-93621232b560

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarBox
import Theorems.Thm_PI_ProdFormulaE_HaarBox_isOpen_box
import Theorems.Thm_PI_ProdFormulaE_HaarBox_isCompact_box
import Theorems.Thm_PI_ProdFormulaE_HaarBox_zero_mem_box
import Theorems.Thm_PI_ProdFormulaE_HaarBox_image_eq_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.style.haveILetI false
open MeasureTheory Measure ValuativeRel Topology Filter Module
open scoped NNReal ENNReal Pointwise
open PI PI.ProdFormulaE PI.ProdFormulaE.HaarBox
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {E : Type} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsModuleTopology K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable [MeasurableSpace E] [BorelSpace E]
namespace PI.ProdFormulaE.HaarBox
theorem _root_.solution (b : Basis ι K E) (μ : Measure E) [μ.IsAddHaarMeasure] (T : E ≃ₗ[K] E)
    (γ : ι → ValueGroupWithZero K) (hγ : ∀ i, γ i ≠ 0) (c : ℝ≥0∞)
    (hc : μ (T '' box b γ) = c * μ (box b γ)) (S : Set E) : μ (T '' S) = c * μ S := by
  obtain ⟨c', hc'⟩ := image_eq_smul b μ T
  have hpos : μ (box b γ) ≠ 0 := (isOpen_box b γ hγ).measure_ne_zero μ ⟨0, zero_mem_box b γ⟩
  have hfin : μ (box b γ) ≠ ⊤ := (isCompact_box b γ).measure_lt_top.ne
  rw [hc' (box b γ)] at hc
  have hcc : ((c' : ℝ≥0∞)) = c := (ENNReal.mul_left_inj hpos hfin).mp hc
  rw [hc' S, hcc]
end PI.ProdFormulaE.HaarBox
