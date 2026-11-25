-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.ap_holo_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:17:20.484851+00:00
-- url     : https://prove2.me/submissions/75a54e8a-af03-4de9-813b-b41ee0c16a83

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IntegralFderivApplyEqZero
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_contDiffOn_of_differentiableOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ)
    (hf : Holo n z f) (k : Fin n) : Holo n z (d n z k f) := by
  intro e he
  have hh : DifferentiableOn ℂ (f ∘ e.symm) e.target := hf e he
  have hcd : ContDiffOn ℂ ∞ (f ∘ e.symm) e.target :=
    contDiffOn_of_differentiableOn n _ _ e.open_target hh
  have hfd : DifferentiableOn ℂ (fun y => fderiv ℂ (f ∘ e.symm) y (bas n k)) e.target := by
    have h1 := (hcd.fderiv_of_isOpen e.open_target (m := ∞) (by exact_mod_cast le_top)).differentiableOn
      (by norm_num)
    exact h1.clm_apply (differentiableOn_const _)
  refine hfd.congr (fun y hy => ?_)
  simp only [Function.comp_apply]
  rw [d_comp_symm n z e he k f y hy]
  have hd := (hh.differentiableAt (e.open_target.mem_nhds hy)).hasFDerivAt
  rw [wd, (hd.restrictScalars ℝ).fderiv]
  simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.map_smul, smul_eq_mul]
  rw [← mul_assoc, Complex.I_mul_I]
  ring
end ReciprocityTheory.L2DbarEstimates.I
