-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_ArgumentConvergenceLemmas_tendsto_logErrorBound_nhdsWithin_5a678e65cdbe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:45:42.311835+00:00
-- url     : https://prove2.me/submissions/3f6e641f-9d57-4e00-b105-da1cbd5a191d

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_RegularizedMaxC2ExampleRealLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsOpenKappaOpenNeighbourhood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_NormIteratedFDerivCompLeOfIsOpen
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open GroundTheory.Heights₂.Heights.AnalyticLimit.ArgumentConvergenceLemmas
open Filter Topology Metric Set MeasureTheory
open scoped ContDiff
open ReciprocityTheory.AnForm.A (Mollifier molli shrink)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (errE errorWithLinear ell)
noncomputable section
namespace GroundTheory.Heights₂.Heights.AnalyticLimit.ArgumentConvergenceLemmas
theorem _root_.solution (C : ℝ) : Tendsto (fun t => errorWithLinear C t) (𝓝[>] 0) (𝓝 0) := by
  have hell : Tendsto ell (𝓝[>] (0 : ℝ)) atTop :=
    Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h2 : Tendsto (fun t => errE C t) (𝓝[>] 0) (𝓝 0) := by
    have := (h1.comp hell).const_mul C
    rw [mul_zero] at this
    refine this.congr fun t => ?_
    simp only [Function.comp, errE, mul_div_assoc]
  have h3 : Tendsto (fun t : ℝ => C * t) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => C * t) (𝓝 0) (𝓝 (C * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  simpa [errorWithLinear] using h2.add h3
end GroundTheory.Heights₂.Heights.AnalyticLimit.ArgumentConvergenceLemmas
