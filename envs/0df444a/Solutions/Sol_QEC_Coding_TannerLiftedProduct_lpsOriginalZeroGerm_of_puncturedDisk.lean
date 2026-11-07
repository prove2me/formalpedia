-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalZeroGerm_of_puncturedDisk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:18:35.2799+00:00
-- url     : https://prove2.me/submissions/682495f3-31b4-4e01-ae57-734b7a711821

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hz : ∀ q : ℂ, ‖q‖ < 1 → q ≠ 0 → f q = 0) :
    f =ᶠ[𝓝 0] 0 := by
  have hsmall : ∀ᶠ q : ℂ in 𝓝 0, ‖q‖ < 1 :=
    (isOpen_lt (continuous_norm : Continuous (fun q : ℂ => ‖q‖))
      continuous_const).mem_nhds (by norm_num : ‖(0 : ℂ)‖ < 1)
  have hp : f =ᶠ[𝓝[≠] (0 : ℂ)] 0 := by
    filter_upwards [hsmall.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with q hq hq0
    exact hz q hq hq0
  have h0 : f 0 = 0 := tendsto_nhds_unique_of_eventuallyEq
    (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) tendsto_const_nhds hp
  filter_upwards [hsmall] with q hq
  by_cases hq0 : q = 0
  · subst q
    exact h0
  · exact hz q hq hq0
end QEC.Coding.TannerLiftedProduct
