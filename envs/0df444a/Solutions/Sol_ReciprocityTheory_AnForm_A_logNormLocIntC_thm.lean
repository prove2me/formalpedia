-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.logNormLocIntC_thm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:18:40.718834+00:00
-- url     : https://prove2.me/submissions/84526993-9535-4712-b6c2-a19ea9d52b68

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogIntSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Theorems.Thm_ReciprocityTheory_AnForm_A_locallyIntegrable_comp_fst_real
import Theorems.Thm_ReciprocityTheory_AnForm_A_locallyIntegrable_comp_snd_real
import Theorems.Thm_ReciprocityTheory_AnForm_A_locallyIntegrable_norm_real_log
import Theorems.Thm_ReciprocityTheory_AnForm_A_norm_log_norm_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution : LogNormLocIntCStatement := by
  have hH : LocallyIntegrable
      (fun p : ℝ × ℝ => ‖Real.log p.1‖ + ‖Real.log p.2‖ + ‖p.1‖ + ‖p.2‖) volume :=
    (((locallyIntegrable_comp_fst_real locallyIntegrable_norm_real_log).add
      (locallyIntegrable_comp_snd_real locallyIntegrable_norm_real_log)).add
      (locallyIntegrable_comp_fst_real (continuous_norm (E := ℝ)).locallyIntegrable)).add
      (locallyIntegrable_comp_snd_real (continuous_norm (E := ℝ)).locallyIntegrable)
  have hG : LocallyIntegrable
      (fun z : ℂ => ‖Real.log z.re‖ + ‖Real.log z.im‖ + ‖z.re‖ + ‖z.im‖) volume := by
    intro x
    obtain ⟨s, hs, hint⟩ := hH (Complex.measurableEquivRealProd x)
    have hcont : Continuous (Complex.measurableEquivRealProd : ℂ → ℝ × ℝ) := by
      show Continuous fun z : ℂ => (z.re, z.im)
      fun_prop
    refine ⟨Complex.measurableEquivRealProd ⁻¹' s, hcont.continuousAt.preimage_mem_nhds hs, ?_⟩
    exact (Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
      Complex.measurableEquivRealProd.measurableEmbedding).mpr hint
  refine hG.mono (Real.measurable_log.comp continuous_norm.measurable).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  have h1 := norm_log_norm_le z
  have h2 : 0 ≤ ‖Real.log z.re‖ + ‖Real.log z.im‖ + ‖z.re‖ + ‖z.im‖ := by positivity
  calc ‖Real.log ‖z‖‖ ≤ ‖Real.log z.re‖ + ‖Real.log z.im‖ + ‖z.re‖ + ‖z.im‖ := h1
    _ = ‖‖Real.log z.re‖ + ‖Real.log z.im‖ + ‖z.re‖ + ‖z.im‖‖ := (Real.norm_of_nonneg h2).symm
end ReciprocityTheory.AnForm.A
