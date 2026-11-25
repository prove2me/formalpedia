-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.logUnitMonoLocInt_thm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:41:55.934378+00:00
-- url     : https://prove2.me/submissions/e0006877-7866-4538-8ece-ee1c80103a61

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogIntSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Theorems.Thm_ReciprocityTheory_AnForm_A_logMonoLocInt_thm
import Theorems.Thm_ReciprocityTheory_AnForm_A_log_norm_prod_zpow_eq_logMono

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
theorem _root_.solution : LogUnitMonoLocIntStatement := by
  intro D m U u hU hu hu0
  have hc : ContinuousOn (fun z => Real.log ‖u z‖) U :=
    (hu.continuousOn.norm).log (fun z hz => norm_ne_zero_iff.mpr (hu0 z hz))
  have h1 : LocallyIntegrableOn (fun z => Real.log ‖u z‖ + logMono m z) U volume :=
    (hc.locallyIntegrableOn hU.measurableSet).add ((logMonoLocInt_thm D m).locallyIntegrableOn U)
  have hnull : ∀ᵐ z ∂(volume : Measure (Fin D → ℂ)), ∀ i, z i ≠ 0 := by
    rw [ae_all_iff]
    intro i
    have hs : (volume : Measure (Fin D → ℂ))
        ((LinearMap.ker (LinearMap.proj i : (Fin D → ℂ) →ₗ[ℝ] ℂ) : Submodule ℝ (Fin D → ℂ)) :
          Set (Fin D → ℂ)) = 0 := by
      apply Measure.addHaar_submodule
      intro htop
      have h2 : (Pi.single i (1 : ℂ) : Fin D → ℂ) ∈
          LinearMap.ker (LinearMap.proj i : (Fin D → ℂ) →ₗ[ℝ] ℂ) := by
        rw [htop]
        exact Submodule.mem_top
      simp at h2
    have hset : {a : Fin D → ℂ | ¬ a i ≠ 0} =
        ((LinearMap.ker (LinearMap.proj i : (Fin D → ℂ) →ₗ[ℝ] ℂ) : Submodule ℝ (Fin D → ℂ)) :
          Set (Fin D → ℂ)) := by
      ext z
      simp
    rw [ae_iff, hset]
    exact hs
  rw [locallyIntegrableOn_iff hU.isLocallyClosed] at h1 ⊢
  intro K hKU hK
  refine (h1 K hKU hK).congr_fun_ae ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' hK.isClosed.measurableSet]
  filter_upwards [hnull] with z hz hzK
  have hzU := hKU hzK
  show Real.log ‖u z‖ + logMono m z = Real.log ‖u z * ∏ i, z i ^ m i‖
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (hu0 z hzU))
    (norm_ne_zero_iff.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hz i))),
    log_norm_prod_zpow_eq_logMono m z hz]
end ReciprocityTheory.AnForm.A
