-- Prove2me | solution 1 for SNumbers.gelfandNumber_comp_metricInjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:03:45.166807+00:00
-- url     : https://prove2.me/submissions/7b1db81f-5e35-4624-a9e2-9110062f7c0e

module
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_Injectivity
public import Theorems.Thm_SNumbers_deviationFromRestriction_comp_metricInjection
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] Submodule.liftQL_mkQL



set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SNumbers
theorem _root_.solution {J : Y →L[𝕜] Z}
    (hJ : IsMetricInjection J) (S : X →L[𝕜] Y) (n : ℕ) :
    gelfandNumber (J.comp S) n = gelfandNumber S n := by
  unfold gelfandNumber
  congr 1
  ext r
  simp only [gelfandSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨M, hcl, hrank, rfl⟩
    exact ⟨M, hcl, hrank, deviationFromRestriction_comp_metricInjection hJ S M⟩
  · rintro ⟨M, hcl, hrank, rfl⟩
    exact ⟨M, hcl, hrank, (deviationFromRestriction_comp_metricInjection hJ S M).symm⟩
end SNumbers
