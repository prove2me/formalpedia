-- Prove2me | solution 1 for SNumbers.kolmogorovNumber_comp_metricSurjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:03:10.589115+00:00
-- url     : https://prove2.me/submissions/111f35c8-d345-464e-b77c-a6402bbde23b

module
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_Injectivity
public import Theorems.Thm_SNumbers_deviationFromSubspace_comp_metricSurjection
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
theorem _root_.solution {Q : W →L[𝕜] X}
    (hQ : IsMetricSurjection Q) (S : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber (S.comp Q) n = kolmogorovNumber S n := by
  unfold kolmogorovNumber
  congr 1
  ext r
  simp only [kolmogorovSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨V, hrank, rfl⟩
    exact ⟨V, hrank, deviationFromSubspace_comp_metricSurjection hQ S V⟩
  · rintro ⟨V, hrank, rfl⟩
    exact ⟨V, hrank, (deviationFromSubspace_comp_metricSurjection hQ S V).symm⟩
end SNumbers
