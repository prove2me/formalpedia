-- Prove2me | solution 1 for SNumbers.deviationFromRestriction_comp_metricInjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:03:01.200735+00:00
-- url     : https://prove2.me/submissions/e20c3852-2892-44ac-bdb9-f290aa043698

module
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_Injectivity
public import Theorems.Thm_SNumbers_IsMetricInjection_norm_comp
public import Theorems.Thm_SNumbers_IsMetricSurjection_norm_comp

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
    (hJ : IsMetricInjection J) (S : X →L[𝕜] Y) (M : Submodule 𝕜 X) :
    deviationFromRestriction (J.comp S) M = deviationFromRestriction S M := by
  unfold deviationFromRestriction
  rw [ContinuousLinearMap.comp_assoc]
  exact hJ.norm_comp _
end SNumbers
