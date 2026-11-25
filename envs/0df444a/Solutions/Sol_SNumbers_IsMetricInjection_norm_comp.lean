-- Prove2me | solution 1 for SNumbers.IsMetricInjection.norm_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:01:11.240964+00:00
-- url     : https://prove2.me/submissions/8f718e13-062e-4f03-8ef0-2a9b91104e7c

module
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_Injectivity

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
namespace IsMetricInjection
theorem _root_.solution {J : Y →L[𝕜] Z} (hJ : IsMetricInjection J)
    (T : W →L[𝕜] Y) : ‖J.comp T‖ = ‖T‖ := by
  refine le_antisymm ?_ ?_
  · -- `‖(J ∘ T) x‖ = ‖J (T x)‖ = ‖T x‖ ≤ ‖T‖ ‖x‖`.
    refine (J.comp T).opNorm_le_bound (norm_nonneg T) fun x => ?_
    rw [ContinuousLinearMap.comp_apply, hJ]
    exact T.le_opNorm x
  · -- `‖T x‖ = ‖J (T x)‖ = ‖(J ∘ T) x‖ ≤ ‖J ∘ T‖ ‖x‖`.
    refine T.opNorm_le_bound (norm_nonneg _) fun x => ?_
    have h := (J.comp T).le_opNorm x
    rwa [ContinuousLinearMap.comp_apply, hJ] at h
end IsMetricInjection
end SNumbers
