-- Prove2me | solution 1 for SNumbers.sn_comp_metricInjection_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:21:49.281324+00:00
-- url     : https://prove2.me/submissions/e44af4de-e117-43d7-a2e2-6e9bd74139f3

module
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_Injectivity
public import Theorems.Thm_SNumbers_IsMetricInjection_norm_le_one

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
theorem _root_.solution {s : Family 𝕜} (hs : IsSNumberSequence s)
    (S : X →L[𝕜] Y) {J : Y →L[𝕜] Z} (hJ : IsMetricInjection J) (n : ℕ) :
    s (J.comp S) n ≤ s S n := by
  have h := hs.ideal (ContinuousLinearMap.id 𝕜 X) S J n
  rw [ContinuousLinearMap.comp_id] at h
  have hsn := hs.nonneg S n
  have hidX : ‖ContinuousLinearMap.id 𝕜 X‖ ≤ 1 := norm_id_le
  have hb : ‖J‖ * s S n ≤ s S n := by nlinarith [hsn, hJ.norm_le_one, norm_nonneg J]
  have hba : ‖J‖ * s S n * ‖ContinuousLinearMap.id 𝕜 X‖ ≤ s S n := by
    nlinarith [hb, hidX, mul_nonneg (norm_nonneg J) hsn]
  linarith [h]
end SNumbers
