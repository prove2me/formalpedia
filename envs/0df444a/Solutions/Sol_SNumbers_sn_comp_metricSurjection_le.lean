-- Prove2me | solution 1 for SNumbers.sn_comp_metricSurjection_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:22:27.662873+00:00
-- url     : https://prove2.me/submissions/56cbf191-d459-4d63-a898-f53ec6876bdc

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
    (S : X →L[𝕜] Y) {Q : W →L[𝕜] X} (hQ : IsMetricSurjection Q) (n : ℕ) :
    s (S.comp Q) n ≤ s S n := by
  have h := hs.ideal Q S (ContinuousLinearMap.id 𝕜 Y) n
  rw [ContinuousLinearMap.id_comp] at h
  have hsn := hs.nonneg S n
  have hidY : ‖ContinuousLinearMap.id 𝕜 Y‖ ≤ 1 := norm_id_le
  have hb : ‖ContinuousLinearMap.id 𝕜 Y‖ * s S n ≤ s S n := by
    nlinarith [hsn, hidY, norm_nonneg (ContinuousLinearMap.id 𝕜 Y)]
  have hba : ‖ContinuousLinearMap.id 𝕜 Y‖ * s S n * ‖Q‖ ≤ s S n := by
    nlinarith [hb, hQ.norm_le_one, mul_nonneg (norm_nonneg (ContinuousLinearMap.id 𝕜 Y)) hsn,
      norm_nonneg Q]
  linarith [h]
end SNumbers
