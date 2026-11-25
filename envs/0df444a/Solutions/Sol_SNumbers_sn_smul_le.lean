-- Prove2me | solution 1 for SNumbers.sn_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:47:48.989939+00:00
-- url     : https://prove2.me/submissions/a76eb8ac-a2f4-4f79-9d6c-0deea7b6833e

module
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Definitions.Def_SNumbers_Basic

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
namespace SNumbers
theorem _root_.solution {s : Family 𝕜} (hs : IsSNumberSequence s)
    {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (c : 𝕜) (T : X →L[𝕜] Y) (n : ℕ) :
    s (c • T) n ≤ ‖c‖ * s T n := by
  have h := hs.ideal (ContinuousLinearMap.id 𝕜 X) T (c • ContinuousLinearMap.id 𝕜 Y) n
  rw [show (c • ContinuousLinearMap.id 𝕜 Y).comp (T.comp (ContinuousLinearMap.id 𝕜 X)) = c • T
      from by rw [ContinuousLinearMap.comp_id, ContinuousLinearMap.smul_comp,
        ContinuousLinearMap.id_comp]] at h
  have hsn : 0 ≤ s T n := hs.nonneg T n
  have hcid : ‖c • ContinuousLinearMap.id 𝕜 Y‖ ≤ ‖c‖ := by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg c)).trans_eq
      (mul_one _)
  calc s (c • T) n
      ≤ ‖c • ContinuousLinearMap.id 𝕜 Y‖ * s T n * ‖ContinuousLinearMap.id 𝕜 X‖ := h
    _ ≤ ‖c‖ * s T n * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_right hcid hsn) ContinuousLinearMap.norm_id_le
          (norm_nonneg _) (mul_nonneg (norm_nonneg _) hsn)
    _ = ‖c‖ * s T n := mul_one _
end SNumbers
