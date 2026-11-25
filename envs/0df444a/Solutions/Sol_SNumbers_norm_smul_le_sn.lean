-- Prove2me | solution 1 for SNumbers.norm_smul_le_sn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:53:22.828823+00:00
-- url     : https://prove2.me/submissions/46bf27ee-7d8b-44bc-93ce-0254d3fbf248

module
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Definitions.Def_SNumbers_Basic
public import Theorems.Thm_SNumbers_sn_smul_le

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
    {c : 𝕜} (hc : c ≠ 0) (T : X →L[𝕜] Y) (n : ℕ) :
    ‖c‖ * s T n ≤ s (c • T) n := by
  have h := sn_smul_le hs c⁻¹ (c • T) n
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul, norm_inv] at h
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  calc ‖c‖ * s T n
      ≤ ‖c‖ * (‖c‖⁻¹ * s (c • T) n) := mul_le_mul_of_nonneg_left h (norm_nonneg c)
    _ = s (c • T) n := by rw [← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul]
end SNumbers
