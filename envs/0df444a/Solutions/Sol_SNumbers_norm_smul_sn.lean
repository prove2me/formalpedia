-- Prove2me | solution 1 for SNumbers.norm_smul_sn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:18:15.764627+00:00
-- url     : https://prove2.me/submissions/37d9d4d6-9306-410f-ae4d-b4d4a3e68e32

module
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Definitions.Def_SNumbers_Basic
public import Theorems.Thm_SNumbers_sn_smul_le
public import Theorems.Thm_SNumbers_norm_smul_le_sn

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
    s (c • T) n = ‖c‖ * s T n := by
  rcases eq_or_ne c 0 with rfl | hc
  · refine le_antisymm (sn_smul_le hs 0 T n) ?_
    rw [norm_zero, zero_mul]
    exact hs.nonneg (0 • T) n
  exact le_antisymm (sn_smul_le hs c T n) (norm_smul_le_sn hs hc T n)
end SNumbers
