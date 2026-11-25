-- Prove2me | solution 1 for SNumbers.IsSNumberSequence.abs_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:16:57.430275+00:00
-- url     : https://prove2.me/submissions/2e5d6b10-e966-4ca0-9094-c2a3e31d4a91

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
namespace IsSNumberSequence
theorem _root_.solution {s : Family 𝕜} (h : IsSNumberSequence s)
    {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (S T : X →L[𝕜] Y) (n : ℕ) :
    |s S n - s T n| ≤ ‖S - T‖ := by
  have h₁ := h.subadditive T (S - T) n
  have h₂ := h.subadditive S (T - S) n
  rw [add_sub_cancel] at h₁
  rw [add_sub_cancel, norm_sub_rev] at h₂
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
end IsSNumberSequence
end SNumbers
