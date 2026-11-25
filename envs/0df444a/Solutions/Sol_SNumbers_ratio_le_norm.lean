-- Prove2me | solution 1 for SNumbers.ratio_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:42:56.809896+00:00
-- url     : https://prove2.me/submissions/d00052f6-177f-457d-b956-d7b5c528df46

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Definitions.Def_SNumbers_Hilbert
public import Theorems.Thm_SNumbers_norm_comp_comp_le
public import Theorems.Thm_SNumbers_approximationNumber_le_norm


set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y W Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SNumbers
theorem _root_.solution (S : X →L[𝕜] Y) (n : ℕ) {A : L2 𝕜 →L[𝕜] X} {B : Y →L[𝕜] L2 𝕜}
    (hA : A ≠ 0) (hB : B ≠ 0) :
    approximationNumber (B.comp (S.comp A)) n / (‖B‖ * ‖A‖) ≤ ‖S‖ := by
  have hpos : 0 < ‖B‖ * ‖A‖ := mul_pos (norm_pos_iff.mpr hB) (norm_pos_iff.mpr hA)
  rw [div_le_iff₀ hpos]
  calc approximationNumber (B.comp (S.comp A)) n
      ≤ ‖B.comp (S.comp A)‖ := approximationNumber_le_norm _ _
    _ ≤ ‖B‖ * ‖S‖ * ‖A‖ := norm_comp_comp_le A S B
    _ = ‖S‖ * (‖B‖ * ‖A‖) := by ring
end SNumbers
