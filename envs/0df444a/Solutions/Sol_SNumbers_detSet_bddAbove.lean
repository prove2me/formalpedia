-- Prove2me | solution 1 for SNumbers.detSet_bddAbove
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:31:43.723592+00:00
-- url     : https://prove2.me/submissions/cc457cf3-68dd-4cd8-bfad-66b362fa7a0a

module
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_MaxDifference
public import Theorems.Thm_SNumbers_norm_det_le_pow_norm
public import Theorems.Thm_SNumbers_norm_comp_comp_le

section
@[expose] public section
universe u
open ContinuousLinearMap
open scoped Pointwise
namespace SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
private lemma detSet_le_pow_norm (S : X →L[𝕜] Y) (k : ℕ) :
    ∀ r ∈ detSet S k, r ≤ ‖S‖ ^ k := by
  rintro r ⟨A, B, hA, hB, rfl⟩
  refine (norm_det_le_pow_norm _).trans (pow_le_pow_left₀ (norm_nonneg _) ?_ k)
  calc ‖B.comp (S.comp A)‖
      ≤ ‖B‖ * ‖S‖ * ‖A‖ := norm_comp_comp_le A S B
    _ ≤ 1 * ‖S‖ * 1 := by gcongr
    _ = ‖S‖ := by ring
section Border
variable {k : ℕ}
variable (A : EuclideanSpace 𝕜 (Fin k) →L[𝕜] X) (x : X)
  (B : Y →L[𝕜] EuclideanSpace 𝕜 (Fin k)) (b : Y →L[𝕜] 𝕜) (lam mu : ℝ)
end Border
end SNumbers
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open scoped Pointwise
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
namespace SNumbers
theorem _root_.solution (S : X →L[𝕜] Y) (k : ℕ) : BddAbove (detSet S k) :=
  ⟨‖S‖ ^ k, detSet_le_pow_norm S k⟩
end SNumbers
