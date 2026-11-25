-- Prove2me | solution 1 for SNumbers.norm_det_le_detNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:36:23.303318+00:00
-- url     : https://prove2.me/submissions/66506f4e-e0b8-4ac5-9c99-1c0d48caa8b8

module
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_MaxDifference
public import Theorems.Thm_SNumbers_detSet_bddAbove

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
theorem _root_.solution (S : X →L[𝕜] Y) {k : ℕ}
    {A : EuclideanSpace 𝕜 (Fin k) →L[𝕜] X} {B : Y →L[𝕜] EuclideanSpace 𝕜 (Fin k)}
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    ‖LinearMap.det (B.comp (S.comp A) :
        EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))‖ ≤ detNumber S k :=
  le_csSup (detSet_bddAbove S k) ⟨A, B, hA, hB, rfl⟩
end SNumbers
