-- Prove2me | solution 1 for Sqrt6KissingBound.preimage_strictCone_linearIsometryEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:04:31.911406+00:00
-- url     : https://prove2.me/submissions/7d3e3798-e97f-4760-9155-8e8d01a47cc3

import Mathlib
import Definitions.Def_Sqrt6KissingBound_Geometry

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set
open NormedSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace Sqrt6KissingBound
theorem _root_.solution (A : E ≃ₗᵢ[ℝ] E) {x z : E}
    (hAx : A x = z) : A ⁻¹' strictCone z = strictCone x := by
  ext y
  change (s3 / 2) * ‖A y‖ < inner ℝ z (A y) ↔
    (s3 / 2) * ‖y‖ < inner ℝ x y
  rw [A.norm_map, ← hAx, A.inner_map_map]
end Sqrt6KissingBound
