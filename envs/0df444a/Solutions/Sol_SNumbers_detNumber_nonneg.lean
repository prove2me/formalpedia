-- Prove2me | solution 1 for SNumbers.detNumber_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:58:32.005034+00:00
-- url     : https://prove2.me/submissions/38b76b37-ae7a-4081-a1c9-8bf98d1f565b

module
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_MaxDifference

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
theorem _root_.solution (S : X →L[𝕜] Y) (k : ℕ) : 0 ≤ detNumber S k :=
  Real.sSup_nonneg <| by rintro r ⟨A, B, _, _, rfl⟩; exact norm_nonneg _
end SNumbers
