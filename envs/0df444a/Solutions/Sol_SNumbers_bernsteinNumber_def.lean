-- Prove2me | solution 1 for SNumbers.bernsteinNumber_def
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:23:32.010353+00:00
-- url     : https://prove2.me/submissions/ffbd4321-1fef-4011-bbcd-0eb1bb8ea75d

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_Injectivity
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Definitions.Def_SNumbers_Bernstein

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
theorem _root_.solution (S : X →L[𝕜] Y) (n : ℕ) :
    bernsteinNumber S n = sSup (bernsteinSet S n) := rfl
end SNumbers
