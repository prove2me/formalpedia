-- Prove2me | solution 1 for P2M_SNumbers_gelfandNumber_antitone__140691ee51a6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:28:54.266134+00:00
-- url     : https://prove2.me/submissions/9f384627-4e8b-4e66-bc8b-4d9828512c66

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Gelfand
public import Theorems.Thm_SNumbers_gelfandSet_nonempty
public import Theorems.Thm_SNumbers_bddBelow_gelfandSet
public import Theorems.Thm_SNumbers_gelfandSet_subset

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
theorem _root_.solution (S : X →L[𝕜] Y) {n m : ℕ} (h : n ≤ m) :
    gelfandNumber S m ≤ gelfandNumber S n :=
  csInf_le_csInf (bddBelow_gelfandSet S m) (gelfandSet_nonempty S n)
    (gelfandSet_subset S h)
end SNumbers
