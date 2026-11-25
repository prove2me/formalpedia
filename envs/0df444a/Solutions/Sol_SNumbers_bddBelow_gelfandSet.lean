-- Prove2me | solution 1 for SNumbers.bddBelow_gelfandSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:53:18.961891+00:00
-- url     : https://prove2.me/submissions/3f773380-e482-4d2d-b24f-0b62e3dfa199

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Gelfand
public import Theorems.Thm_SNumbers_deviationFromRestriction_nonneg

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
    BddBelow (gelfandSet S n) :=
  ⟨0, by rintro _ ⟨M, _, _, rfl⟩; exact deviationFromRestriction_nonneg S M⟩
end SNumbers
