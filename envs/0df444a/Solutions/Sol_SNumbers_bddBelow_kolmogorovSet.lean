-- Prove2me | solution 1 for SNumbers.bddBelow_kolmogorovSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:02:26.840041+00:00
-- url     : https://prove2.me/submissions/43b6627d-12b0-401c-a693-831f06659217

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_QuotientMapNorms
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Kolmogorov
public import Theorems.Thm_SNumbers_deviationFromSubspace_nonneg

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
    BddBelow (kolmogorovSet S n) :=
  ⟨0, by rintro _ ⟨V, _, rfl⟩; exact deviationFromSubspace_nonneg S V⟩
end SNumbers
