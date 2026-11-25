-- Prove2me | solution 1 for SNumbers.kolmogorovSet_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:29:08.9258+00:00
-- url     : https://prove2.me/submissions/a537044e-9a51-4f2a-8dd8-4bee477c999a

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_QuotientMapNorms
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Kolmogorov

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
    kolmogorovSet S n ⊆ kolmogorovSet S m := by
  rintro _ ⟨V, hV, rfl⟩
  exact ⟨V, hV.trans (by exact_mod_cast h), rfl⟩
end SNumbers
