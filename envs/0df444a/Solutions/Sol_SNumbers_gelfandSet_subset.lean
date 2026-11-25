-- Prove2me | solution 1 for SNumbers.gelfandSet_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:27:35.498915+00:00
-- url     : https://prove2.me/submissions/1a8317f3-677f-4ad4-b409-f8f9ce9fbedc

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Gelfand

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
    gelfandSet S n ⊆ gelfandSet S m := by
  rintro _ ⟨M, hM_closed, hM_rank, rfl⟩
  exact ⟨M, hM_closed, hM_rank.trans (by exact_mod_cast h), rfl⟩
end SNumbers
