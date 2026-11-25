-- Prove2me | solution 1 for SNumbers.gelfandNumber_le_deviation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:58:44.098795+00:00
-- url     : https://prove2.me/submissions/11b32915-bfcb-4e9a-b457-e53f0186f2a6

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Gelfand
public import Theorems.Thm_SNumbers_bddBelow_gelfandSet

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
theorem _root_.solution {S : X →L[𝕜] Y} {n : ℕ} {M : Submodule 𝕜 X}
    (hM_closed : IsClosed (M : Set X))
    (hM_rank : Module.rank 𝕜 (X ⧸ M) ≤ (n : Cardinal)) :
    gelfandNumber S n ≤ deviationFromRestriction S M :=
  csInf_le (bddBelow_gelfandSet S n) ⟨M, hM_closed, hM_rank, rfl⟩
end SNumbers
