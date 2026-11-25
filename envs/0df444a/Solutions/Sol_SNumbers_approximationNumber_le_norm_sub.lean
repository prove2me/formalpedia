-- Prove2me | solution 1 for SNumbers.approximationNumber_le_norm_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:14:19.276453+00:00
-- url     : https://prove2.me/submissions/266e29b7-3c98-41a6-9236-d32bec8ce1ee

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Approximation
public import Theorems.Thm_SNumbers_bddBelow_approximationSet

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
theorem _root_.solution {S : X →L[𝕜] Y} {n : ℕ}
    {L : X →L[𝕜] Y} (hL : L.rank ≤ (n : Cardinal)) :
    approximationNumber S n ≤ ‖S - L‖ :=
  csInf_le (bddBelow_approximationSet S n) ⟨L, hL, rfl⟩
end SNumbers
