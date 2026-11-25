-- Prove2me | solution 1 for P2M_SNumbers_approximationNumber_antitone__260bc309c16c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:49:07.101955+00:00
-- url     : https://prove2.me/submissions/9b0dd26a-ecf3-490e-8de2-215d52805e65

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Approximation
public import Theorems.Thm_SNumbers_approximationSet_nonempty
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
theorem _root_.solution {S : X →L[𝕜] Y} {n m : ℕ} (h : n ≤ m) :
    approximationNumber S m ≤ approximationNumber S n := by
  refine csInf_le_csInf (bddBelow_approximationSet S m) (approximationSet_nonempty S n) ?_
  rintro r ⟨L, hL, rfl⟩
  exact ⟨L, hL.trans (by exact_mod_cast h), rfl⟩
end SNumbers
