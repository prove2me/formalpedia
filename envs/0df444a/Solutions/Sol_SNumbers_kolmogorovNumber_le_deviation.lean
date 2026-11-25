-- Prove2me | solution 1 for SNumbers.kolmogorovNumber_le_deviation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:07:24.33027+00:00
-- url     : https://prove2.me/submissions/b057f58b-55f8-4f0f-a7a6-a864397e9929

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_QuotientMapNorms
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Kolmogorov
public import Theorems.Thm_SNumbers_bddBelow_kolmogorovSet

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
theorem _root_.solution {S : X →L[𝕜] Y} {n : ℕ} {V : Submodule 𝕜 Y}
    (hV : Module.rank 𝕜 V ≤ (n : Cardinal)) :
    kolmogorovNumber S n ≤ deviationFromSubspace S V :=
  csInf_le (bddBelow_kolmogorovSet S n) ⟨V, hV, rfl⟩
end SNumbers
