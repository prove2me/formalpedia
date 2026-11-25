-- Prove2me | solution 1 for SNumbers.approximationNumber_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:31:33.082792+00:00
-- url     : https://prove2.me/submissions/a2ee058b-87aa-40e8-8ae6-e74cf2c15957

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Approximation
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_approximationNumber_additive
public import Theorems.Thm_ContinuousLinearMap_rank_zero
attribute [local simp] ContinuousLinearMap.rank_zero


attribute [local simp] SNumbers.approximationNumber_zero_eq_norm

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
theorem _root_.solution (S T : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber (S + T) n ≤ approximationNumber S n + ‖T‖ := by
  have h := approximationNumber_additive S T n 0
  rwa [Nat.add_zero, approximationNumber_zero_eq_norm] at h
end SNumbers
