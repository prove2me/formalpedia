-- Prove2me | solution 1 for SNumbers.approximationNumber_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:31:26.822344+00:00
-- url     : https://prove2.me/submissions/341c25b4-3142-4688-8ad7-57f49d5b588f

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Approximation
public import Theorems.Thm_SNumbers_approximationNumber_antitone
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
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
theorem _root_.solution (S : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber S n ≤ ‖S‖ :=
  (antitone_nat_of_succ_le (approximationNumber_antitone S) (Nat.zero_le n)).trans_eq
    (approximationNumber_zero_eq_norm S)
end SNumbers
