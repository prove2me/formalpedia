-- Prove2me | solution 1 for SNumbers.approximationNumber_id_euclidean
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:38:00.206316+00:00
-- url     : https://prove2.me/submissions/0c5b2184-1d73-44d9-a0eb-2171582184fd

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Approximation
public import Theorems.Thm_SNumbers_approximationNumber_strict
public import Theorems.Thm_P2M_SNumbers_finrank_euclideanSpace_fin__a8e0c4e81f72


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
variable [CompleteSpace 𝕜]
namespace SNumbers
theorem _root_.solution (n : ℕ) :
    approximationNumber
      (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n = 1 := by
  have h : n < Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) := by
    rw [finrank_euclideanSpace_fin' (n + 1)]; exact Nat.lt_succ_self n
  exact approximationNumber_strict n (Module.lt_rank_of_lt_finrank h)
end SNumbers
