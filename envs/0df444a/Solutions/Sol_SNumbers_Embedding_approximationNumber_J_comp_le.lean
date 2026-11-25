-- Prove2me | solution 1 for SNumbers.Embedding.approximationNumber_J_comp_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:17:34.98159+00:00
-- url     : https://prove2.me/submissions/42f398af-546e-4976-ad5a-1af4acaaffc1

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Injectivity
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Definitions.Def_SNumbers_GelfandEmbedding
public import Theorems.Thm_SNumbers_Embedding_rank_le_rank_quotient_of_le_ker
public import Theorems.Thm_SNumbers_Embedding_exists_le_ker_norm_sub_le
public import Theorems.Thm_SNumbers_approximationNumber_le_norm_sub
public import Theorems.Thm_SNumbers_gelfandNumber_def
public import Theorems.Thm_SNumbers_gelfandSet_nonempty


set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal ENNReal
open ContinuousLinearMap
open SNumbers
open SNumbers.Embedding
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
namespace SNumbers.Embedding
theorem _root_.solution (S : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber ((J : Y →L[𝕜] _).comp S) n ≤ gelfandNumber S n := by
  rw [gelfandNumber_def]
  refine le_csInf (gelfandSet_nonempty S n) ?_
  rintro _ ⟨M, -, hM, rfl⟩
  obtain ⟨L, hker, hnorm⟩ := exists_le_ker_norm_sub_le S M
  exact (approximationNumber_le_norm_sub
    ((rank_le_rank_quotient_of_le_ker L hker).trans hM)).trans hnorm
end SNumbers.Embedding
