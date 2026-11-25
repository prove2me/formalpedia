-- Prove2me | solution 1 for SNumbers.Embedding.gelfandNumber_eq_approximationNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:32:30.591572+00:00
-- url     : https://prove2.me/submissions/e544e9b0-c3f7-4a2b-baf6-0e52c1e33c8c

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Injectivity
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Definitions.Def_SNumbers_GelfandEmbedding
public import Theorems.Thm_SNumbers_Embedding_isMetricInjection_J
public import Theorems.Thm_SNumbers_Embedding_approximationNumber_J_comp_le
public import Theorems.Thm_SNumbers_gelfandNumber_comp_metricInjection
public import Theorems.Thm_SNumbers_isSNumberSequence_gelfandNumber
public import Theorems.Thm_SNumbers_sn_le_approximationNumber


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
    gelfandNumber S n = approximationNumber ((J : Y →L[𝕜] _).comp S) n := by
  refine le_antisymm ?_ (approximationNumber_J_comp_le S n)
  rw [← gelfandNumber_comp_metricInjection isMetricInjection_J S n]
  exact sn_le_approximationNumber isSNumberSequence_gelfandNumber _ n
end SNumbers.Embedding
