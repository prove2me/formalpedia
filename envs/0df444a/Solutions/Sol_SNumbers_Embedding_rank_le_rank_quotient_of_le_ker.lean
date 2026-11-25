-- Prove2me | solution 1 for SNumbers.Embedding.rank_le_rank_quotient_of_le_ker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:13:19.703852+00:00
-- url     : https://prove2.me/submissions/73d04635-c5ca-4f78-b61f-abc173419006

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Injectivity
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Definitions.Def_SNumbers_GelfandEmbedding

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
theorem _root_.solution {Z : Type u} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    (L : X →L[𝕜] Z) {M : Submodule 𝕜 X} (h : M ≤ LinearMap.ker (L : X →ₗ[𝕜] Z)) :
    L.rank ≤ Module.rank 𝕜 (X ⧸ M) := by
  rw [ContinuousLinearMap.rank, LinearMap.rank, ← Submodule.range_liftQ M _ h]
  exact rank_range_le _
end SNumbers.Embedding
