-- Prove2me | solution 1 for SNumbers.Embedding.toLInfty_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:13:14.060322+00:00
-- url     : https://prove2.me/submissions/36723725-88ac-4b38-ba93-fd3d255a11bd

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
variable {ι : Type u}
namespace SNumbers.Embedding
theorem _root_.solution (f : ι → X →L[𝕜] 𝕜) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i, ‖f i‖ ≤ C) (x : X) (i : ι) :
    (toLInfty f hC0 hC x : ι → 𝕜) i = f i x := rfl
end SNumbers.Embedding
