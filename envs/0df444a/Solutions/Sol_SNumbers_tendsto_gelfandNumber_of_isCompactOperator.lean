-- Prove2me | solution 1 for SNumbers.tendsto_gelfandNumber_of_isCompactOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:24:03.475654+00:00
-- url     : https://prove2.me/submissions/f02f0a95-dbeb-4024-a535-3605c70ddf64

module
public import Definitions.Def_AddOns_Approximable
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_EntropyBounds
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_AddOns_Compact
public import Theorems.Thm_SNumbers_totallyBounded_image_closedBall_of_isCompactOperator
public import Theorems.Thm_SNumbers_tendsto_gelfandNumber_of_totallyBounded

set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open scoped Cardinal
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
namespace SNumbers
theorem _root_.solution {S : X →L[𝕜] Y}
    (hS : IsCompactOperator S) : Tendsto (gelfandNumber S) atTop (𝓝 0) :=
  tendsto_gelfandNumber_of_totallyBounded
    (totallyBounded_image_closedBall_of_isCompactOperator hS)
end SNumbers
