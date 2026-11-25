-- Prove2me | solution 1 for SNumbers.isCompactOperator_of_tendsto_kolmogorovNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:23:31.508291+00:00
-- url     : https://prove2.me/submissions/5890a10e-3a4c-46ea-8cab-c916a0b4b2af

module
public import Definitions.Def_AddOns_Approximable
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_EntropyBounds
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_AddOns_Compact
public import Theorems.Thm_SNumbers_isCompactOperator_of_totallyBounded_image_closedBall
public import Theorems.Thm_SNumbers_totallyBounded_of_tendsto_kolmogorovNumber

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
theorem _root_.solution [CompleteSpace Y]
    {S : X →L[𝕜] Y} (hS : Tendsto (kolmogorovNumber S) atTop (𝓝 0)) :
    IsCompactOperator S :=
  isCompactOperator_of_totallyBounded_image_closedBall
    (totallyBounded_of_tendsto_kolmogorovNumber hS)
end SNumbers
