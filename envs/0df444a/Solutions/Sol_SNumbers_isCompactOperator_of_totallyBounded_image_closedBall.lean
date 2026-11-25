-- Prove2me | solution 1 for SNumbers.isCompactOperator_of_totallyBounded_image_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:46:55.2366+00:00
-- url     : https://prove2.me/submissions/13c35480-9e43-4730-93a0-53d2e5a358d7

module
public import Definitions.Def_AddOns_Approximable
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_EntropyBounds
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_AddOns_Compact
public import Theorems.Thm_SNumbers_isCompactOperator_of_tendsto_entropyNumber
public import Theorems.Thm_SNumbers_tendsto_entropyNumber_iff_totallyBounded


set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open scoped Cardinal
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
namespace SNumbers
theorem _root_.solution [CompleteSpace Y]
    {S : X →L[𝕜] Y} (hS : TotallyBounded (⇑S '' Metric.closedBall 0 1)) :
    IsCompactOperator S :=
  isCompactOperator_of_tendsto_entropyNumber
    ((tendsto_entropyNumber_iff_totallyBounded S).mpr hS)
end SNumbers
