-- Prove2me | solution 1 for SNumbers.totallyBounded_image_closedBall_of_isCompactOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:46:08.40475+00:00
-- url     : https://prove2.me/submissions/1e636f7c-b858-4fb4-9e53-aee5fae77951

module
public import Definitions.Def_AddOns_Approximable
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_EntropyBounds
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_AddOns_Compact
public import Theorems.Thm_SNumbers_tendsto_entropyNumber_iff_totallyBounded
public import Theorems.Thm_SNumbers_tendsto_entropyNumber_of_isCompactOperator


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
theorem _root_.solution {S : X →L[𝕜] Y}
    (hS : IsCompactOperator S) :
    TotallyBounded (⇑S '' Metric.closedBall 0 1) :=
  (tendsto_entropyNumber_iff_totallyBounded S).mp
    (tendsto_entropyNumber_of_isCompactOperator hS)
end SNumbers
