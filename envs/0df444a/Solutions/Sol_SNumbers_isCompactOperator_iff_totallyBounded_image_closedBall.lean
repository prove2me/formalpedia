-- Prove2me | solution 1 for SNumbers.isCompactOperator_iff_totallyBounded_image_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:51:53.429346+00:00
-- url     : https://prove2.me/submissions/64b929e5-456a-4370-b44f-81b0253ab742

module
public import Definitions.Def_AddOns_Approximable
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_EntropyBounds
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_AddOns_Compact
public import Theorems.Thm_SNumbers_totallyBounded_image_closedBall_of_isCompactOperator
public import Theorems.Thm_SNumbers_isCompactOperator_of_totallyBounded_image_closedBall

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
    (S : X →L[𝕜] Y) :
    IsCompactOperator S ↔ TotallyBounded (⇑S '' Metric.closedBall 0 1) :=
  ⟨totallyBounded_image_closedBall_of_isCompactOperator,
    isCompactOperator_of_totallyBounded_image_closedBall⟩
end SNumbers
