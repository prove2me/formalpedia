-- Prove2me | solution 1 for SNumbers.isCompactOperator_iff_tendsto_gelfandNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:55:23.535784+00:00
-- url     : https://prove2.me/submissions/6ab6ebb9-5ed9-4c72-ba8b-fb5c0efd8acc

module
public import Definitions.Def_AddOns_Approximable
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_EntropyBounds
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_AddOns_Compact
public import Theorems.Thm_SNumbers_tendsto_gelfandNumber_of_isCompactOperator
public import Theorems.Thm_SNumbers_isCompactOperator_of_tendsto_gelfandNumber

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
    (S : X →L[𝕜] Y) :
    IsCompactOperator S ↔ Tendsto (gelfandNumber S) atTop (𝓝 0) :=
  ⟨tendsto_gelfandNumber_of_isCompactOperator,
    isCompactOperator_of_tendsto_gelfandNumber⟩
end SNumbers
