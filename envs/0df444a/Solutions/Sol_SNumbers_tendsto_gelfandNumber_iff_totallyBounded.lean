-- Prove2me | solution 1 for SNumbers.tendsto_gelfandNumber_iff_totallyBounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:55:11.942437+00:00
-- url     : https://prove2.me/submissions/cd830977-6b39-41c2-a031-70e020447b43

module
public import Definitions.Def_AddOns_Approximable
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_EntropyBounds
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_AddOns_Compact
public import Theorems.Thm_SNumbers_tendsto_gelfandNumber_of_totallyBounded
public import Theorems.Thm_SNumbers_totallyBounded_of_tendsto_gelfandNumber

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
theorem _root_.solution (S : X →L[𝕜] Y) :
    Tendsto (gelfandNumber S) atTop (𝓝 0) ↔
      TotallyBounded (⇑S '' Metric.closedBall 0 1) :=
  ⟨totallyBounded_of_tendsto_gelfandNumber, tendsto_gelfandNumber_of_totallyBounded⟩
end SNumbers
