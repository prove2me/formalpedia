-- Prove2me | solution 1 for SNumbers.isCompactOperator_iff_tendsto_kolmogorovNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:55:06.187253+00:00
-- url     : https://prove2.me/submissions/bfdd5e4e-6d25-481d-b8cd-195bbbdb8f8b

module
public import Definitions.Def_AddOns_Approximable
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_EntropyBounds
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_AddOns_Compact
public import Theorems.Thm_SNumbers_tendsto_kolmogorovNumber_of_isCompactOperator
public import Theorems.Thm_SNumbers_isCompactOperator_of_tendsto_kolmogorovNumber

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
    IsCompactOperator S ↔ Tendsto (kolmogorovNumber S) atTop (𝓝 0) :=
  ⟨tendsto_kolmogorovNumber_of_isCompactOperator,
    isCompactOperator_of_tendsto_kolmogorovNumber⟩
end SNumbers
