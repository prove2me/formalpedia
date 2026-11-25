-- Prove2me | solution 1 for SNumbers.isCompactOperator_iff_tendsto_entropyNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:42:55.240236+00:00
-- url     : https://prove2.me/submissions/7578a863-f17d-4190-941d-a827f0524df6

module
public import Definitions.Def_SNumbers_Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_Entropy
public import Theorems.Thm_SNumbers_tendsto_entropyNumber_of_isCompactOperator
public import Theorems.Thm_SNumbers_isCompactOperator_of_tendsto_entropyNumber

set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {X Y Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SNumbers
theorem _root_.solution [CompleteSpace Y]
    (S : X →L[𝕜] Y) :
    IsCompactOperator S ↔ Tendsto (entropyNumber S) atTop (𝓝 0) :=
  ⟨tendsto_entropyNumber_of_isCompactOperator, isCompactOperator_of_tendsto_entropyNumber⟩
end SNumbers
