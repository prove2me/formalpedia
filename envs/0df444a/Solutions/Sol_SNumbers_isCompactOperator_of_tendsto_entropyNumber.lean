-- Prove2me | solution 1 for SNumbers.isCompactOperator_of_tendsto_entropyNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:54:50.008595+00:00
-- url     : https://prove2.me/submissions/6308bcf5-3e7b-4769-8cae-24f060099770

module
public import Definitions.Def_SNumbers_Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_Entropy
public import Theorems.Thm_SNumbers_tendsto_entropyNumber_iff_totallyBounded

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
    {S : X →L[𝕜] Y} (hS : Tendsto (entropyNumber S) atTop (𝓝 0)) :
    IsCompactOperator S :=
  (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image ⇑S).mpr
    ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds 0 one_pos,
      ((tendsto_entropyNumber_iff_totallyBounded S).mp hS).closure.isCompact_of_isClosed
        isClosed_closure⟩
end SNumbers
