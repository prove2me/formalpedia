-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LinesIsLattice_proof_02d454bfaf2d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:24.723013+00:00
-- url     : https://prove2.me/submissions/63e242d4-8353-499a-b096-c1f4bab1953e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesIsLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField
namespace GroundTheory.Heights₂.Heights
namespace LinesIsLattice
theorem _root_.solution : LinesIsLattice.Statement := by
  intro K _ _ ι _ M hfg hspan
  refine ⟨hfg, ?_⟩
  have hMN : Submodule.span K (M : Set (ι → K)) ≤ KLinesIsLattice.qSpan M :=
    Submodule.span_le.mpr fun v hv => Submodule.subset_span hv
  rw [hspan, top_le_iff] at hMN
  rw [eq_top_iff]
  intro v _
  have hv : v ∈ KLinesIsLattice.qSpan M := hMN ▸ Submodule.mem_top
  exact hv
end LinesIsLattice
end GroundTheory.Heights₂.Heights
