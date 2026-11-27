-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCPeriod_schurQuotientPeriod_59dd4f7c80ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:03:19.190048+00:00
-- url     : https://prove2.me/submissions/63dbb47d-9f65-4a09-adad-1708c95e9e6b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Period

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCPeriod
open Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.MCPeriod
theorem _root_.solution : SchurQuotientPeriod.Statement := by
  intro r s τ hs hp
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    have := congrFun (congrFun hs (Sum.inr i)) (Sum.inr j)
    simpa [Matrix.toBlocks₂₂] using this
  · ext i j
    simp [Matrix.toBlocks₂₂]
  · have : (τ.toBlocks₂₂).map Complex.im = (τ.map Complex.im).submatrix Sum.inr Sum.inr := by
      ext i j
      simp [Matrix.toBlocks₂₂]
    rw [this]
    exact hp.submatrix Sum.inr_injective
end GroundTheory.Heights₂.Heights.MCPeriod
