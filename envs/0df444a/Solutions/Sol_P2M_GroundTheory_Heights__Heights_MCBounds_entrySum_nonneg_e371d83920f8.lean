-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCBounds_entrySum_nonneg_e371d83920f8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:27.060957+00:00
-- url     : https://prove2.me/submissions/ce7f6c6d-8c28-41f4-858e-ca96c02566bd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCBounds
open Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.MCBounds
theorem _root_.solution {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) : 0 ≤ entrySum A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
end GroundTheory.Heights₂.Heights.MCBounds
