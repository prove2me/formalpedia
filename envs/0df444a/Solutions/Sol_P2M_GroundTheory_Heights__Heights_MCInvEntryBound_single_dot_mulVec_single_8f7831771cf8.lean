-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCInvEntryBound_single_dot_mulVec_single_8f7831771cf8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:11.621978+00:00
-- url     : https://prove2.me/submissions/ed81a5c4-38c9-442d-917d-2fa749b2bcac

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PInvEntryBound

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
open Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.MCInvEntryBound
namespace GroundTheory.Heights₂.Heights.MCInvEntryBound
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (j l : ι) : Pi.single j (1 : ℝ) ⬝ᵥ (A *ᵥ Pi.single l 1) = A j l := by
  simp [mulVec_single, single_dotProduct]
end GroundTheory.Heights₂.Heights.MCInvEntryBound
