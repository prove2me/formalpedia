-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_PeriodPolydisc_tau_shifted_transpose_3683cff9c7b5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:49:00.91792+00:00
-- url     : https://prove2.me/submissions/cb9264dd-9956-454d-8f4b-598f188729ae

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PosSemidefOfIntQuadNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Matrix Topology Filter
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.PeriodPolydisc
variable {n a g : ℕ} (P : PeriodPolydisc n a g)
namespace GroundTheory.Heights₂.Heights.Regular.PeriodPolydisc
theorem _root_.solution {w : Fin n → ℂ} (hw : w ∈ logCover P.a_le) : (P.tau0 w)ᵀ = P.tau0 w := by
  simp only [tau0, transpose_sub, transpose_sum, transpose_smul, ← transpose_map, P.B_symm,
    P.symm w hw]
end GroundTheory.Heights₂.Heights.Regular.PeriodPolydisc
