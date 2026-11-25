-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCInvEntryDeriv_inv_entry_eq_c0f1905f6b53
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:18:23.014656+00:00
-- url     : https://prove2.me/submissions/13c1b9ae-8185-492e-ba27-cd3ea1020344

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PInvEntryDeriv

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
open Matrix Topology
open GroundTheory.Heights₂.Heights.MCInvEntryDeriv
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : ℕ}
namespace GroundTheory.Heights₂.Heights.MCInvEntryDeriv
theorem _root_.solution (A : Matrix (Fin g) (Fin g) ℝ) (j l : Fin g) :
    A⁻¹ j l = (A.det)⁻¹ * (A.updateRow l (Pi.single j 1)).det := by
  rw [inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, adjugate_apply]
end GroundTheory.Heights₂.Heights.MCInvEntryDeriv
