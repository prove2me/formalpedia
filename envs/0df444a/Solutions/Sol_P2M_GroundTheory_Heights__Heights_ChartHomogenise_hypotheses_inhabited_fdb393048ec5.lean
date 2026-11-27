-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartHomogenise_hypotheses_inhabited_fdb393048ec5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:53:50.449726+00:00
-- url     : https://prove2.me/submissions/cb05c0a8-111d-484d-9c26-a6fff198432c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartMax
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linForm_tLine_1098a18ec0be


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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ChartHomogenise
theorem _root_.solution :
    pointIdealZeroOne.IsPrime ∧ linForm tLine - 1 ∈ pointIdealZeroOne := by
  refine ⟨RingHom.ker_isPrime _, ?_⟩
  rw [pointIdealZeroOne, RingHom.mem_ker, linForm_tLine]
  simp
end ChartHomogenise
end GroundTheory.Heights₂.Heights
