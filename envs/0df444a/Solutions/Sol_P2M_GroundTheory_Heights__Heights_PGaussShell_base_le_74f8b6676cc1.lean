-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PGaussShell_base_le_74f8b6676cc1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:46:01.668805+00:00
-- url     : https://prove2.me/submissions/e87f9ccd-ed6b-46de-822f-a94e1d69792c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussShell

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
open Real
noncomputable section
open GroundTheory.Heights₂.Heights.PGaussShell
namespace GroundTheory.Heights₂.Heights.PGaussShell
theorem _root_.solution (m δ : ℝ) (hm : 0 ≤ m) (hδ : 0 < δ) :
    1 + 2 * (m + 1) / δ ≤ 3 * (m + 1) * (1 + 1 / δ) := by
  have h2 : 3 * (m + 1) * (1 + 1 / δ) = 3 * (m + 1) + 3 * (m + 1) / δ := by ring
  have h1 : 2 * (m + 1) / δ ≤ 3 * (m + 1) / δ :=
    div_le_div_of_nonneg_right (by linarith) hδ.le
  linarith
end GroundTheory.Heights₂.Heights.PGaussShell
