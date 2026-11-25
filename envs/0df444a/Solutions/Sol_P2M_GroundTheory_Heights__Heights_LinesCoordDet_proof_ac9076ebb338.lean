-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LinesCoordDet_proof_ac9076ebb338
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:21:56.429077+00:00
-- url     : https://prove2.me/submissions/eecb4087-832c-45c0-a1b2-62316f65b550

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesCoordDet
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesCoordDet_det_eq_89a8912c4c84
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesCoordDet_det_ne_zero_d33450b39a0d

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
namespace GroundTheory.Heights₂.Heights
namespace LinesCoordDet
theorem _root_.solution : LinesCoordDet.Statement := by
  intro K _ n m k B b c hb hli
  exact ⟨KLinesCoordDet.det_eq B b c hb,
    KLinesCoordDet.det_eq B b c hb ▸ KLinesCoordDet.det_ne_zero B b c hli⟩
end LinesCoordDet
end GroundTheory.Heights₂.Heights
