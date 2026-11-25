-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplMinkowskiBox_volume_fundamentalDomain_basisFun_562ffd935c98
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:46:08.509521+00:00
-- url     : https://prove2.me/submissions/559f73b5-6835-48b2-9bb6-03e2f106eb49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplMinkowskiBox

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
open Matrix MeasureTheory
open GroundTheory.Heights₂.Heights.PSymplMinkowskiBox
namespace GroundTheory.Heights₂.Heights.PSymplMinkowskiBox
theorem _root_.solution (ι : Type) [Fintype ι] :
    volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ ι)) = 1 := by
  rw [ZSpan.fundamentalDomain_pi_basisFun, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ico]
end GroundTheory.Heights₂.Heights.PSymplMinkowskiBox
