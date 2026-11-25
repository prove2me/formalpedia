-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KThetaCubeParseval_measureReal_cube_c63ba2eef981
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:01:14.83448+00:00
-- url     : https://prove2.me/submissions/3bb074f2-1fc3-4781-873f-c3c8bbf2d420

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsTheta
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PThetaCubeParseval

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
open MeasureTheory Real ComplexConjugate
noncomputable section
open GroundTheory.Heights₂.Heights.KThetaCubeParseval
namespace GroundTheory.Heights₂.Heights.KThetaCubeParseval
theorem _root_.solution (g : ℕ) :
    (volume.restrict (Set.Icc (0 : Fin g → ℝ) 1)).real Set.univ = 1 := by
  simp [Measure.real, Real.volume_Icc_pi]
end GroundTheory.Heights₂.Heights.KThetaCubeParseval
