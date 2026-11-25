-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KThetaCubeParseval_continuous_torusChar_a506262f8410
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:01:34.192566+00:00
-- url     : https://prove2.me/submissions/a8181e4c-df23-4c36-b88b-b0e520ee4669

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
theorem _root_.solution {g : ℕ} (m : Fin g → ℤ) : Continuous (torusChar m) := by
  unfold torusChar
  fun_prop
end GroundTheory.Heights₂.Heights.KThetaCubeParseval
