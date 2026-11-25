-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KThetaCubeParseval_norm_torusChar_5b8d1269a090
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:01:16.756462+00:00
-- url     : https://prove2.me/submissions/1f7a7b10-8c1f-4353-a17c-02b7be8d8689

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsTheta
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PThetaCubeParseval
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KThetaCubeParseval_torusChar_eq_8a9d063e55cf

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
theorem _root_.solution {g : ℕ} (m : Fin g → ℤ) (u : Fin g → ℝ) : ‖torusChar m u‖ = 1 := by
  rw [torusChar_eq, Complex.norm_exp_ofReal_mul_I]
end GroundTheory.Heights₂.Heights.KThetaCubeParseval
