-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_degLT_zero_8822dfd84ef9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:13.377924+00:00
-- url     : https://prove2.me/submissions/f84d3a57-25c0-4a64-988c-f6e37a1d44f9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_mixedDiff_zero_4b76ed212846

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {K : Type*} (n : ℕ) : DegLT (0 : (K → ℤ) → ℤ) n := fun bs =>
  Filter.Eventually.of_forall fun m => by rw [mixedDiff_zero]; rfl
end GroundTheory.Heights₂.Heights.NumbersDVR
