-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ofPositionAdditive_apply_bf8ee1efc0e4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:56:28.374296+00:00
-- url     : https://prove2.me/submissions/17a81f27-bdd8-4d6c-8881-f83813596e0f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {K : Type*} [Fintype K] [DecidableEq K]
omit [Fintype K] [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution {n : ℕ} (L : (Fin n → K → ℤ) → ℤ) (hadd) (m : Fin n → K → ℤ) :
    ofPositionAdditive L hadd m = L m := rfl
end GroundTheory.Heights₂.Heights.HilbertSamuel
