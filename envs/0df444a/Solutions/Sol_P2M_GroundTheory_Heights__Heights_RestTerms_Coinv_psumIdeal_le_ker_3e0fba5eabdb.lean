-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_psumIdeal_le_ker_3e0fba5eabdb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:50:26.746564+00:00
-- url     : https://prove2.me/submissions/a73f63ca-9ed4-475e-9f86-f8c6d22e4d79

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoinvReduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Coinv
open MvPolynomial Finset
noncomputable section
variable (K : Type*) [Field K] (f n : ℕ)
variable {K f n}
variable [CharZero K]
variable (K)
omit [CharZero K]
namespace GroundTheory.Heights₂.Heights.RestTerms.Coinv
theorem _root_.solution :
    psumIdeal K f n ≤ RingHom.ker (constantCoeff : MvPolynomial (Fin f × Fin n) K →+* K) := by
  refine Ideal.span_le.mpr ?_
  rintro P ⟨m, b, h1, -, rfl⟩
  simp [bps, constantCoeff_X, zero_pow (show m ≠ 0 by omega)]
end GroundTheory.Heights₂.Heights.RestTerms.Coinv
