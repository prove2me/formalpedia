-- Prove2me | solution 1 for P2M_GlobalTheory_ExistsNatMulIsIntegral__exists_nat_mul_isIntegral_373366b61ebd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:31:49.328708+00:00
-- url     : https://prove2.me/submissions/947c4c9b-345d-48c4-b58c-25c701ba8b78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsNatMulIsIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ExistsNatMulIsIntegral₂
open NumberField
namespace GlobalTheory.ExistsNatMulIsIntegral₂
theorem _root_.solution {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * c) := by
  have halg : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg y
  · simpa using hint
  · simpa using hint.neg
end GlobalTheory.ExistsNatMulIsIntegral₂
