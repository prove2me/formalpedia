-- Prove2me | solution 1 for Reformulated.AutPerF.dvd_of_pow_succ_dvd_smul_dp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:02:03.606584+00:00
-- url     : https://prove2.me/submissions/33beeb5e-cce5-485a-9c37-63d228329aca

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Envelope
import Theorems.Thm_Reformulated_AutPerF_factorial_mul_dp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal
open scoped Nat
open Reformulated Reformulated.AutPerF
variable {B : Type*} [CommRing B] [Algebra ℚ B]
variable {A : Type*} [CommRing A] [Algebra A B]
variable {ξ : A}
variable [IsDomain B] (h0 : algebraMap A B ξ ≠ 0)
  (hξ : ∀ a : A, algebraMap A B ξ ∣ algebraMap A B a → ξ ∣ a)
include h0 hξ
namespace Reformulated.AutPerF
theorem _root_.solution {m : ℕ} {a : A}
    (h : algebraMap A B ξ ^ (m + 1) ∣ a • dp m (algebraMap A B ξ)) : ξ ∣ a := by
  have h1 := h.mul_left (m ! : B)
  rw [Algebra.smul_def, mul_left_comm, factorial_mul_dp, pow_succ'] at h1
  exact hξ a ((mul_dvd_mul_iff_right (pow_ne_zero m h0)).1 h1)
end Reformulated.AutPerF
