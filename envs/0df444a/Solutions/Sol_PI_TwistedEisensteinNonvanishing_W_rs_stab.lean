-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.rs_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:52:12.108805+00:00
-- url     : https://prove2.me/submissions/4c2e4af9-17f5-4467-96b1-d8f5911f61b2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumScaling
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_SumSliceEq
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_sum_stab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE Function
variable {E K : Type} [Field E] [NumberField E] [Field K]
variable {P : HeightOneSpectrum (𝓞 E)} (hN : NTAll) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hK : ((qOf P : ℕ) : K) ≠ 0)
include hN hp hq
include hK
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {a b A B : ℕ} (hA : a ≤ A) (hB : b ≤ B)
    {H : (ι → E) → K} (hH : Good P a b H) : RS P A B H = RS P a b H := by
  unfold RS
  rw [sum_stab hN hp hq hA hB hH, ← mul_assoc, ← mul_pow]
  congr 2
  push_cast
  have hqb : ((qOf P : K)) ^ B = (qOf P : K) ^ b * (qOf P : K) ^ (B - b) := by
    rw [← pow_add, Nat.add_sub_cancel' hB]
  rw [hqb, mul_inv, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hK), mul_one]
end PI.TwistedEisensteinNonvanishing.W
