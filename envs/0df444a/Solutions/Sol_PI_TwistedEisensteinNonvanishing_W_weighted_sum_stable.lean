-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.weighted_sum_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:42:08.798649+00:00
-- url     : https://prove2.me/submissions/ca35798f-4134-40e3-90e9-ebabab3ead7a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Lemmata_PeriodicFunctions_PeriodicApplyMulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumScaling
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_sg_stab

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
open Loc LocE
variable {E K : Type} [Field E] [NumberField E] [Field K]
variable {P : HeightOneSpectrum (𝓞 E)}
variable (hN : NTAll) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hK : ((qOf P : ℕ) : K) ≠ 0)
include hN hp hq
include hK
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {a b A B : ℕ} (hA : a ≤ A) (hB : b ≤ B) {φ : E → K} (h : Good1 P a b φ) :
    W1 P A B φ = W1 P a b φ := by
  unfold W1
  rw [sg_stab hN hp hq hA hB h]
  push_cast
  have e : (qOf P : K) ^ B = (qOf P : K) ^ (B - b) * (qOf P : K) ^ b := by
    rw [← pow_add, Nat.sub_add_cancel hB]
  rw [e]
  field_simp
end PI.TwistedEisensteinNonvanishing.W
