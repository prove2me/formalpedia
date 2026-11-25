-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.sg_qinv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:43:03.786618+00:00
-- url     : https://prove2.me/submissions/d12abd8a-e8bd-4a2d-b23d-687d5441b76b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Lemmata_PeriodicFunctions_PeriodicApplyMulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumScaling
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_sg_stab
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_mul
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_qpow
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qE_ne


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
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {a b : ℕ} {φ : E → K} (h : Good1 P a b φ) (f : ℕ) :
    Good1 P a (b + f) (fun u => φ (u / (qOf P : E) ^ f)) ∧
      Sg P a (b + f) (fun u => φ (u / (qOf P : E) ^ f)) = Sg P a b φ := by
  have hq0 := qE_ne P hp
  refine ⟨⟨fun u hu => ?_, fun u δ hδ => ?_⟩, ?_⟩
  · have h1 := h.1 _ hu
    have e : (qOf P : E) ^ a * u = (qOf P : E) ^ f * ((qOf P : E) ^ a * (u / (qOf P : E) ^ f)) := by
      field_simp
    rw [e]
    exact ia_mul P (ia_qpow P _) h1
  · show φ ((u + δ) / (qOf P : E) ^ f) = φ (u / (qOf P : E) ^ f)
    rw [add_div]
    apply h.2
    have e : δ / (qOf P : E) ^ f / (qOf P : E) ^ b = δ / (qOf P : E) ^ (b + f) := by
      rw [pow_add]
      field_simp
    rw [e]
    exact hδ
  · have e : Sg P a (b + f) (fun u => φ (u / (qOf P : E) ^ f)) = Sg P (a + f) b φ := by
      unfold Sg
      rw [show a + (b + f) = a + f + b by ring]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      rw [pow_add]
      field_simp
    rw [e, sg_stab hN hp hq (Nat.le_add_right a f) le_rfl h, Nat.sub_self, pow_zero, Nat.cast_one, one_mul]
end PI.TwistedEisensteinNonvanishing.W
