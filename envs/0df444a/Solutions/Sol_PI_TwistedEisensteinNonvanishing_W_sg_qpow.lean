-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.sg_qpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:43:07.996551+00:00
-- url     : https://prove2.me/submissions/de01310c-351c-4e69-a9b0-d37ee12deaa4

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
    Good1 P (a + f) b (fun u => φ ((qOf P : E) ^ f * u)) ∧
      Sg P (a + f) b (fun u => φ ((qOf P : E) ^ f * u)) = ((qOf P ^ f : ℕ) : K) * Sg P a b φ := by
  have hq0 := qE_ne P hp
  refine ⟨⟨fun u hu => ?_, fun u δ hδ => ?_⟩, ?_⟩
  · have h1 := h.1 _ hu
    rw [pow_add, mul_assoc]
    exact h1
  · show φ ((qOf P : E) ^ f * (u + δ)) = φ ((qOf P : E) ^ f * u)
    rw [mul_add]
    apply h.2
    rw [mul_div_assoc]
    exact ia_mul P (ia_qpow P _) hδ
  · have e : Sg P (a + f) b (fun u => φ ((qOf P : E) ^ f * u)) = Sg P a (b + f) φ := by
      unfold Sg
      rw [show a + f + b = a + (b + f) by ring]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      rw [pow_add]
      field_simp
    rw [e, sg_stab hN hp hq le_rfl (Nat.le_add_right b f) h, Nat.add_sub_cancel_left]
end PI.TwistedEisensteinNonvanishing.W
