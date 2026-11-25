-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.weighted_sum_scaling
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:52:16.980892+00:00
-- url     : https://prove2.me/submissions/01dae5e7-ee47-4989-b9c2-78cf1b6290d5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Lemmata_PeriodicFunctions_PeriodicApplyMulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumScaling
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_sg_unit
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_sg_qpow
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_sg_qinv
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qE_ne
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_vq_spec


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
theorem _root_.solution {d : E} (hd : d ≠ 0) (a b : ℕ) :
    ∃ a' b' : ℕ, ∀ φ : E → K, Good1 P a b φ →
      Good1 P a' b' (fun u => φ (d * u)) ∧ W1 P a' b' (fun u => φ (d * u)) = (qOf P : K) ^ vq P d * W1 P a b φ := by
  have hq0 := qE_ne P hp
  obtain ⟨w, hdw, hw⟩ := vq_spec hN hp hq hd
  rcases Int.eq_nat_or_neg (vq P d) with ⟨f, hf | hf⟩
  · refine ⟨a + f, b, fun φ h => ?_⟩
    have e : (fun u => φ (d * u)) = fun u => (fun u => φ ((qOf P : E) ^ f * u)) (w * u) := by
      funext u
      rw [hdw, hf, zpow_natCast, mul_assoc]
    obtain ⟨g1, s1⟩ := sg_qpow hN hp hq h f
    obtain ⟨g2, s2⟩ := sg_unit hN hp hq g1 hw
    rw [e]
    refine ⟨g2, ?_⟩
    unfold W1
    rw [s2, s1, hf, zpow_natCast]
    push_cast
    ring
  · refine ⟨a, b + f, fun φ h => ?_⟩
    have e : (fun u => φ (d * u)) = fun u => (fun u => φ (u / (qOf P : E) ^ f)) (w * u) := by
      funext u
      rw [hdw, hf, zpow_neg, zpow_natCast]
      congr 1
      field_simp
    obtain ⟨g1, s1⟩ := sg_qinv hN hp hq h f
    obtain ⟨g2, s2⟩ := sg_unit hN hp hq g1 hw
    rw [e]
    refine ⟨g2, ?_⟩
    unfold W1
    rw [s2, s1, hf, zpow_neg, zpow_natCast, pow_add]
    field_simp
end PI.TwistedEisensteinNonvanishing.W
