-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.sg_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:31:44.506267+00:00
-- url     : https://prove2.me/submissions/3e5a62d7-11a0-4606-b54b-ccd91af3cafd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Lemmata_PeriodicFunctions_PeriodicApplyMulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumScaling
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_perm_range
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_add
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_mul
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_nat
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
theorem _root_.solution {a b : ℕ} {φ : E → K} (h : Good1 P a b φ) {w : E} (hw : UnitAt P w) :
    Good1 P a b (fun u => φ (w * u)) ∧ Sg P a b (fun u => φ (w * u)) = Sg P a b φ := by
  have hq0 := qE_ne P hp
  have qp : 0 < qOf P := hp.pos
  refine ⟨⟨fun u hu => ?_, fun u δ hδ => ?_⟩, ?_⟩
  · have h1 := h.1 _ hu
    have e : (qOf P : E) ^ a * u = w⁻¹ * ((qOf P : E) ^ a * (w * u)) := by
      field_simp [hw.1]
    rw [e]
    exact ia_mul P hw.2.2 h1
  · show φ (w * (u + δ)) = φ (w * u)
    rw [mul_add]
    apply h.2
    rw [mul_div_assoc]
    exact ia_mul P hw.2.1 hδ
  · obtain ⟨w0, hco, hw0⟩ := hN.2.2.2.2 E P hp hq w (a + b) hw.1 hw.2.1 hw.2.2
    set M := qOf P ^ (a + b) with hM
    have Mpos : 0 < M := pow_pos qp _
    unfold Sg
    rw [← hM]
    have key : ∀ i : ℕ, φ (w * ((i : E) / (qOf P : E) ^ a)) = φ ((((w0 * i) % M : ℕ) : E) / (qOf P : E) ^ a) := by
      intro i
      have hd := congrArg (Nat.cast (R := E)) (Nat.mod_add_div (w0 * i) M)
      have e : w * ((i : E) / (qOf P : E) ^ a) = (((w0 * i) % M : ℕ) : E) / (qOf P : E) ^ a +
          ((((w0 * i) / M : ℕ) : E) * (qOf P : E) ^ b + (w - w0) * (i : E) / (qOf P : E) ^ a) := by
        have hr : (((w0 * i) % M : ℕ) : E) = (w0 : E) * i - (qOf P : E) ^ (a + b) * (((w0 * i) / M : ℕ) : E) := by
          rw [hM] at hd
          push_cast at hd ⊢
          linear_combination hd
        rw [hr, pow_add]
        field_simp
        ring
      rw [e]
      apply h.2
      have e2 : ((((w0 * i) / M : ℕ) : E) * (qOf P : E) ^ b + (w - w0) * (i : E) / (qOf P : E) ^ a) / (qOf P : E) ^ b =
          (((w0 * i) / M : ℕ) : E) + (i : E) * ((w - w0) / (qOf P : E) ^ (a + b)) := by
        rw [pow_add]
        field_simp
      rw [e2]
      exact ia_add P (ia_nat P _) (ia_mul P (ia_nat P _) hw0)
    simp only [key]
    have hcoM : Nat.gcd M w0 = 1 := by
      rw [hM, Nat.gcd_comm]
      exact Nat.Coprime.pow_right _ hco
    exact perm_range M (fun i => (w0 * i) % M) (fun i _ => Nat.mod_lt _ Mpos)
      (fun i hi i' hi' hii => by
        have h3 : i % M = i' % M := Nat.ModEq.cancel_left_of_coprime hcoM hii
        rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at h3)
      (fun i => φ ((i : E) / (qOf P : E) ^ a))
end PI.TwistedEisensteinNonvanishing.W
