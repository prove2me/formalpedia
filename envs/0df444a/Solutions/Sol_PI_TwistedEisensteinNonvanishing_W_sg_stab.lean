-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.sg_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:38:15.861291+00:00
-- url     : https://prove2.me/submissions/792a6ea2-b73a-448d-8018-fe0ffa629ac7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Lemmata_PeriodicFunctions_PeriodicApplyMulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumScaling
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_sum_range_mul
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_one
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
theorem _root_.solution {a b A B : ℕ} (hA : a ≤ A) (hB : b ≤ B) {φ : E → K} (h : Good1 P a b φ) :
    Sg P A B φ = ((qOf P ^ (B - b) : ℕ) : K) * Sg P a b φ := by
  have hq0 := qE_ne P hp
  have qp : 0 < qOf P := hp.pos

  have s1 : Sg P A B φ = ∑ i ∈ Finset.range (qOf P ^ (a + B)), φ ((i : E) / (qOf P : E) ^ a) := by
    unfold Sg
    have hI : Set.InjOn (fun i : ℕ => qOf P ^ (A - a) * i) (Finset.range (qOf P ^ (a + B)) : Set ℕ) :=
      fun i _ j _ h => Nat.eq_of_mul_eq_mul_left (pow_pos qp _) h
    have hsub : (Finset.range (qOf P ^ (a + B))).image (fun i : ℕ => qOf P ^ (A - a) * i) ⊆
        Finset.range (qOf P ^ (A + B)) := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
      rw [Finset.mem_range] at hi ⊢
      have : A + B = (A - a) + (a + B) := by omega
      rw [this, pow_add]
      exact Nat.mul_lt_mul_of_pos_left hi (pow_pos qp _)
    rw [← Finset.sum_subset hsub, Finset.sum_image hI]
    · refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      push_cast
      have : (qOf P : E) ^ A = (qOf P : E) ^ (A - a) * (qOf P : E) ^ a := by
        rw [← pow_add, Nat.sub_add_cancel hA]
      rw [this]
      field_simp
    · intro i hi hni
      by_contra hne
      have h1 := h.1 _ hne
      have e : (qOf P : E) ^ a * ((i : E) / (qOf P : E) ^ A) = (i : E) / (qOf P : E) ^ (A - a) := by
        have : (qOf P : E) ^ A = (qOf P : E) ^ (A - a) * (qOf P : E) ^ a := by
          rw [← pow_add, Nat.sub_add_cancel hA]
        rw [this]
        field_simp
      rw [e, hN.1 E P hp hq] at h1
      obtain ⟨i', rfl⟩ := h1
      apply hni
      refine Finset.mem_image.2 ⟨i', Finset.mem_range.2 ?_, rfl⟩
      have hi' := Finset.mem_range.1 hi
      have : A + B = (A - a) + (a + B) := by omega
      rw [this, pow_add] at hi'
      exact Nat.lt_of_mul_lt_mul_left hi'

  rw [s1]
  have e2 : qOf P ^ (a + B) = qOf P ^ (a + b) * qOf P ^ (B - b) := by
    rw [← pow_add]
    congr 1
    omega
  rw [e2, sum_range_mul]
  · rfl
  · intro i
    have e3 : (((i + qOf P ^ (a + b) : ℕ) : E) / (qOf P : E) ^ a) = (i : E) / (qOf P : E) ^ a + (qOf P : E) ^ b := by
      push_cast
      rw [pow_add]
      field_simp
    rw [e3]
    apply h.2
    rw [div_self (pow_ne_zero _ hq0)]
    exact ia_one P
end PI.TwistedEisensteinNonvanishing.W
