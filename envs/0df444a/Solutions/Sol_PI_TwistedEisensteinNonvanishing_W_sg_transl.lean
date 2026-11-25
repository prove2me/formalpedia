-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.sg_transl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:31:40.634689+00:00
-- url     : https://prove2.me/submissions/b597bffd-5018-42fd-bc65-d8e557f6131b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Lemmata_PeriodicFunctions_PeriodicApplyMulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumScaling
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_perm_range
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_add
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_nat
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_sub
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
theorem _root_.solution {a b : ℕ} {φ : E → K} (h : Good1 P a b φ) {β : E} (hβ : IntAt P ((qOf P : E) ^ a * β)) :
    Good1 P a b (fun u => φ (u + β)) ∧ Sg P a b (fun u => φ (u + β)) = Sg P a b φ := by
  have hq0 := qE_ne P hp
  have qp : 0 < qOf P := hp.pos
  refine ⟨⟨fun u hu => ?_, fun u δ hδ => ?_⟩, ?_⟩
  · have h1 := h.1 _ hu
    have e : (qOf P : E) ^ a * u = (qOf P : E) ^ a * (u + β) - (qOf P : E) ^ a * β := by ring
    rw [e]
    exact ia_sub P h1 hβ
  · show φ (u + δ + β) = φ (u + β)
    rw [add_right_comm]
    exact h.2 _ _ hδ
  · obtain ⟨j, -, hj⟩ := hN.2.1 E P hp hq _ (a + b) hβ
    set M := qOf P ^ (a + b) with hM
    have Mpos : 0 < M := pow_pos qp _
    unfold Sg
    rw [← hM]
    have key : ∀ i : ℕ, φ ((i : E) / (qOf P : E) ^ a + β) = φ ((((i + j) % M : ℕ) : E) / (qOf P : E) ^ a) := by
      intro i
      have hd := congrArg (Nat.cast (R := E)) (Nat.mod_add_div (i + j) M)
      push_cast at hd
      have e : (i : E) / (qOf P : E) ^ a + β = (((i + j) % M : ℕ) : E) / (qOf P : E) ^ a +
          ((((i + j) / M : ℕ) : E) * (qOf P : E) ^ b + (β - (j : E) / (qOf P : E) ^ a)) := by
        have hr : (((i + j) % M : ℕ) : E) = (i : E) + j - (qOf P : E) ^ (a + b) * (((i + j) / M : ℕ) : E) := by
          rw [hM] at hd
          push_cast at hd ⊢
          linear_combination hd
        rw [hr, pow_add]
        field_simp
        ring
      rw [e]
      apply h.2
      have e2 : ((((i + j) / M : ℕ) : E) * (qOf P : E) ^ b + (β - (j : E) / (qOf P : E) ^ a)) / (qOf P : E) ^ b =
          (((i + j) / M : ℕ) : E) + ((qOf P : E) ^ a * β - j) / (qOf P : E) ^ (a + b) := by
        rw [pow_add]
        field_simp
      rw [e2]
      exact ia_add P (ia_nat P _) hj
    simp only [key]
    exact perm_range M (fun i => (i + j) % M) (fun i _ => Nat.mod_lt _ Mpos)
      (fun i hi i' hi' hii => by
        have h3 : i % M = i' % M := Nat.ModEq.add_right_cancel' j hii
        rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at h3)
      (fun i => φ ((i : E) / (qOf P : E) ^ a))
end PI.TwistedEisensteinNonvanishing.W
