-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowFormExists_proof_9f7a68bbdf98
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:16:15.9668+00:00
-- url     : https://prove2.me/submissions/85526ae7-9231-4c80-a9a0-ead401de0773

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormExists
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_one_le_of_isProjPrime_d1887d63bb03
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_height_add_ringKrullDim_quotient


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace ChowFormExists
theorem _root_.solution (h₁ : IncIdealDim.Statement) (h₂ : IncIdealPrime.Statement) :
    ChowFormExists.Statement := by
  intro F _ n k P hP hdim
  have hk : 1 ≤ k := one_le_of_isProjPrime hP hdim
  obtain ⟨j, -⟩ := hP.isRelevant
  have hn : 0 < n := j.pos
  have hQ : (incIdeal P k).IsPrime := h₂ F n k P hP.isPrime hP.isRelevant
  have hdimQ := h₁ F n k (k - 1) P hP (by rw [Nat.sub_add_cancel hk]; exact hdim)
  have hS : ringKrullDim (MvPolynomial (Fin k × Fin n) F) = ((k * n : ℕ) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, zero_add]
  have hsum := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient F (incIdeal P k)
  rw [hdimQ, hS] at hsum
  have hkn : k ≤ k * n := Nat.le_mul_of_pos_right k hn
  obtain ⟨m, hm1, hm2⟩ : ∃ m, k * n - k + min k (k - 1) = m ∧ m + 1 = k * n :=
    ⟨_, rfl, by generalize k * n = N at hkn ⊢; omega⟩
  rw [hm1, ← hm2] at hsum
  have hht : (incIdeal P k).height = 1 := by
    generalize (incIdeal P k).height = h at hsum
    have h' : (h + m : ℕ∞) = ((m + 1 : ℕ) : ℕ∞) := by
      have : ((h + m : ℕ∞) : WithBot ℕ∞) = (((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        push_cast at hsum ⊢
        exact hsum
      exact_mod_cast this
    induction h using ENat.recTopCoe with
    | top => exact (ENat.natCast_ne_top (m + 1) h'.symm).elim
    | coe a =>
      norm_cast at h' ⊢
      omega
  have hne : incIdeal P k ≠ ⊥ := Ideal.ne_bot_of_height_eq_one hht
  obtain ⟨g, hgmem, hgp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot hQ hne
  have hspan := Ideal.eq_span_singleton_of_height_eq_one hht hgmem hgp
  refine ⟨g, hgp.ne_zero, fun f => ?_⟩
  rw [← Ideal.mem_span_singleton, ← hspan]
  simp only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker]
end ChowFormExists
end GroundTheory.Heights₂.Heights
