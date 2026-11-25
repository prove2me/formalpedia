-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeDimOfChowForm_proof_4902a506838c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:31:27.367807+00:00
-- url     : https://prove2.me/submissions/5e6d97e1-4b08-4b66-b15a-d4f7d2b88945

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PConeDimOfChowForm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsChowForm_incIdeal_eq_span_e2f6b622f525
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsProjPrime_not_isField_quotient_60522c54b766
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_exists_ringKrullDim_eq_trdeg
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
namespace ConeDimOfChowForm
theorem _root_.solution (h₁ : IncIdealDim.Statement) (h₂ : IncIdealPrime.Statement) :
    ConeDimOfChowForm.Statement := by
  intro F _ n k P f hP hf
  have hspan := hf.incIdeal_eq_span
  have hprime : (Ideal.span {f}).IsPrime := hspan ▸ h₂ F n k P hP.isPrime hP.isRelevant
  have hnu : ¬ IsUnit f := fun hu => hprime.ne_top (Ideal.span_singleton_eq_top.mpr hu)
  have hht : (Ideal.span {f}).height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hf.1) hnu
  have hdimS : ringKrullDim (MvPolynomial (Fin k × Fin n) F) = ((k * n : ℕ) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
      Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient F (Ideal.span {f})
  rw [hht, hdimS] at hform
  have := hP.isPrime
  obtain ⟨m, hm, -⟩ :=
    GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg (k := F) (A := MvPolynomial (Fin n) F ⧸ P)
  cases m with
  | zero =>
    exfalso
    have : Ring.KrullDimLE 0 (MvPolynomial (Fin n) F ⧸ P) := Ring.krullDimLE_iff.mpr (by rw [hm])
    exact hP.not_isField_quotient Ring.KrullDimLE.isField_of_isDomain
  | succ d =>
    have h := h₁ F n k d P hP hm
    rw [hspan] at h
    rw [h] at hform
    have h3 : ((1 + (k * n - k + min k d) : ℕ) : WithBot ℕ∞) = ((k * n : ℕ) : WithBot ℕ∞) := by
      rw [Nat.cast_add, Nat.cast_one]
      convert hform using 2
      exact WithBot.coe_one.symm
    replace h3 := Nat.cast_injective h3
    rw [hm]
    congr 1
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      omega
    · have hkn := Nat.le_mul_of_pos_right k hn
      generalize k * n = N at h3 hkn
      omega
end ConeDimOfChowForm
end GroundTheory.Heights₂.Heights
