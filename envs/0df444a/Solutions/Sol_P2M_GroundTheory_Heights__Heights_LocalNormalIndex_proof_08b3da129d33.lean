-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LocalNormalIndex_proof_08b3da129d33
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:04:30.024162+00:00
-- url     : https://prove2.me/submissions/67566398-e379-4056-8c7a-eef7d109dc82

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightLocalNormalIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PLocalQuotCard
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PLocalQuotCentred
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartResidue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteIntegralClosureCharZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PLocalNormalIndex
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalQuotCard_proof_7bdafcd4f747
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalQuotCentred_proof_5c3e45083b88
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_finite_integralClosure_fractionRing_of_charZero_ff051fc57786
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartResidue_proof_28fdecb34b79
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SubringPrimeMaximal_proof_6f25c325f70e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_card_quot_span_eq_relIndex_7d79e126b957
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_natCard_eq_pow_length_of_finiteType_f3a3739dc0cd


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
open NumberField
namespace GroundTheory.Heights₂.Heights
namespace LocalNormalIndex
theorem _root_.solution : LocalNormalIndex.Statement := by
  intro L _ _ O hft hfr m _
  set A := Localization.subalgebra.ofField L m.primeCompl m.primeCompl_le_nonZeroDivisors
  set C := integralClosure A L
  have : Algebra.FiniteType ℤ O := hft
  have : CharZero O := ⟨fun a b h ↦ by
    have := congrArg (fun t : O ↦ (t : L)) h
    simpa using this⟩

  have hfin : Module.Finite O (integralClosure O L) :=
    Model.finite_integralClosure_fractionRing_of_charZero O L
  obtain ⟨d, hd, hdI⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors O)
    (Module.Finite.iff_fg.mp hfin : (Subalgebra.toSubmodule (integralClosure O L)).FG)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hdL : algebraMap O L d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd

  have hdC : ∀ x ∈ C, algebraMap O L d * x ∈ A := by
    intro x hx
    obtain ⟨⟨s, hs⟩, hsx⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (R := O) (M := m.primeCompl) (Rₘ := A) x hx
    obtain ⟨o, ho⟩ := hdI _ hsx
    have hs0 : algebraMap O L s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (m.primeCompl_le_nonZeroDivisors hs)
    simp only [Submonoid.smul_def, Algebra.smul_def] at ho
    refine ⟨o, s, hs, ?_⟩
    rw [ho]
    field_simp

  have hAC : A.toSubring ≤ C.toSubring := fun x hx ↦
    (isIntegral_algebraMap : IsIntegral A (algebraMap A L ⟨x, hx⟩))
  set f := algebraMap O L d
  have hinj : Function.Injective (AddMonoidHom.mulLeft f) := mul_right_injective₀ hdL
  have h1 : A.toSubring.toAddSubgroup.map (AddMonoidHom.mulLeft f) ≤
      C.toSubring.toAddSubgroup.map (AddMonoidHom.mulLeft f) := AddSubgroup.map_mono hAC
  have h2 : C.toSubring.toAddSubgroup.map (AddMonoidHom.mulLeft f) ≤ A.toSubring.toAddSubgroup := by
    rintro _ ⟨y, hy, rfl⟩
    exact hdC y hy
  have e1 := AddSubgroup.relIndex_mul_relIndex _ _ _ h1 h2
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ hinj] at e1
  have hcard : (A.toSubring.toAddSubgroup.map (AddMonoidHom.mulLeft f)).relIndex
      A.toSubring.toAddSubgroup ≠ 0 := by
    let e : Localization.AtPrime m ≃ₐ[O] A := IsLocalization.algEquiv m.primeCompl _ _
    have hq1 : Nat.card (Localization.AtPrime m ⧸ Ideal.span {algebraMap O (Localization.AtPrime m) d}) =
        Nat.card (A.toSubring ⧸ Ideal.span {(algebraMap O A d : A.toSubring)}) := by
      refine Nat.card_congr (Ideal.quotientEquiv _ _ e.toRingEquiv ?_).toEquiv
      rw [Ideal.map_span, Set.image_singleton]
      congr 2
      exact (e.commutes d).symm
    have hfL : ((algebraMap O A d : A.toSubring) : L) = f := rfl
    have hcq := card_quot_span_eq_relIndex A.toSubring (algebraMap O A d : A.toSubring)
    rw [hfL] at hcq
    have key : Nat.card (Localization.AtPrime m ⧸
        Ideal.span {algebraMap O (Localization.AtPrime m) d}) ≠ 0 := by
      rw [LocalQuotCard.proof L O hft hfr m d hd0]
      refine pow_ne_zero _ ?_
      have hq : Algebra.FiniteType ℤ (O ⧸ m) :=
        @Algebra.FiniteType.of_surjective ℤ O (O ⧸ m) _ _ _ _ _ hft (Ideal.Quotient.mkₐ ℤ m)
          (Ideal.Quotient.mkₐ_surjective ℤ m)
      let _ : Field (O ⧸ m) := Ideal.Quotient.field m
      obtain ⟨hp, hc⟩ :=
        @natCard_eq_pow_length_of_finiteType (O ⧸ m) _
          (by convert hq <;> rfl) (ringChar (O ⧸ m)) (ringChar.charP _)
      rw [hc]
      exact pow_ne_zero _ hp.ne_zero
    rw [← hcq]
    exact fun h ↦ key (hq1.trans h)
  rw [← e1] at hcard
  exact left_ne_zero_of_mul hcard
end LocalNormalIndex
end GroundTheory.Heights₂.Heights
