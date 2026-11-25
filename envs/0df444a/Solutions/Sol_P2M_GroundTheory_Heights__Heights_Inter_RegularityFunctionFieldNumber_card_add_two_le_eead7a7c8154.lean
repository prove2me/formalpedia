-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RegularityFunctionFieldNumber_card_add_two_le_eead7a7c8154
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:53:12.606825+00:00
-- url     : https://prove2.me/submissions/147833eb-cb96-4214-a938-1fb2c1de35ca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotMemOfNonZeroDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PHorizNotMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FunFieldLeLocRing
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularityFunctionFieldNumber_specMap_X_ce1131bead89
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularityFunctionFieldNumber_specMap_form_ff00a8b1a3cb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_HorizNotMem_ringKrullDim_quotient_add_one_le_8cf7c98efa8e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.RegularityFunctionFieldNumber
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable [DecidableEq K] {E : Type*} [Field E]
namespace GroundTheory.Heights₂.Heights.Inter.RegularityFunctionFieldNumber
theorem _root_.solution [CharZero E] (ψ : MRing ι →+* E) (j : ∀ k, ι k) (hj : ∀ k, ψ (X ⟨k, j k⟩) = 1)
    {P : Ideal (MRing ι)} [P.IsPrime] (hPh : IsMultiHomogIdeal P)
    (hPψ : ∀ (g : MRing ι) (a : K → ℕ), IsMultiHomog g a → g ∈ P → ψ g = 0)
    {u : MRing ι} {a : K → ℕ} (hu : IsMultiHomog u a) (huP : u ∉ P) (hψu : ψ u = 0) :
    ((Fintype.card K + 2 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι ⧸ P) := by
  let Q : Finset K → Ideal (MRing ι) := fun S => RingHom.ker (specMap ψ S)
  have hQp : ∀ S, (Q S).IsPrime := fun S => RingHom.ker_isPrime _
  have hmem : ∀ S g, g ∈ Q S ↔ specMap ψ S g = 0 := fun S g => RingHom.mem_ker

  have hPQ : P < Q ∅ := by
    obtain ⟨T, hT, hPT⟩ := hPh
    refine SetLike.lt_iff_le_and_exists.mpr ⟨?_, u, ?_, huP⟩
    · rw [hPT, Ideal.span_le]
      intro g hg
      obtain ⟨b, hb⟩ := hT g hg
      rw [SetLike.mem_coe, hmem, specMap_form ψ ∅ hb, hPψ g b hb (hPT ▸ Ideal.subset_span hg), map_zero,
        mul_zero]
    · rw [hmem, specMap_form ψ ∅ hu, hψu, map_zero, mul_zero]

  have hstep : ∀ S k, k ∉ S → Q S < Q (insert k S) := by
    intro S k hk
    let ρ : MvPolynomial K E →+* MvPolynomial K E :=
      (aeval fun k' => if k' = k then (0 : MvPolynomial K E) else MvPolynomial.X k').toRingHom
    have e : ρ.comp (specMap ψ S).toRingHom = (specMap ψ (insert k S)).toRingHom := by
      refine MvPolynomial.ringHom_ext (fun n => by simp) fun q => ?_
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, specMap_X, map_mul]
      congr 1
      · by_cases h1 : q.1 ∈ S
        · simp [ρ, cS, h1]
        · by_cases h2 : q.1 = k
          · subst h2
            simp [ρ, cS, h1]
          · simp [ρ, cS, h1, h2]
      · simp [ρ]
    refine SetLike.lt_iff_le_and_exists.mpr ⟨fun g hg => ?_, X ⟨k, j k⟩, ?_, ?_⟩
    · rw [hmem] at hg ⊢
      have := congrArg (fun f => f g) e
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
      rw [← this, hg, map_zero]
    · rw [hmem, specMap_X]
      simp [cS]
    · rw [hmem, specMap_X, hj, map_one, mul_one]
      simp only [cS, if_neg hk]
      exact MvPolynomial.X_ne_zero k

  let Qt : Ideal (MRing ι) := RingHom.ker ((Int.castRingHom (ZMod 2)).comp MvPolynomial.constantCoeff)
  have hQt : Qt.IsPrime := RingHom.ker_isPrime _
  have huniv : ∀ g, specMap ψ Finset.univ g = MvPolynomial.C ((MvPolynomial.constantCoeff g : ℤ) : E) := by
    intro g
    have e : (specMap ψ Finset.univ).toRingHom =
        (MvPolynomial.C : E →+* MvPolynomial K E).comp ((Int.castRingHom E).comp MvPolynomial.constantCoeff) :=
      MvPolynomial.ringHom_ext (fun n => by simp) fun q => by simp [specMap_X, cS]
    exact congrArg (fun f => f g) e
  have hc2 : MvPolynomial.constantCoeff (2 : MRing ι) = 2 := by
    rw [show (2 : MRing ι) = MvPolynomial.C 2 from (map_ofNat MvPolynomial.C 2).symm, constantCoeff_C]
  have hlast : Q Finset.univ < Qt := by
    refine SetLike.lt_iff_le_and_exists.mpr ⟨fun g hg => ?_, 2, ?_, ?_⟩
    · rw [hmem, huniv, MvPolynomial.C_eq_zero, Int.cast_eq_zero] at hg
      simp [Qt, RingHom.mem_ker, hg]
    · rw [RingHom.mem_ker, RingHom.comp_apply, hc2, map_ofNat]
      rfl
    · intro h
      rw [hmem, huniv, MvPolynomial.C_eq_zero, Int.cast_eq_zero, hc2] at h
      exact two_ne_zero h

  have chain : ∀ S : Finset K, (S.card : WithBot ℕ∞) + ringKrullDim (MRing ι ⧸ Q S) ≤
      ringKrullDim (MRing ι ⧸ Q ∅) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert k S hk ih =>
      have : (Q S).IsPrime := hQp S
      have : (Q (insert k S)).IsPrime := hQp _
      have h1 := HorizNotMem.ringKrullDim_quotient_add_one_le (hstep S k hk)
      rw [Finset.card_insert_of_notMem hk]
      calc (((S.card + 1 : ℕ)) : WithBot ℕ∞) + ringKrullDim (MRing ι ⧸ Q (insert k S))
          = (S.card : WithBot ℕ∞) + (ringKrullDim (MRing ι ⧸ Q (insert k S)) + 1) := by
            push_cast; abel
        _ ≤ (S.card : WithBot ℕ∞) + ringKrullDim (MRing ι ⧸ Q S) := by gcongr
        _ ≤ _ := ih
  have : (Q ∅).IsPrime := hQp _
  have : (Q Finset.univ).IsPrime := hQp _
  have h0 := HorizNotMem.ringKrullDim_quotient_add_one_le hPQ
  have h2 := HorizNotMem.ringKrullDim_quotient_add_one_le hlast
  have hc := chain Finset.univ
  have : IsDomain (MRing ι ⧸ Qt) := Ideal.Quotient.isDomain _
  have h3 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MRing ι ⧸ Qt) := ringKrullDim_nonneg_of_nontrivial
  rw [Finset.card_univ] at hc
  calc ((Fintype.card K + 2 : ℕ) : WithBot ℕ∞) = (Fintype.card K : WithBot ℕ∞) + (0 + 1) + 1 := by
        push_cast; simp [add_assoc]; rfl
    _ ≤ (Fintype.card K : WithBot ℕ∞) + (ringKrullDim (MRing ι ⧸ Qt) + 1) + 1 := by gcongr
    _ ≤ (Fintype.card K : WithBot ℕ∞) + ringKrullDim (MRing ι ⧸ Q Finset.univ) + 1 := by gcongr
    _ ≤ ringKrullDim (MRing ι ⧸ Q ∅) + 1 := by gcongr
    _ ≤ _ := h0
end GroundTheory.Heights₂.Heights.Inter.RegularityFunctionFieldNumber
