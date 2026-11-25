-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_lemmas_hypotheses_example_719c75c092f9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:27.722183+00:00
-- url     : https://prove2.me/submissions/3867d8b8-5523-4d68-954c-a5e7b3165e7c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_span_singleton_c8d0b884ca6f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isModelOver_projectiveSpace_b39ad6b0fb36
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isVerticalDivisor_uniformiser_50f9902254e2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution :
    let S := MRing (fun _ : Unit => Fin 2) ℤ_[2]
    let ϖ : ℤ_[2] := ((2 : ℕ) : ℤ_[2])
    let H : Ideal S := Ideal.span {X ⟨(), 0⟩}
    IsModelOver (⊥ : Ideal S) 1 ∧ (X ⟨(), 0⟩ : S) ∉ (⊥ : Ideal S) ∧ (X ⟨(), 1⟩ : S) ∉ (⊥ : Ideal S) ∧
      IsVerticalDivisor (⊥ : Ideal S) ϖ 0 (C ϖ) 1 ∧
      IsMultiProjPrime H ∧ (⊥ : Ideal S) ≤ H ∧ (C ϖ : S) ∉ H ∧
      H ∈ ((⊥ : Ideal S) ⊔ Ideal.span {X ⟨(), 0⟩}).minimalPrimes := by
  intro S ϖ H
  have hϖ : ϖ ≠ 0 := PadicInt.irreducible_p.ne_zero
  have hCϖ : (C ϖ : S) ∉ (⊥ : Ideal S) := by
    rw [Ideal.mem_bot, C_eq_zero]; exact hϖ

  have hev : ∀ p ∈ H, aeval (fun v : Σ _ : Unit, Fin 2 => if v.2 = 0 then (0 : S) else X v) p = 0 := by
    intro p hp
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    simp
  have hHprime : H.IsPrime := (Ideal.span_singleton_prime (X_ne_zero _)).mpr (MvPolynomial.X_prime)
  refine ⟨isModelOver_projectiveSpace 1, by rw [Ideal.mem_bot]; exact X_ne_zero _,
    by rw [Ideal.mem_bot]; exact X_ne_zero _, isVerticalDivisor_uniformiser ϖ ⊥ hCϖ,
    ⟨hHprime, isMultiHomogIdeal_span_singleton (isWeightedHomogeneous_X _ _ _), ?_⟩, bot_le, ?_, ?_⟩
  · intro k
    refine ⟨1, fun h => ?_⟩
    have := hev _ h
    simp at this
    exact X_ne_zero _ this
  · intro h
    have := hev _ h
    rw [aeval_C] at this
    change (C ϖ : S) = 0 at this
    exact hϖ (C_eq_zero.mp this)
  · rw [bot_sup_eq, Ideal.minimalPrimes_eq_subsingleton_self]
    rfl
end GroundTheory.Heights₂.Heights.NumbersDVR
