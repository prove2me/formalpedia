-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__CuspExists_exists_monic_irreducible_4b6ba284380d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:04:30.415798+00:00
-- url     : https://prove2.me/submissions/f7c3f79c-8c86-465c-880e-c35a0f3b0f70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCuspidalWithLabel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsTeichmullerMapAlgebraicClosureFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IsIrreducibleTransportRep
import Theorems.Thm_Formalism_L2_DIV_IsAbsIrrChar_isIntegral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists
variable (K : Type) [Field K] [Fintype K]
namespace GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists
theorem _root_.solution (d : ℕ) (hd : 1 ≤ d) :
    ∃ P : K[X], P.Monic ∧ Irreducible P ∧ P ≠ X ∧ P.natDegree = d := by
  haveI : Fact (Nat.Prime (ringChar K)) := ⟨CharP.char_is_prime K (ringChar K)⟩
  haveI : NeZero d := ⟨by omega⟩
  let E := FiniteField.Extension K (ringChar K) d
  have hfin : Module.finrank K E = d := FiniteField.finrank_extension K (ringChar K) d
  obtain ⟨β, hβ⟩ := Field.exists_primitive_element K E
  obtain ⟨α, hα0, hα⟩ : ∃ α : E, α ≠ 0 ∧ IntermediateField.adjoin K {α} = ⊤ := by
    by_cases h : β = 0
    · refine ⟨1, one_ne_zero, ?_⟩
      subst h
      rw [IntermediateField.adjoin_one]
      rwa [IntermediateField.adjoin_zero] at hβ
    · exact ⟨β, h, hβ⟩
  have hint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  refine ⟨minpoly K α, minpoly.monic hint, minpoly.irreducible hint, fun h => hα0 ?_, ?_⟩
  · have h0 := minpoly.aeval K α
    rwa [h, aeval_X] at h0
  · rw [← IntermediateField.adjoin.finrank hint, hα, IntermediateField.finrank_top', hfin]
end GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists
