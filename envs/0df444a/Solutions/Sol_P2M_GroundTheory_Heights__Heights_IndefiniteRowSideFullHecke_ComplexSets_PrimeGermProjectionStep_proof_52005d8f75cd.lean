-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimeGermProjectionStep_proof_52005d8f75cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:03:47.720205+00:00
-- url     : https://prove2.me/submissions/0a0b1846-977f-41d4-85ad-13242be55000

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermProjectionStep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermGeneralCoordinates
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeGermProjectionStep
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_germ_division_after_coordinates_2cab62082ae2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isFiniteGermProjection_comp_323d1cf2b56f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isField_holGerms_fin_zero_e759378e8bfd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace PrimeGermProjectionStep
theorem _root_.solution (hD : WeierstrassDivision.Statement)
    (hG : GeneralLinearCoordinates.Statement) : PrimeGermProjectionStep.Statement := by
  classical
  intro σ _ w P hP hP0 IH
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card σ = m + 1 := by
    rcases h : Fintype.card σ with _ | m
    · exfalso
      let e : (Fin 0 → ℂ) ≃L[ℂ] (σ → ℂ) :=
        (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFinOfCardEq h)).toContinuousLinearEquiv
      have hF : IsField (holGerms w) := (germAffineEquiv e w).toMulEquiv.isField isField_holGerms_fin_zero
      let _ := hF.toField
      rcases Ideal.eq_bot_or_top P with h' | h'
      · exact hP0 h'
      · exact hP.ne_top h'
    · exact ⟨m, rfl⟩
  obtain ⟨φ, hφP, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  obtain ⟨π, T, n, hdiv⟩ := germ_division_after_coordinates hD hG hm w φ hφ0
  have hdivP : ∀ ψ : holGerms w, ∃ a : Fin n → holGerms (π w),
      ψ - ∑ j : Fin n, germPull π (π.analyticAt w) rfl (a j) * affineGerm w T (-T w) ^ (j : ℕ) ∈ P := by
    intro ψ
    obtain ⟨r, a, h⟩ := hdiv ψ
    refine ⟨a, ?_⟩
    rw [h, add_sub_cancel_right]
    exact P.mul_mem_left r hφP
  have hP' : (P.comap (germPull π (π.analyticAt w) rfl)).IsPrime := Ideal.IsPrime.comap _
  obtain ⟨d, B, hB⟩ := IH (Fin m) (by simp [hm]) (π w) _ hP'
  exact ⟨d, B.comp π, isFiniteGermProjection_comp w P π T (-T w) n hdivP B hB⟩
end PrimeGermProjectionStep
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
