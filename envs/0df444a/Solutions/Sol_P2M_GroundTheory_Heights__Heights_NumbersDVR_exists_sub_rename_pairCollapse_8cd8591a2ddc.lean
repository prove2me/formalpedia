-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_sub_rename_pairCollapse_8cd8591a2ddc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:40:30.232942+00:00
-- url     : https://prove2.me/submissions/4f5a4bfd-e292-4804-b15f-8f1dbad89393

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMixedDiffLinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OfSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberExpansionKoszul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (p : Fin n) (G : MvPolynomial (Fin n ⊕ Fin n) ℤ) :
    ∃ Q, G - rename (pairCollapse p) G = pairDiff p * Q := by
  induction G using MvPolynomial.induction_on with
  | C a => exact ⟨0, by simp⟩
  | add G H hG hH =>
    obtain ⟨Q₁, h₁⟩ := hG
    obtain ⟨Q₂, h₂⟩ := hH
    refine ⟨Q₁ + Q₂, ?_⟩
    rw [map_add, mul_add, ← h₁, ← h₂]
    ring
  | mul_X G s hG =>
    obtain ⟨Q, hQ⟩ := hG
    refine ⟨Q * X s + if s = Sum.inl p then rename (pairCollapse p) G else 0, ?_⟩
    have hs : X s - rename (pairCollapse p) (X s) =
        pairDiff p * (if s = Sum.inl p then 1 else 0) := by
      rw [rename_X]
      unfold pairCollapse pairDiff
      split_ifs with h
      · subst h
        ring
      · simp
    calc G * X s - rename (pairCollapse p) (G * X s)
        = (G - rename (pairCollapse p) G) * X s +
            rename (pairCollapse p) G * (X s - rename (pairCollapse p) (X s)) := by
          rw [map_mul]
          ring
      _ = _ := by
          rw [hQ, hs]
          split_ifs <;> ring
end GroundTheory.Heights₂.Heights.NumbersDVR
