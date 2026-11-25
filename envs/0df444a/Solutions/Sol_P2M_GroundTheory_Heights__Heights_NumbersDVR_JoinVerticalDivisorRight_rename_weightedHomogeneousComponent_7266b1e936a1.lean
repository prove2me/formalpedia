-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_rename_weightedHomogeneousComponent_7266b1e936a1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:26:31.536189+00:00
-- url     : https://prove2.me/submissions/a12b6924-ba23-4986-90ef-dd5a744415ea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsMoreAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinVertDivRight
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_midNat_injective_747e29b1d6e4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_isMultiHomog_rename_defefe0d02e9

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
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal mcMap joinCoord midDeg midVar)
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisorRight
variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}
variable [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisorRight
theorem _root_.solution [DecidableEq K] [DecidableEq K'] [DecidableEq K₂] {R : Type}
    [CommRing R] (b : K ⊕ K' → ℕ) (h : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R) :
    rename (midVar ι₂) (weightedHomogeneousComponent (blockWeight (Sum.elim ι ι')) b h) =
      weightedHomogeneousComponent (blockWeight (Sum.elim ι (Sum.elim ι₂ ι'))) (midNat b)
        (rename (midVar ι₂) h) := by
  induction h using MvPolynomial.induction_on' with
  | monomial d r =>
    have hm : IsMultiHomog (monomial d r : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R)
        (Finsupp.weight (blockWeight (Sum.elim ι ι')) d) := isWeightedHomogeneous_monomial _ _ _ rfl
    have hj := isMultiHomog_rename (ι₂ := ι₂) hm
    by_cases hb : b = Finsupp.weight (blockWeight (Sum.elim ι ι')) d
    · subst hb
      rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same hm,
        IsWeightedHomogeneous.weightedHomogeneousComponent_same hj]
    · rw [IsWeightedHomogeneous.weightedHomogeneousComponent_ne b hm hb,
        IsWeightedHomogeneous.weightedHomogeneousComponent_ne _ hj (fun e => hb (midNat_injective e)),
        map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
end GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisorRight
