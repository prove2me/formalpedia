-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointVerticalDivisor_rename_weightedHomogeneousComponent_6c090a1c8134
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:39:44.343825+00:00
-- url     : https://prove2.me/submissions/a2227028-3c7f-4f07-a57c-9387af279ea8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerExtra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVerticalDivisorJoinPullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinPointVertDiv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomog_joinForm_b4deacf8f20d


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
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord liftVar pullDeg joinCoord mcIdeal IsVertDiv)
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointVerticalDivisor
variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
variable [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
omit [Fintype K'] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointVerticalDivisor
theorem _root_.solution [DecidableEq K] [DecidableEq K'] {R : Type} [CommRing R]
    (b : K → ℕ) (h : MvPolynomial (Σ k, ι k) R) :
    rename (liftVar ι') (weightedHomogeneousComponent (blockWeight ι) b h) =
      weightedHomogeneousComponent (blockWeight (Sum.elim ι ι')) (Sum.elim b 0)
        (rename (liftVar ι') h) := by
  induction h using MvPolynomial.induction_on' with
  | monomial d r =>
    have hm : IsMultiHomog (monomial d r : MRing ι R) (Finsupp.weight (blockWeight ι) d) :=
      isWeightedHomogeneous_monomial _ _ _ rfl
    have hj : IsMultiHomog (rename (liftVar ι') (monomial d r : MRing ι R))
        (Sum.elim (Finsupp.weight (blockWeight ι) d) 0) := isMultiHomog_joinForm hm
    by_cases hb : b = Finsupp.weight (blockWeight ι) d
    · subst hb
      rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same hm,
        IsWeightedHomogeneous.weightedHomogeneousComponent_same hj]
    · have hb' : (Sum.elim b 0 : K ⊕ K' → ℕ) ≠ Sum.elim (Finsupp.weight (blockWeight ι) d) 0 :=
        fun e => hb (funext fun k => congrFun e (Sum.inl k))
      rw [IsWeightedHomogeneous.weightedHomogeneousComponent_ne b hm hb,
        IsWeightedHomogeneous.weightedHomogeneousComponent_ne _ hj hb', map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
end GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointVerticalDivisor
