-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_rename_dropPt_of_homog_e7fc05f7ee1a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:24:34.010874+00:00
-- url     : https://prove2.me/submissions/828698b6-a73b-4d7b-bf34-7690c1c9dd5a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinIntNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PEventualValueFacts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PJoinIntNum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_weight_newBlock_8970a1a2384f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_rename_dropPt_monomial_0fae10bf47d2

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
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx liftVar pullDeg)
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
noncomputable section
set_option linter.unusedSectionVars false
variable {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
theorem _root_.solution {g : MRing (Sum.elim ι ptIdx) F} {M : K ⊕ Unit → ℕ}
    (hg : IsWeightedHomogeneous (blockWeight (Sum.elim ι ptIdx)) g M) :
    rename (liftVar (ι := ι) ptIdx) (aeval (dropPt F) g) * X newVar ^ (M (.inr ())) = g := by
  conv_rhs => rw [g.as_sum]
  conv_lhs => rw [g.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw : Finsupp.weight (blockWeight (Sum.elim ι ptIdx)) d = M := hg (mem_support_iff.mp hd)
  have ht : M (.inr ()) = d newVar := by rw [← hw, weight_newBlock]
  rw [ht, rename_dropPt_monomial]
end GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
