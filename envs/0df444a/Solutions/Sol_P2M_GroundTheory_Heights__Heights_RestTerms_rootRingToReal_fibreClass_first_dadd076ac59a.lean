-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_fibreClass_first_dadd076ac59a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:48.162054+00:00
-- url     : https://prove2.me/submissions/1b707cbf-1f52-48dc-9dc6-c08ef0be66be

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHomogeneousComponentMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_X_6be993a34174
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_C_43a59c7a9997
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_map_vandermondeOf_e6810552c7af
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_vandermondeOf_eq_vandermonde_144b4b56a0c7
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Heights₂.Heights.RestTerms.rootRingToReal_X
attribute [local simp] GroundTheory.Heights₂.Heights.RestTerms.rootRingToReal_C

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution (f r a : ℕ) :
    rootRingToReal f (r + a) r a rfl (fibreClass f r a .first) =
      IndefiniteRowSideFullHecke.RestTerms.fibClass f r a false := by
  simp only [fibreClass, IndefiniteRowSideFullHecke.RestTerms.fibClass, Bool.false_eq_true, if_false, map_prod, map_mul,
    map_vandermondeOf]
  refine prod_congr rfl fun τ _ => ?_
  rw [vandermondeOf_eq_vandermonde, vandermondeOf_eq_vandermonde]
  congr 2
  · funext i
    simp only [yRoot, SmallBlock.sign, yIndex, map_mul, rootRingToReal_C, rootRingToReal_X, Rat.cast_neg,
      Rat.cast_one, C_neg, C_1, neg_one_mul, map_neg] <;> rfl
  · funext i
    simp only [zRoot, zIndex, rootRingToReal_X] <;> rfl
end GroundTheory.Heights₂.Heights.RestTerms
