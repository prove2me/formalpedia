-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_vandermondeOf_eq_vandermonde_144b4b56a0c7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:50.284726+00:00
-- url     : https://prove2.me/submissions/9d18a864-9c2e-4943-8c65-7c7a079c28ec

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHomogeneousComponentMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_X_6be993a34174
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_C_43a59c7a9997
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
theorem _root_.solution {R : Type*} [CommRing R] {m : ℕ} (v : Fin m → R) :
    vandermondeOf v = GroundTheory.Heights₂.Heights.vandermonde v := by
  have hM : (Matrix.of fun a b : Fin m => v a ^ (m - 1 - (b : ℕ))) =
      (Matrix.vandermonde v).submatrix id Fin.revPerm := by
    ext a b
    simp only [Matrix.of_apply, Matrix.submatrix_apply, id, Matrix.vandermonde_apply,
      Fin.revPerm_apply, Fin.val_rev]
    congr 1
    omega
  have hW : Matrix.vandermonde (fun i => v (Fin.revPerm i)) =
      (Matrix.vandermonde v).submatrix Fin.revPerm id := by
    ext a b
    simp [Matrix.vandermonde_apply]
  rw [GroundTheory.Heights₂.Heights.vandermonde, hM, Matrix.det_permute', ← Matrix.det_permute, ← hW,
    Matrix.det_vandermonde]
  have key : ∀ g : Fin m → Fin m → R,
      ∏ i, ∏ l ∈ Ioi i, g i l = ∏ i, ∏ l, if i < l then g i l else 1 := by
    intro g
    refine prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_filter]
    congr 1
    ext l
    simp
  rw [vandermondeOf, key, key]
  conv_rhs => rw [Finset.prod_comm]
  refine Fintype.prod_equiv Fin.revPerm _ _ (fun i => ?_)
  refine Fintype.prod_equiv Fin.revPerm _ _ (fun l => ?_)
  simp [Fin.revPerm_apply, Fin.rev_lt_rev]
end GroundTheory.Heights₂.Heights.RestTerms
