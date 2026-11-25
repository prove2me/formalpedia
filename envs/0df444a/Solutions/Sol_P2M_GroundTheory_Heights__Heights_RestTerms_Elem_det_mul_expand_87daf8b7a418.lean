-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Elem_det_mul_expand_87daf8b7a418
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:50:35.711676+00:00
-- url     : https://prove2.me/submissions/3c3a4312-a52c-491a-8b82-c8343f2ba2e8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Pluecker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open Matrix Finset
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.Elem
variable {R : Type*} [CommRing R] {κ : Type*}
namespace GroundTheory.Heights₂.Heights.RestTerms.Elem
theorem _root_.solution [Fintype κ] {p : ℕ} (A : Matrix (Fin p) κ R) (B : Matrix κ (Fin p) R) :
    (A * B).det = ∑ φ : Fin p → κ, (A.submatrix id φ).det * ∏ i, B (φ i) i := by
  simp only [det_apply', mul_apply, Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun φ _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [submatrix_apply, id, Finset.prod_mul_distrib]
  ring
end GroundTheory.Heights₂.Heights.RestTerms.Elem
