-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Elem_det_submatrix_eq_zero_of_not_injective_54a2168de0b0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:50:36.396272+00:00
-- url     : https://prove2.me/submissions/2e16cca4-fbc8-496c-a551-049a35d103de

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
theorem _root_.solution {p : ℕ} (A : Matrix (Fin p) κ R)
    (φ : Fin p → κ) (h : ¬ Function.Injective φ) : (A.submatrix id φ).det = 0 := by
  simp only [Function.Injective, not_forall] at h
  obtain ⟨i, j, hij, hne⟩ := h
  exact det_zero_of_column_eq hne (fun k => by simp [hij])
end GroundTheory.Heights₂.Heights.RestTerms.Elem
