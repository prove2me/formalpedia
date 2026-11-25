-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_PlueckerCauchyBinet_intersectionNumber_baseChange_577c916731df
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:36:47.883998+00:00
-- url     : https://prove2.me/submissions/8ec9d94c-0392-47c2-bbc1-9bf6979da6a9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Pluecker
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_cauchyBinet_b49b24ee53ec

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
open Elem
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace PlueckerCauchyBinet
theorem _root_.solution : PlueckerCauchyBinet.Statement := by
  intro p q Z
  set A := Matrix.fromCols (1 : Matrix (Fin p) (Fin p) ℂ) Z with hAdef
  have hA : 1 + Z * Z.conjTranspose = A * A.conjTranspose := by
    rw [hAdef, conjTranspose_fromCols_eq_fromRows_conjTranspose, fromCols_mul_fromRows]
    simp
  rw [hA, cauchyBinet, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hB : A.conjTranspose.submatrix (subsetCols S) id =
      (A.submatrix id (subsetCols S)).conjTranspose := by
    ext i j; simp
  rw [hB, det_conjTranspose, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl
end PlueckerCauchyBinet
end GroundTheory.Heights₂.Heights.RestTerms
