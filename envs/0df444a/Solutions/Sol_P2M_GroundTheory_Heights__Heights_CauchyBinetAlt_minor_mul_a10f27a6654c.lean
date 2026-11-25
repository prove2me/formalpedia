-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CauchyBinetAlt_minor_mul_a10f27a6654c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:36:26.775342+00:00
-- url     : https://prove2.me/submissions/602669c3-4d14-4a7a-9bb3-43ce7d845a0b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet

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
open Matrix Finset Equiv
open GroundTheory.Heights₂.Heights.CauchyBinetAlt
variable {R : Type*} [CommRing R] {j N : ℕ}
namespace GroundTheory.Heights₂.Heights.CauchyBinetAlt
theorem _root_.solution (A : Matrix (Fin j) (Fin N) R) (B : Matrix (Fin N) (Fin j) R)
    (I : {I : Finset (Fin N) // I.card = j}) :
    (colsOf A I).det * (rowsOf B I).det =
      ∑ w : Perm (Fin j), (∏ i, B (I.1.orderEmbOfFin I.2 (w i)) i) *
        (A.submatrix id (I.1.orderEmbOfFin I.2 ∘ w)).det := by
  rw [det_apply' (rowsOf B I), mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h : A.submatrix id (I.1.orderEmbOfFin I.2 ∘ w) = (colsOf A I).submatrix id w := by
    ext a b
    rfl
  rw [h, det_permute']
  simp only [rowsOf, submatrix_apply, id]
  ring
end GroundTheory.Heights₂.Heights.CauchyBinetAlt
