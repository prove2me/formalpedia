-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CauchyBinetAlt_det_mul_eq_sum_e0cc8465dd90
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:36:23.450424+00:00
-- url     : https://prove2.me/submissions/c18e3e11-59bb-4f98-ab60-63976b6c0f08

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
theorem _root_.solution (A : Matrix (Fin j) (Fin N) R) (B : Matrix (Fin N) (Fin j) R) :
    (A * B).det = ∑ p : Fin j → Fin N, (∏ i, B (p i) i) * (A.submatrix id p).det := by
  simp only [det_apply', mul_apply, prod_univ_sum, mul_sum, Fintype.piFinset_univ,
    submatrix_apply, id]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun σ _ => ?_
  rw [prod_mul_distrib]
  ring
end GroundTheory.Heights₂.Heights.CauchyBinetAlt
