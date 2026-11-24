-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KRest_sum_fin_val_mul_two_327ec1f0d7fe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:03.751958+00:00
-- url     : https://prove2.me/submissions/2acea586-f294-42a8-9067-524c6197102c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_RestCutBasic

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
open GroundTheory.Heights₂.Heights.KRest
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.KRest
theorem _root_.solution (N : ℕ) : (∑ i : Fin N, (i : ℕ)) * 2 = N * (N - 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id_mul_two]
end GroundTheory.Heights₂.Heights.KRest
