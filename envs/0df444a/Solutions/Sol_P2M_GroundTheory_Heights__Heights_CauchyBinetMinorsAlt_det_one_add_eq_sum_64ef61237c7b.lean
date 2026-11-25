-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CauchyBinetMinorsAlt_det_one_add_eq_sum_64ef61237c7b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:36:30.207442+00:00
-- url     : https://prove2.me/submissions/a7f50f34-2655-4c63-9c40-a8e5922d57a0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCauchyBinetMinors

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
open Matrix Finset
open GroundTheory.Heights₂.Heights.CauchyBinetMinorsAlt
namespace GroundTheory.Heights₂.Heights.CauchyBinetMinorsAlt
theorem _root_.solution {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n R) :
    (1 + X).det = ∑ s : Finset n, (X.submatrix ((↑) : s → n) ((↑) : s → n)).det := by
  rw [add_comm]
  change detRowAlternating (fun i => X i + (1 : Matrix n n R) i) = _
  rw [show (fun i => X i + (1 : Matrix n n R) i) =
      (fun i => X i) + (fun i => (1 : Matrix n n R) i) from rfl, AlternatingMap.map_add_univ]
  refine Finset.sum_congr rfl fun s _ => ?_
  exact det_piecewise_one_eq_submatrix_det X s
end GroundTheory.Heights₂.Heights.CauchyBinetMinorsAlt
