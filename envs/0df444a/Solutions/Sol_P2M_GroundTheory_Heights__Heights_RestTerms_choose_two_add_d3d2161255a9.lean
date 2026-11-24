-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_choose_two_add_d3d2161255a9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:47.614609+00:00
-- url     : https://prove2.me/submissions/94ebbbe7-c327-4436-baef-370c2230917e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PRestPolynomialHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution (r a : ℕ) :
    (r + a) * (r + a - 1) / 2 = r * (r - 1) / 2 + a * (a - 1) / 2 + r * a := by
  rw [← Finset.sum_range_id, ← Finset.sum_range_id, ← Finset.sum_range_id, Finset.sum_range_add,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  ring
end GroundTheory.Heights₂.Heights.RestTerms
