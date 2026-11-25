-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_VandermondeOfHomogeneous_sum_card_Ioi_77f69092f923
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:12:58.014509+00:00
-- url     : https://prove2.me/submissions/d6297314-4244-4d08-906f-72febbf9cb3c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PVandermondeOfHomogeneous

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
namespace VandermondeOfHomogeneous
theorem _root_.solution (m : ℕ) :
    (∑ i : Fin m, ∑ _j ∈ Finset.Ioi i, (1 : ℕ)) = m * (m - 1) / 2 := by
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun i => m - 1 - i) m]
  have h := Finset.sum_range_reflect (fun i => i) m
  rw [h, Finset.sum_range_id]
end VandermondeOfHomogeneous
end GroundTheory.Heights₂.Heights.RestTerms
