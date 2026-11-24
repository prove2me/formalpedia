-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_sum_staircase_exponents_9893f3414274
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:36:25.983486+00:00
-- url     : https://prove2.me/submissions/3f3b549c-7161-4744-9b5a-03c099c2c23a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvStaircaseDegree

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
open MvPolynomial Finset Coinv
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace Coinv
theorem _root_.solution (f n : ℕ) :
    ∑ v : Fin f × Fin n, (v.2 : ℕ) = coinvTop f n := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]
  rfl
end Coinv
end GroundTheory.Heights₂.Heights.RestTerms
