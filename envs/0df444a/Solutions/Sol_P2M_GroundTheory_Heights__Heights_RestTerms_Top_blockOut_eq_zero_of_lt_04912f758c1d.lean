-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockOut_eq_zero_of_lt_04912f758c1d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:53:39.375307+00:00
-- url     : https://prove2.me/submissions/985b9d3d-d045-4505-9881-74c4058993ec

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_sum_of_mem_partitionsOf_e2ce5534b3c3

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
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Top
theorem _root_.solution (r a : ℕ) (c : SmallBlock) (κ : ℚ) (q m : ℕ)
    (h : q + m < r * a) : blockOut r a c κ q m = 0 := by
  refine Finset.sum_eq_zero fun lam hlam => ?_
  have hs := sum_of_mem_partitionsOf hlam
  rw [pushOut, if_neg, smul_zero]
  intro hall
  have : ∑ i : Fin r, a ≤ ∑ i, lam i := Finset.sum_le_sum fun i _ => hall i
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
  omega
end GroundTheory.Heights₂.Heights.RestTerms.Top
