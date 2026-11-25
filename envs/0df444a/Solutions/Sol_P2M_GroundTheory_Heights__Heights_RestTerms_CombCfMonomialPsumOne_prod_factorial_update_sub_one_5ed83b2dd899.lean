-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CombCfMonomialPsumOne_prod_factorial_update_sub_one_5ed83b2dd899
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:23:07.103926+00:00
-- url     : https://prove2.me/submissions/f80c3b3c-e242-4c37-af80-c2a62af328bd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombCfMonomialPsumOne

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
open MvPolynomial Finset Comb
open GroundTheory.Heights₂.Heights.RestTerms.CombCfMonomialPsumOne
namespace GroundTheory.Heights₂.Heights.RestTerms.CombCfMonomialPsumOne
theorem _root_.solution {m : ℕ} (l v : Fin m → ℕ) (i : Fin m) (hi : v i < l i) :
    (∏ j, ((Function.update l i (l i - 1) j - v j).factorial : ℚ)) * ((l i - v i : ℕ) : ℚ) =
      ∏ j, ((l j - v j).factorial : ℚ) := by
  have hf : (fun j => ((Function.update l i (l i - 1) j - v j).factorial : ℚ)) =
      Function.update (fun j => ((l j - v j).factorial : ℚ)) i ((l i - 1 - v i).factorial : ℚ) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  rw [hf, Finset.prod_update_of_mem (Finset.mem_univ i),
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)
      (fun j => ((l j - v j).factorial : ℚ))]
  have h : l i - v i = (l i - 1 - v i) + 1 := by omega
  rw [h, Nat.factorial_succ]
  push_cast
  ring
end GroundTheory.Heights₂.Heights.RestTerms.CombCfMonomialPsumOne
