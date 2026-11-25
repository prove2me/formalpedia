-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_hsymm_isHomogeneous_fa4efb84373b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:30:53.064909+00:00
-- url     : https://prove2.me/submissions/fe5388e5-83bb-4641-99b0-54dd129df19e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchSchurHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_sum_a5fe0c99cdcf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_hsymm_eq_sum_finsuppAntidiag_43772939f291


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
theorem _root_.solution (σ : Type*) [Fintype σ] [DecidableEq σ] (n : ℕ) :
    (hsymm σ ℚ n).IsHomogeneous n := by
  rw [Schur.hsymm_eq_sum_finsuppAntidiag]
  refine IsHomogeneous.sum _ _ _ fun l hl => ?_
  have hsum : ∑ i, l i = n := (mem_finsuppAntidiag.mp hl).1
  rw [← hsum]
  exact IsHomogeneous.prod _ _ _ fun i _ => by
    simpa using (isHomogeneous_X ℚ i).pow (l i)
end GroundTheory.Heights₂.Heights.RestTerms
