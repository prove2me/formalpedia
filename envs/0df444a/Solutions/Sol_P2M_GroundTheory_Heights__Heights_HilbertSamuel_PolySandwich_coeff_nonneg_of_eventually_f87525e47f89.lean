-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_PolySandwich_coeff_nonneg_of_eventually_f87525e47f89
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:05:43.351031+00:00
-- url     : https://prove2.me/submissions/9ababa8b-a298-48dd-81c2-5bf71810280d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPolySandwich
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PPolySandwich
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_PolySandwich_leadingCoeff_nonneg_of_eventually_0ddfabcf76f5

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Polynomial Filter
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace PolySandwich
theorem _root_.solution (f : ℚ[X]) (E : ℕ) (hE : f.natDegree ≤ E)
    (hf : ∀ᶠ n : ℕ in atTop, 0 ≤ f.eval (n : ℚ)) : 0 ≤ f.coeff E := by
  rcases hE.lt_or_eq with hlt | heq
  · rw [coeff_eq_zero_of_natDegree_lt hlt]
  · rw [← heq]
    exact PolySandwich.leadingCoeff_nonneg_of_eventually f hf
end PolySandwich
end GroundTheory.Heights₂.Heights.HilbertSamuel
