-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_PolySandwich_coeff_shift_0da3de1d8bbc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:30.369809+00:00
-- url     : https://prove2.me/submissions/9d0b9bc3-fe33-45bd-9bcd-578af1b3b553

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPolySandwich
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PPolySandwich
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_PolySandwich_natDegree_shift_9db74c7fa47e

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
theorem _root_.solution (p : ℚ[X]) (c : ℚ) (E : ℕ) (hE : p.natDegree ≤ E) :
    (p.comp (X + C c)).coeff E = p.coeff E := by
  rcases hE.lt_or_eq with hlt | heq
  · rw [coeff_eq_zero_of_natDegree_lt hlt,
      coeff_eq_zero_of_natDegree_lt (by rwa [PolySandwich.natDegree_shift])]
  · subst heq
    have h1 : (p.comp (X + C c)).leadingCoeff = p.leadingCoeff := by
      rw [leadingCoeff_comp (by rw [natDegree_X_add_C]; exact one_ne_zero), leadingCoeff_X_add_C, one_pow,
        mul_one]
    rw [leadingCoeff, PolySandwich.natDegree_shift] at h1
    exact h1
end PolySandwich
end GroundTheory.Heights₂.Heights.HilbertSamuel
