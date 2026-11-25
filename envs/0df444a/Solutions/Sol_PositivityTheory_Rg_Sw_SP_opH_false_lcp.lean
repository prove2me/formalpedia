-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.opH_false_lcp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:49:14.83043+00:00
-- url     : https://prove2.me/submissions/63d85623-891c-4fba-8f0d-2190efb27651

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivA
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_opH_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution (s : ℂ) (m : ℕ) (k l : Fin n) {Q' : Fm n}
    (hQ : ∀ a d : Fin n, pderiv (false, a, d) Q' = 0) : LCP Q' (opH s m false k l) := by
  intro R
  have hd : ∀ a d : Fin n, pderiv (false, a, d) (Q' * R) = Q' * pderiv (false, a, d) R := by
    intro a d
    rw [Derivation.leibniz, hQ a d, smul_zero, add_zero, smul_eq_mul]
  rw [opH_apply, opH_apply, mul_add, Finset.mul_sum]
  congr 1
  · rw [mul_smul_comm]; exact congrArg _ (by ring)
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hd, mul_smul_comm]; exact congrArg _ (by ring)
end PositivityTheory.Rg.Sw.SP
