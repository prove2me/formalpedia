-- Prove2me | solution 1 for PI.OpWords.eval_eq_zero_of_support
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:23.443994+00:00
-- url     : https://prove2.me/submissions/2c9f6b34-f455-45f2-bd02-a1403b461447

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_VanishExp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_VanishMain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.OpWords
variable {K : Type} [Field K] [CharZero K] {k : ℕ}
namespace PI.OpWords
theorem _root_.solution (g : Pol K k) (p : Fin k ⊕ Fin k → K)
    (h : ∀ m ∈ g.support, ∃ i, m i ≠ 0 ∧ p i = 0) : eval p g = 0 := by
  rw [eval_eq]
  refine Finset.sum_eq_zero fun m hm => ?_
  obtain ⟨i, hmi, hpi⟩ := h m hm
  rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hmi) (by rw [hpi]; exact zero_pow hmi), mul_zero]
end PI.OpWords
