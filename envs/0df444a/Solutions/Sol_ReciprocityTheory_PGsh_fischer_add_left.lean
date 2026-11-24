-- Prove2me | solution 1 for ReciprocityTheory.PGsh.fischer_add_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:53.799815+00:00
-- url     : https://prove2.me/submissions/27b23069-4d9a-4980-9358-3dbdd7b40701

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_FischerSmulRight
import Theorems.Thm_ReciprocityTheory_PGsh_fischer_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open scoped Classical
open ReciprocityTheory ReciprocityTheory.PGsh
variable {ν : ℕ} {ι : Type*}
namespace ReciprocityTheory.PGsh
theorem _root_.solution (P P' Q : MvPolynomial (Fin ν × ι) ℂ) :
    fischer (P + P') Q = fischer P Q + fischer P' Q := by
  have hsub : (P + P').support ⊆ P.support ∪ P'.support := by
    intro A hA
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_add] at hA
    rw [Finset.mem_union, MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff]
    by_contra h
    simp only [not_or, ne_eq, not_not] at h
    rw [h.1, h.2, add_zero] at hA
    exact hA rfl
  rw [fischer_eq_sum (P + P') Q (P.support ∪ P'.support) hsub,
    fischer_eq_sum P Q (P.support ∪ P'.support) (fun x hx => Finset.mem_union_left _ hx),
    fischer_eq_sum P' Q (P.support ∪ P'.support) (fun x hx => Finset.mem_union_right _ hx),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [MvPolynomial.coeff_add]
  ring
end ReciprocityTheory.PGsh
