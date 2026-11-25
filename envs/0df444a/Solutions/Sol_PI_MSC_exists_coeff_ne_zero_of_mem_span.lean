-- Prove2me | solution 1 for PI.MSC.exists_coeff_ne_zero_of_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:50:09.424793+00:00
-- url     : https://prove2.me/submissions/c3ea95b4-ebe1-4708-80de-122f78d5f0fe

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_ExistsCoeffNeZeroOfMemSpan

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
open PI PI.MSC
open scoped MonomialOrder
variable {σ R : Type*} [CommRing R]
namespace PI.MSC
theorem _root_.solution (O : MonomialOrder σ) {ι : Type*}
    (c : ι → MvPolynomial σ R) (hinj : Function.Injective fun i => O.degree (c i))
    (hlc : ∀ i, O.leadingCoeff (c i) = 1) {g : MvPolynomial σ R}
    (hg : g ∈ Submodule.span R (Set.range c)) (hg0 : g ≠ 0) :
    ∃ i, g.coeff (O.degree (c i)) ≠ 0 := by
  classical
  obtain ⟨f, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hg
  have hne : f.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    apply hg0
    rw [Finsupp.support_eq_empty.mp h, Finsupp.sum_zero_index]
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image f.support (fun j => O.toSyn (O.degree (c j))) hne
  refine ⟨i, ?_⟩
  have hlt : ∀ j ∈ f.support, j ≠ i → O.toSyn (O.degree (c j)) < O.toSyn (O.degree (c i)) := by
    intro j hj hji
    refine lt_of_le_of_ne (hmax j hj) ?_
    intro heq
    exact hji (hinj (O.toSyn.injective heq))
  rw [Finsupp.sum, MvPolynomial.coeff_sum, Finset.sum_eq_single i]
  · rw [MvPolynomial.coeff_smul, smul_eq_mul]
    have h1 : (c i).coeff (O.degree (c i)) = 1 := hlc i
    rw [h1, mul_one]
    exact Finsupp.mem_support_iff.mp hi
  · intro j hj hji
    rw [MvPolynomial.coeff_smul, MonomialOrder.coeff_eq_zero_of_lt (hlt j hj hji), smul_zero]
  · intro h
    exact absurd hi h
end PI.MSC
