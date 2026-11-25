-- Prove2me | solution 1 for PI.MSC.monomial_mem_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:51:06.051977+00:00
-- url     : https://prove2.me/submissions/3bc1ea25-73e5-4d2f-b36b-6c63e3b30528

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
theorem _root_.solution (O : MonomialOrder σ) {ι : Type*} (c : ι → MvPolynomial σ R)
    (hlc : ∀ i, O.leadingCoeff (c i) = 1) (e : σ →₀ ℕ) (a : R) :
    monomial e a ∈ Submodule.span R (Set.range c) ⊔
      restrictSupport R (Set.range fun i => O.degree (c i))ᶜ := by
  classical
  haveI := O.wf
  have key : ∀ s : O.syn, ∀ e : σ →₀ ℕ, O.toSyn e = s → ∀ a : R,
      monomial e a ∈ Submodule.span R (Set.range c) ⊔
        restrictSupport R (Set.range fun i => O.degree (c i))ᶜ := by
    intro s
    induction s using WellFoundedLT.induction with
    | _ s ih =>
      intro e he a
      by_cases hmem : e ∈ Set.range fun i => O.degree (c i)
      · obtain ⟨i, rfl⟩ := hmem
        have hdecomp : monomial (O.degree (c i)) a =
            a • c i - a • (c i - monomial (O.degree (c i)) 1) := by
          rw [smul_sub, sub_sub_cancel, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
        rw [hdecomp]
        refine Submodule.sub_mem _
          (Submodule.mem_sup_left (Submodule.smul_mem _ a (Submodule.subset_span ⟨i, rfl⟩)))
          (Submodule.smul_mem _ a ?_)
        have hlc1 : (c i).coeff (O.degree (c i)) = 1 := hlc i
        set q := c i - monomial (O.degree (c i)) 1 with hq
        rw [MvPolynomial.as_sum q]
        refine Submodule.sum_mem _ fun d hd => ih (O.toSyn d) ?_ d rfl _
        rw [← he]
        have hd' : q.coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
        have hne : d ≠ O.degree (c i) := by
          intro hdeq
          apply hd'
          rw [hdeq, hq, MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial, if_pos rfl, hlc1, sub_self]
        have hci : (c i).coeff d ≠ 0 := by
          rw [hq, MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial, if_neg (Ne.symm hne),
            sub_zero] at hd'
          exact hd'
        have hle := MonomialOrder.le_degree (m := O) (MvPolynomial.mem_support_iff.mpr hci)
        exact lt_of_le_of_ne hle (fun h => hne (O.toSyn.injective h))
      · exact Submodule.mem_sup_right ((MvPolynomial.monomial_mem_restrictSupport R).mpr (Or.inl hmem))
  exact key _ e rfl a
end PI.MSC
