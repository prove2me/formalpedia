-- Prove2me | solution 1 for PI.FJMB.exists_support_of_killS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:38:38.147845+00:00
-- url     : https://prove2.me/submissions/b0e148ce-3467-45df-bf5e-c374798faf71

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurDiag
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurCauchy

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Classical
open PI PI.FJMB
variable {σ : Type*}
namespace PI.FJMB
theorem _root_.solution {S : Set σ} {P : MvPolynomial σ ℂ} (h : aeval (killS S) P ≠ 0) :
    ∃ e ∈ P.support, ∀ v ∈ S, e v = 0 := by
  by_contra hne
  push_neg at hne
  apply h
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine Finset.sum_eq_zero fun e he => ?_
  obtain ⟨v, hvS, hv⟩ := hne e he
  rw [aeval_monomial, Finsupp.prod]
  refine mul_eq_zero_of_right _ ?_
  refine Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hv) ?_
  simp [killS, hvS, hv]
end PI.FJMB
