-- Prove2me | solution 1 for PI.TOW.MonoW.stepMonoFactor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:29:26.109807+00:00
-- url     : https://prove2.me/submissions/95b313cd-3c7d-467b-80a8-3c858e8c0cf3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_StepMonoFactor

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
open PI PI.TOW PI.TOW.MonoW
open PI.TO PI.TOW
namespace PI.TOW.MonoW
theorem _root_.solution : StepMonoFactor := by
  intro K _ n' k μ
  simp only [embS, rename_monomial]
  suffices hμ : μ = ∑ t, Finsupp.mapDomain (fun c => (t, c)) (partS μ t) by
    rw [← MvPolynomial.monomial_sum_one, ← hμ]
  ext ⟨t, c⟩
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single t]
  · rw [Finsupp.mapDomain_apply (fun a b h => by simpa using h)]
    simp [partS]
  · intro t' _ ht'
    rw [Finsupp.mapDomain_notin_range]
    rintro ⟨c', hc'⟩
    exact ht' (congrArg Prod.fst hc')
  · simp
end PI.TOW.MonoW
