-- Prove2me | solution 1 for PI.SqfPrimeFactor.W.T_disj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:56:52.844572+00:00
-- url     : https://prove2.me/submissions/cdc122fc-c727-4cb1-ac4c-9e48c81caac3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_MonicDegFnNatDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_SquarefreeCountEstimate
import Theorems.Thm_PI_SqfPrimeFactor_W_mem_bad

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfPrimeFactor PI.SqfPrimeFactor.W
open PI.SqfLab
variable {g : ℕ} [Fact g.Prime]
namespace PI.SqfPrimeFactor.W
theorem _root_.solution (r p : ℕ) (hp : p ∈ bigPrimes r) (T : Finset (ZMod g)[X])
    (hT : ∀ f ∈ T, Ev g r f) : Disjoint T (bad g r p) := by
  rw [Finset.disjoint_left]
  intro f hfT hfb
  obtain ⟨q, h, rfl, hqm, hqd, hqi, hhm, hhd⟩ := mem_bad hfb
  obtain ⟨hpp, h2p, hp3⟩ := (Finset.mem_filter.1 hp).2
  refine (hT _ hfT).2.2 ⟨q, hqi, dvd_mul_right q h, ?_, ?_, ?_⟩
  · rw [hqd]; exact hpp
  · rw [hqd]; exact h2p
  · rw [hqd]; exact hp3
end PI.SqfPrimeFactor.W
