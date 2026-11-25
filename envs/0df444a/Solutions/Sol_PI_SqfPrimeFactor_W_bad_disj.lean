-- Prove2me | solution 1 for PI.SqfPrimeFactor.W.bad_disj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:59:04.25286+00:00
-- url     : https://prove2.me/submissions/ab93614a-653f-4ff5-b7af-040db752c775

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_MonicDegFnNatDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_SquarefreeCountEstimate
import Theorems.Thm_PI_SqfPrimeFactor_W_irr_dvd_of_dvd_mul
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
theorem _root_.solution {r p p' : ℕ} (hp : r < 2 * p) (hp' : r < 2 * p') (hne : p ≠ p') :
    Disjoint (bad g r p) (bad g r p') := by
  rw [Finset.disjoint_left]
  intro f hf hf'
  obtain ⟨q, h, rfl, hqm, hqd, hqi, hhm, hhd⟩ := mem_bad hf
  obtain ⟨q', h', he, hqm', hqd', hqi', hhm', hhd'⟩ := mem_bad hf'
  have h1 : q ∣ q' := irr_dvd_of_dvd_mul hqi hhm'.ne_zero (by omega) ⟨h, he.symm⟩
  have h2 : q' ∣ q := irr_dvd_of_dvd_mul hqi' hhm.ne_zero (by omega) ⟨h', he⟩
  have := natDegree_le_of_dvd h1 hqm'.ne_zero
  have := natDegree_le_of_dvd h2 hqm.ne_zero
  omega
end PI.SqfPrimeFactor.W
