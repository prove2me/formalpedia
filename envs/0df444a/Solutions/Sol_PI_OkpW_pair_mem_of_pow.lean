-- Prove2me | solution 1 for PI.OkpW.pair_mem_of_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:59:32.956473+00:00
-- url     : https://prove2.me/submissions/430a2c72-8e7b-424c-99a9-4a9d367667a8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_TeichNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_UltrametricPairEstimate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
noncomputable section
open PI PI.OkpW
variable {K : Type} [Field K] [NumberField K] {p : ℕ} [hp : Fact p.Prime]
namespace PI.OkpW
theorem _root_.solution (t : ℂ_[p]) (ht : t ^ (p ^ 2) = t) :
    (t, t ^ p) ∈ Subring.closure (gens p) := by
  by_cases h0 : t = 0
  · subst h0
    have e : ((0 : ℂ_[p]), (0 : ℂ_[p]) ^ p) = 0 := by
      simp [zero_pow hp.out.ne_zero]
    rw [e]
    exact zero_mem _
  · apply Subring.subset_closure
    refine ⟨t, ?_, rfl⟩
    have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.out.pos
    have e : t ^ (p ^ 2 - 1) * t = 1 * t := by
      rw [← pow_succ, Nat.sub_add_cancel h1, ht, one_mul]
    exact mul_right_cancel₀ h0 e
end PI.OkpW
