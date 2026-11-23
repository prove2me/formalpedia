-- Prove2me | solution 1 for PI.AddIntG.Wk.exists_intS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:21.9238+00:00
-- url     : https://prove2.me/submissions/5eea4198-4d49-4f8c-b2f7-7d9f71210fe2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GuLine
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GlueHoldsVar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.AddIntG PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]
namespace PI.AddIntG.Wk
theorem _root_.solution (p : ℕ) [Fact p.Prime] : ∃ S : Subring ℂ_[p], ∀ x, x ∈ S ↔ ‖x‖ ≤ 1 := by
  have hadd : ∀ a b : ℂ_[p], ‖a + b‖ ≤ max ‖a‖ ‖b‖ := by
    first
    | exact fun a b => IsUltrametricDist.norm_add_le_max a b
    | exact fun a b => (IsUltrametricDist.isNonarchimedean_norm (R := ℂ_[p])) a b
  refine ⟨{ carrier := {x | ‖x‖ ≤ 1},
            mul_mem' := fun {a b} ha hb => ?_,
            one_mem' := ?_,
            add_mem' := fun {a b} ha hb => ?_,
            zero_mem' := ?_,
            neg_mem' := fun {a} ha => ?_ }, fun x => by first | exact Iff.rfl | simp⟩
  · change ‖a‖ ≤ 1 at ha
    change ‖b‖ ≤ 1 at hb
    change ‖a * b‖ ≤ 1
    rw [norm_mul]
    nlinarith [norm_nonneg a, norm_nonneg b]
  · change ‖(1 : ℂ_[p])‖ ≤ 1
    simp
  · change ‖a‖ ≤ 1 at ha
    change ‖b‖ ≤ 1 at hb
    change ‖a + b‖ ≤ 1
    exact (hadd a b).trans (max_le ha hb)
  · change ‖(0 : ℂ_[p])‖ ≤ 1
    simp
  · change ‖a‖ ≤ 1 at ha
    change ‖-a‖ ≤ 1
    rwa [norm_neg]
end PI.AddIntG.Wk
