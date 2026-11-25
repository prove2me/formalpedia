-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.exists_closest
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:59:37.739163+00:00
-- url     : https://prove2.me/submissions/a486f0e1-e3ce-41a0-8f6b-068ccd612454

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtC
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtE
import Theorems.Thm_P2M_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_sub_le_max__b9ad733dbc67


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution {M : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hM : FiniteDimensional ℚ_[p] M) (x : PadicAlgCl p) :
    ∃ m0 ∈ M, ∀ m ∈ M, ‖x - m0‖ ≤ ‖x - m‖ := by
  have : ProperSpace M := FiniteDimensional.proper ℚ_[p] M
  have hc : IsCompact (Metric.closedBall (0 : M) ‖x‖) := isCompact_closedBall 0 ‖x‖
  have hcont : Continuous (fun m : M => ‖x - (m : PadicAlgCl p)‖) :=
    (continuous_const.sub continuous_subtype_val).norm
  have hne : (Metric.closedBall (0 : M) ‖x‖).Nonempty :=
    ⟨0, Metric.mem_closedBall_self (norm_nonneg x)⟩
  obtain ⟨m0, hm0, hmin⟩ := hc.exists_isMinOn hne hcont.continuousOn
  have hmin' : ∀ m : M, m ∈ Metric.closedBall (0 : M) ‖x‖ →
      ‖x - (m0 : PadicAlgCl p)‖ ≤ ‖x - (m : PadicAlgCl p)‖ := fun m hm => hmin hm
  have hle0 : ‖x - (m0 : PadicAlgCl p)‖ ≤ ‖x‖ := by
    have h2 := hmin' 0 (Metric.mem_closedBall_self (norm_nonneg x))
    rwa [ZeroMemClass.coe_zero, sub_zero] at h2
  refine ⟨m0, m0.2, fun m hm => ?_⟩
  by_cases hmx : ‖m‖ ≤ ‖x‖
  · exact hmin' ⟨m, hm⟩ (by rw [mem_closedBall_zero_iff]; exact hmx)
  · rw [not_le] at hmx
    refine hle0.trans ?_
    by_contra hlt
    rw [not_le] at hlt
    have e : m = x - (x - m) := by ring
    have h3 : ‖m‖ ≤ max ‖x‖ ‖x - m‖ := by
      conv_lhs => rw [e]
      exact UnramifiedExtensions.norm_sub_le_max' _ _
    exact absurd (h3.trans (max_le le_rfl hlt.le)) (not_le.2 hmx)
end ReciprocityTheory.DiscreteGroups.LocalClassField
