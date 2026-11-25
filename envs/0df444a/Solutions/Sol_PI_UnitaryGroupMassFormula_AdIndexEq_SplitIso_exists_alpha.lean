-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.SplitIso.exists_alpha
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:36:23.46446+00:00
-- url     : https://prove2.me/submissions/2de43306-3cf5-4077-abd2-865e79b7ff07

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitIso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.AdIndexEq.SplitIso
open scoped TensorProduct
variable {F E K : Type} [Field F] [Field E] [Algebra F E] [Field K] [Algebra F K]
namespace PI.UnitaryGroupMassFormula.AdIndexEq.SplitIso
theorem _root_.solution (σ : E →ₐ[F] E) (hσσ : ∀ a, σ (σ a) = a)
    (hfix : ∀ a, σ a = a → a ∈ (algebraMap F E).range) (h2 : Module.finrank F E = 2) :
    ∃ α : E, α ≠ 0 ∧ σ α = -α := by
  have : ∃ a : E, a ∉ (algebraMap F E).range := by
    by_contra hall
    push Not at hall
    have hr : LinearMap.range (Algebra.linearMap F E) = ⊤ := by
      rw [eq_top_iff]
      intro a _
      obtain ⟨f, rfl⟩ := hall a
      exact ⟨f, rfl⟩
    have := (Algebra.linearMap F E).finrank_range_le
    rw [hr, finrank_top, h2, Module.finrank_self] at this
    omega
  obtain ⟨a, ha⟩ := this
  refine ⟨a - σ a, ?_, ?_⟩
  · intro h0
    exact ha (hfix a (by linear_combination -h0))
  · rw [map_sub, hσσ]; ring
end PI.UnitaryGroupMassFormula.AdIndexEq.SplitIso
