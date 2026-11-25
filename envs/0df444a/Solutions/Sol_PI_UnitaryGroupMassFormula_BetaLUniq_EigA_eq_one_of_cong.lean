-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BetaLUniq.EigA.eq_one_of_cong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:41:42.086966+00:00
-- url     : https://prove2.me/submissions/fa1f6441-b53b-41d6-9f83-244f00abeb7e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BetaUniqueness_EqZeroOfNormLtOne
import Theorems.Thm_PI_UnitaryGroupMassFormula_BetaLUniq_EigA_eq_zero_of_norm_lt_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BetaLUniq PI.UnitaryGroupMassFormula.BetaLUniq.EigA
variable {E : Type} [Field E] [NumberField E]
namespace PI.UnitaryGroupMassFormula.BetaLUniq.EigA
theorem _root_.solution (μ : E) (g : ℕ) (hg : 3 ≤ g) (hμ : ∀ φ : E →+* ℂ, ‖φ μ‖ = 1)
    (hν : InO ((μ - 1) / (g : E))) : μ = 1 := by
  obtain ⟨o, ho⟩ := hν
  have hg0 : (g : E) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hg' : (3 : ℝ) ≤ g := by exact_mod_cast hg
  have ho0 : o = 0 := by
    apply eq_zero_of_norm_lt_one
    intro φ
    rw [ho, map_div₀, map_sub, map_one, map_natCast, norm_div, Complex.norm_natCast,
      div_lt_one (by positivity)]
    calc ‖φ μ - 1‖ ≤ ‖φ μ‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [hμ φ, norm_one]; norm_num
      _ < g := by linarith
  rw [ho0, map_zero, eq_comm, div_eq_zero_iff] at ho
  rcases ho with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hg0
end PI.UnitaryGroupMassFormula.BetaLUniq.EigA
