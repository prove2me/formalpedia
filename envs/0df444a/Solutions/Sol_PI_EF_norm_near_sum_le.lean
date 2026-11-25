-- Prove2me | solution 1 for PI.EF.norm_near_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:37:26.853929+00:00
-- url     : https://prove2.me/submissions/9242e1b6-71c6-4852-842c-b6ea3fe44f81

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LogDerivBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex DirichletCharacter
namespace PI.EF
theorem _root_.solution {C : ℝ} (hC : ZerosWindowWith C) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (s : ℂ) {d : ℝ} (hd : 0 < d)
    (h : ∀ ρ ∈ ZerosNear χ s.im, d ≤ ‖s - ρ‖) :
    ‖∑ᶠ ρ ∈ ZerosNear χ s.im, (mult χ ρ : ℂ) / (s - ρ)‖ ≤
      C * Real.log (N * (|s.im| + 2)) / d := by
  have hf := (hC N χ hχ s.im).1
  rw [finsum_mem_eq_finite_toFinset_sum _ hf]
  calc ‖∑ ρ ∈ hf.toFinset, (mult χ ρ : ℂ) / (s - ρ)‖
        ≤ ∑ ρ ∈ hf.toFinset, ‖(mult χ ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ hf.toFinset, (mult χ ρ : ℝ) / d := by
        apply Finset.sum_le_sum
        intro ρ hρ
        rw [norm_div, Complex.norm_natCast]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hd (h ρ ((Set.Finite.mem_toFinset hf).mp hρ))
    _ = (∑ ρ ∈ hf.toFinset, (mult χ ρ : ℝ)) / d := by rw [Finset.sum_div]
    _ ≤ C * Real.log (N * (|s.im| + 2)) / d := by
        apply div_le_div_of_nonneg_right _ hd.le
        rw [← finsum_mem_eq_finite_toFinset_sum _ hf]
        exact (hC N χ hχ s.im).2
end PI.EF
