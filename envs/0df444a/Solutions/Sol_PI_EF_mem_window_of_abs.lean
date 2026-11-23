-- Prove2me | solution 1 for PI.EF.mem_window_of_abs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:49.910241+00:00
-- url     : https://prove2.me/submissions/b69d5dd0-50b0-48d1-a8d3-7ab7fce32369

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeight

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
open DirichletCharacter
namespace PI.EF
theorem _root_.solution {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {ρ : ℂ} {t : ℝ}
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hL : LFunction χ ρ = 0) (h : |(|ρ.im|) - t| ≤ 1) :
    ρ ∈ ZerosNear χ t ∪ ZerosNear χ (-t) := by
  rcases le_or_gt 0 ρ.im with hi | hi
  · left
    refine ⟨h0, h1, ?_, hL⟩
    rwa [abs_of_nonneg hi] at h
  · right
    refine ⟨h0, h1, ?_, hL⟩
    rw [abs_of_neg hi] at h
    rw [show ρ.im - -t = -(-ρ.im - t) by ring, abs_neg]
    exact h
end PI.EF
