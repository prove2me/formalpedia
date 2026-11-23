-- Prove2me | solution 1 for PI.EF.mem_rect_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:49.89555+00:00
-- url     : https://prove2.me/submissions/26a75067-fe13-40ac-9747-9e2bc97fc2eb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_ExplicitFormulaFromGluing
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_Contour

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
open Complex Filter Topology Set DirichletCharacter
namespace PI.EF
theorem _root_.solution {x₀ x₁ y₀ y₁ : ℝ} {s : ℂ} :
    s ∈ rect x₀ x₁ y₀ y₁ ↔ (x₀ ≤ s.re ∧ s.re ≤ x₁) ∧ (y₀ ≤ s.im ∧ s.im ≤ y₁) := by
  rw [rect, Complex.mem_reProdIm]
  simp only [Set.mem_Icc]
end PI.EF
