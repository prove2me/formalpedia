-- Prove2me | solution 1 for PI.EF.Loc.refl_center
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:36:44.953652+00:00
-- url     : https://prove2.me/submissions/86da6056-7cee-4246-87c9-2ca2bccfd8f1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_NormLogDerivReflLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF PI.EF.Loc
open Complex Metric Set Filter Topology ComplexConjugate
namespace PI.EF.Loc
theorem _root_.solution {s₀ ρ : ℂ} {R : ℝ} (hR : 0 < R) : refl s₀ R ρ s₀ = R := by
  have h : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  unfold refl
  rw [sub_self, mul_zero, sub_zero, pow_two, mul_div_assoc, div_self h, mul_one]
end PI.EF.Loc
