-- Prove2me | solution 1 for PI.EF.Loc.differentiable_refl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:08.731801+00:00
-- url     : https://prove2.me/submissions/35bbe61b-61c1-4b1b-ab02-6d4b54399523

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_NormLogDerivReflLe
import Theorems.Thm_PI_EF_Loc_hasDerivAt_refl

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
theorem _root_.solution (s₀ : ℂ) (R : ℝ) (ρ : ℂ) : Differentiable ℂ (refl s₀ R ρ) :=
  fun z => (hasDerivAt_refl s₀ R ρ z).differentiableAt
end PI.EF.Loc
