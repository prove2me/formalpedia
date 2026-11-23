-- Prove2me | solution 1 for PI.EF.Loc.hasDerivAt_refl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:12.112156+00:00
-- url     : https://prove2.me/submissions/0e40642e-bb57-415c-b2cd-06da01e4a3e6

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
theorem _root_.solution (s₀ : ℂ) (R : ℝ) (ρ z : ℂ) :
    HasDerivAt (refl s₀ R ρ) (-(conj (ρ - s₀) * 1) / R) z :=
  ((((hasDerivAt_id' z).sub_const s₀).const_mul (conj (ρ - s₀))).const_sub ((R : ℂ) ^ 2)).div_const (R : ℂ)
end PI.EF.Loc
