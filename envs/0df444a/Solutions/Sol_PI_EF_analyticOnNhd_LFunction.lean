-- Prove2me | solution 1 for PI.EF.analyticOnNhd_LFunction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:14.106675+00:00
-- url     : https://prove2.me/submissions/9a7bed94-d08d-4bf8-90fe-797710631e50

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
theorem _root_.solution {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    AnalyticOnNhd ℂ (LFunction χ) {(1 : ℂ)}ᶜ := by
  exact DifferentiableOn.analyticOnNhd
    (fun z hz => (differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt)
    isOpen_compl_singleton
end PI.EF
