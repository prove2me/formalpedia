-- Prove2me | solution 1 for PI.EF.PK.gl_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:12.697589+00:00
-- url     : https://prove2.me/submissions/8c902c02-ff0e-491e-8c85-227d11574fc8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronKernelA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF PI.EF.PK
open Complex MeasureTheory intervalIntegral Real
namespace PI.EF.PK
theorem _root_.solution (l : ℝ) : Differentiable ℂ (gl l) := by
  unfold gl
  have h : DifferentiableOn ℂ (fun s : ℂ => cexp (↑l * s)) Set.univ :=
    (by fun_prop : Differentiable ℂ (fun s : ℂ => cexp (↑l * s))).differentiableOn
  have := (Complex.differentiableOn_dslope (s := Set.univ) (c := 0) Filter.univ_mem).2 h
  exact differentiableOn_univ.1 this
end PI.EF.PK
