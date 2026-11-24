-- Prove2me | solution 1 for PI.SlopeSteps.nabla_operator_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:43.057113+00:00
-- url     : https://prove2.me/submissions/aa93bc67-78b9-480a-97bf-39538ddb3b2f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_NablaBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_NablaOperatorBasis
import Theorems.Thm_Formalism_L2_DIV_we_nabla_fg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.SlopeSteps
open MvPolynomial Formalism.GradedWeylDivisibility
namespace PI.SlopeSteps
theorem _root_.solution : NablaBasis := by
  intro N ν
  have hfg := Formalism.L2.DIV.we_nabla_fg N N ν
  have : Module.Finite ℤ (dualWeyl ℤ N N ν) := Module.Finite.iff_fg.mpr hfg
  exact ⟨_, ⟨(Module.Free.chooseBasis ℤ (dualWeyl ℤ N N ν)).reindex (Fintype.equivFin _)⟩⟩
end PI.SlopeSteps
