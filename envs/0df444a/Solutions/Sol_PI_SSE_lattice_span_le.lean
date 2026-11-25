-- Prove2me | solution 1 for PI.SSE.lattice_span_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:18:00.084346+00:00
-- url     : https://prove2.me/submissions/9ff24cf5-ea3a-4751-b656-01d72ca5c266

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaDerivNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_Reduce

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex UpperHalfPlane ModularGroup
open scoped MatrixGroups Modular
open PI PI.SSE
namespace PI.SSE
theorem _root_.solution (x y u v : ℂ) (hx : x ∈ PI.lat2 u v) (hy : y ∈ PI.lat2 u v) :
    PI.lat2 x y ≤ PI.lat2 u v := by
  unfold PI.lat2 at *
  rw [AddSubgroup.closure_le]
  rintro z (rfl | rfl) <;> assumption
end PI.SSE
