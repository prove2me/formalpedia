-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PolyCoef.IsPD.const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:49.730281+00:00
-- url     : https://prove2.me/submissions/e5b656eb-279b-4ff9-9846-88ea6277f6e5

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_InstCompactUG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PolyCoef
open MeasureTheory Matrix
namespace PI.UnitaryGroupMassFormula.PolyCoef
namespace IsPD
theorem _root_.solution {N : ℕ} (c : ℂ) : IsPD (fun _ : UG N => c) :=
  ⟨0, MvPolynomial.C c, fun g => by simp⟩
end IsPD
end PI.UnitaryGroupMassFormula.PolyCoef
