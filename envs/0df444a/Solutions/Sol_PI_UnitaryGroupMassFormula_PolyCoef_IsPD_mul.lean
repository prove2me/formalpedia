-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PolyCoef.IsPD.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:45.317928+00:00
-- url     : https://prove2.me/submissions/9be6e292-8a30-4044-a198-b7c8f901c513

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
theorem _root_.solution {N : ℕ} {f f' : UG N → ℂ} (hf : IsPD f) (hf' : IsPD f') : IsPD (fun g => f g * f' g) := by
  obtain ⟨k, P, hP⟩ := hf
  obtain ⟨k', P', hP'⟩ := hf'
  refine ⟨k + k', P * P', fun g => ?_⟩
  simp only [map_mul, ← hP g, ← hP' g]
  ring
end IsPD
end PI.UnitaryGroupMassFormula.PolyCoef
