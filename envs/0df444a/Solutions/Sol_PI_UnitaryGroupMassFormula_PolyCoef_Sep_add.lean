-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PolyCoef.Sep.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:20.852963+00:00
-- url     : https://prove2.me/submissions/b6f0bfca-fb89-4d1d-b2ca-704ba5ebda05

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
namespace Sep
theorem _root_.solution {N : ℕ} {f f' : UG N → ℂ} (hf : Sep f) (hf' : Sep f') : Sep (fun g => f g + f' g) := by
  obtain ⟨ι, _, a, b, ha, hb, he⟩ := hf
  obtain ⟨ι', _, a', b', ha', hb', he'⟩ := hf'
  refine ⟨ι ⊕ ι', inferInstance, Sum.elim a a', Sum.elim b b', ?_, ?_, fun h y => ?_⟩
  · rintro (i | i); exacts [ha i, ha' i]
  · rintro (i | i); exacts [hb i, hb' i]
  · simp [Fintype.sum_sum_type, he, he']
end Sep
end PI.UnitaryGroupMassFormula.PolyCoef
