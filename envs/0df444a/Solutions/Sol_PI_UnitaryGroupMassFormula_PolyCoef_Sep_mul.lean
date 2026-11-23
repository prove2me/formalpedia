-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PolyCoef.Sep.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:50.549626+00:00
-- url     : https://prove2.me/submissions/5e0d417f-e60b-4f77-b9c5-a559612dba1a

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_InstCompactUG
import Theorems.Thm_PI_UnitaryGroupMassFormula_PolyCoef_IsPD_mul

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
theorem _root_.solution {N : ℕ} {f f' : UG N → ℂ} (hf : Sep f) (hf' : Sep f') : Sep (fun g => f g * f' g) := by
  obtain ⟨ι, _, a, b, ha, hb, he⟩ := hf
  obtain ⟨ι', _, a', b', ha', hb', he'⟩ := hf'
  refine ⟨ι × ι', inferInstance, fun p g => a p.1 g * a' p.2 g, fun p g => b p.1 g * b' p.2 g,
    fun p => (ha p.1).mul (ha' p.2), fun p => (hb p.1).mul (hb' p.2), fun h y => ?_⟩
  show f (h⁻¹ * y) * f' (h⁻¹ * y) = ∑ p : ι × ι', (a p.1 h * a' p.2 h) * (b p.1 y * b' p.2 y)
  rw [he, he', Fintype.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end Sep
end PI.UnitaryGroupMassFormula.PolyCoef
