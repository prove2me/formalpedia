-- Prove2me | solution 1 for PI.Mk.good_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:51.140911+00:00
-- url     : https://prove2.me/submissions/1c8c392a-073d-4dcb-a8d9-e6ad64f62f0f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSumStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_CharpolyDvdOfPowEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Mk
open Polynomial Matrix
namespace PI.Mk
theorem _root_.solution (ℓ : ℕ) (p q : ℚ[X]) (hp : Good ℓ p) (hq : Good ℓ q) : Good ℓ (p * q) := by
  obtain ⟨hpm, y, hy1, hy2, hy3⟩ := hp
  obtain ⟨hqm, z, hz1, hz2, hz3⟩ := hq
  have hdeg : (p * q).natDegree = p.natDegree + q.natDegree := hpm.natDegree_mul hqm
  refine ⟨hpm.mul hqm, y + z, ?_, ?_, ?_⟩
  · rw [hdeg, mul_add]; exact add_le_add hy1 hz1
  · rw [hpm.nextCoeff_mul hqm, hdeg]; push_cast; linear_combination hy2 + hz2
  · intro h0
    have hy : y = 0 := by omega
    have hz : z = 0 := by omega
    rw [hdeg, pow_add]
    conv_lhs => rw [hy3 hy, hz3 hz]
end PI.Mk
