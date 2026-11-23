-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BesselLevi.hW_in
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:34:11.861191+00:00
-- url     : https://prove2.me/submissions/d5a5012b-6e5f-479a-92e5-66323857cea0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselLevi
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselLeviAction_MulVecBvecApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BesselLevi
variable {k r : ℕ}
namespace PI.UnitaryGroupMassFormula.BesselLevi
theorem _root_.solution {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {i j : Fin (2 * r + k + 1)} (hi : r ≤ i.val ∧ i.val ≤ r + k) (hj : r ≤ j.val ∧ j.val ≤ r + k) :
    hW k r s i j = s i j := by
  unfold hW
  rw [if_pos ⟨hi, hj⟩]
end PI.UnitaryGroupMassFormula.BesselLevi
