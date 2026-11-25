-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BesselLevi.hW_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:37:25.477108+00:00
-- url     : https://prove2.me/submissions/8d3f00de-ddca-4f35-88da-a5400540efe1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselLevi
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselLeviAction_MulVecBvecApply
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_hW_col_out
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_mulVec_bvec_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselLevi_bvec_apply

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
    (c : Fin (2 * r + k + 1)) (hc : c.val < r ∨ r + k < c.val) : hW k r s *ᵥ bvec c = bvec c := by
  ext p
  rw [mulVec_bvec_apply, bvec_apply, hW_col_out p c hc]
end PI.UnitaryGroupMassFormula.BesselLevi
