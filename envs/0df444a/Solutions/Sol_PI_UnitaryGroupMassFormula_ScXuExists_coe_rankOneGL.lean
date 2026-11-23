-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.coe_rankOneGL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:17.218406+00:00
-- url     : https://prove2.me/submissions/9e2e8403-b38e-4c51-96c8-5c775250818e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinBase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists
open Matrix
variable {R : Type} [CommRing R] {n : ℕ}
namespace PI.UnitaryGroupMassFormula.ScXuExists
theorem _root_.solution (p q : Fin n → R) (c d : R) (h : c + d + c * d * (q ⬝ᵥ p) = 0) :
    ((rankOneUnitGL p q c d h : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = 1 + c • vecMulVec p q := rfl
end PI.UnitaryGroupMassFormula.ScXuExists
