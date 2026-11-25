-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.coe_rankOneGL_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:42:53.755182+00:00
-- url     : https://prove2.me/submissions/7887735b-874e-4f45-ad0a-bb69db9b7370

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
    (((rankOneUnitGL p q c d h)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = 1 + d • vecMulVec p q := rfl
end PI.UnitaryGroupMassFormula.ScXuExists
