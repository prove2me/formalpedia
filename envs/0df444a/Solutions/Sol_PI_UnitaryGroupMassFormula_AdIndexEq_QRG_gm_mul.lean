-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.QRG.gm_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:36:17.03097+00:00
-- url     : https://prove2.me/submissions/7372bdce-df69-4bac-bb1b-ec953969cda9

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.AdIndexEq.QRG
open Matrix Formalism.UG
variable {K : Type} [Field K] {n : ℕ}
variable (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K)
namespace PI.UnitaryGroupMassFormula.AdIndexEq.QRG
theorem _root_.solution (g g' : UJ σ J) : gm σ J (g * g') = gm σ J g * gm σ J g' := rfl
end PI.UnitaryGroupMassFormula.AdIndexEq.QRG
