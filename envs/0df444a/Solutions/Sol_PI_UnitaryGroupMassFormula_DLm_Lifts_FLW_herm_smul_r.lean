-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DLm.Lifts.FLW.herm_smul_r
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:39:27.420381+00:00
-- url     : https://prove2.me/submissions/6a0bdbe3-8642-46e1-938b-e37233cf6349

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFramesCut
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittExtensionTheorem
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_ReverseCauchySchwarzHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFlWitt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped Matrix
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.DLm PI.UnitaryGroupMassFormula.DLm.Lifts
open PI.UnitaryGroupMassFormula.DLm.Lifts.FLW
variable {n : ℕ}
namespace PI.UnitaryGroupMassFormula.DLm.Lifts.FLW
theorem _root_.solution (H : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (u w : Fin n → ℂ) :
    herm H u (c • w) = star c * herm H u w := by
  simp [herm, star_smul, smul_dotProduct, smul_eq_mul]
end PI.UnitaryGroupMassFormula.DLm.Lifts.FLW
