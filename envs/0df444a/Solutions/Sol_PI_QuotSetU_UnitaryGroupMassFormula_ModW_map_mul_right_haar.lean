-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.ModW.map_mul_right_haar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:30:01.260892+00:00
-- url     : https://prove2.me/submissions/03495976-1604-4697-ac92-a960931e600a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ModBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ModCore

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open scoped ENNReal NNReal Pointwise
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.ModW
open PI MG
variable {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} {hG : IsMatGroup G}
namespace PI.QuotSetU.UnitaryGroupMassFormula.ModW
theorem _root_.solution (g : MG G hG) :
    (Measure.haar : Measure (MG G hG)).map (· * g) =
      Measure.modularCharacterFun g • (Measure.haar : Measure (MG G hG)) := by
  rw [Measure.modularCharacterFun_eq_haarScalarFactor (Measure.haar : Measure (MG G hG)) g]
  exact Measure.isMulLeftInvariant_eq_smul_of_regular _ _
end PI.QuotSetU.UnitaryGroupMassFormula.ModW
