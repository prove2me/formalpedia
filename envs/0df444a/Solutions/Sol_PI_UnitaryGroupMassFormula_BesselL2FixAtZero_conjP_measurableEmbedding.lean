-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BesselL2FixAtZero.conjP_measurableEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:44:22.007377+00:00
-- url     : https://prove2.me/submissions/623c8c24-7525-41af-b53e-a4551a26013c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselL2FixAtZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselSquareIntegrable_SchurHpkAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_Closed
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselSquareIntegrable_SchurHpk
import Theorems.Thm_PI_UnitaryGroupMassFormula_BesselL2FixAtZero_conjP_isClosedEmbedding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BesselL2FixAtZero
open MeasureTheory Matrix Topology
open scoped InnerProductSpace ENNReal
open PI.UpqRep PI.BesselL2FixAtZero
variable {n : ℕ} (ε : Fin n → Bool) (P : Matrix (Fin n) (Fin n) ℂ)
namespace PI.UnitaryGroupMassFormula.BesselL2FixAtZero
theorem _root_.solution (hP : IsUnit P) : MeasurableEmbedding (conjPrime₂ ε P) :=
  (conjP_isClosedEmbedding ε P hP).measurableEmbedding
end PI.UnitaryGroupMassFormula.BesselL2FixAtZero
