-- Prove2me | solution 1 for PI.WAU.B.fmat_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:15:15.378814+00:00
-- url     : https://prove2.me/submissions/75df0662-d45a-4676-88cf-f4d1808171af

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_KCountable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ConstructionB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU PI.WAU.B
open Formalism.MainNotions.S MeasureTheory NumberField IsDedekindDomain Formalism.UG Matrix PI.WAU.B
open scoped TensorProduct
variable (I : AutInst) {k : ℕ} (m : Fin k → Fin I.n → I.E)
namespace PI.WAU.B
theorem _root_.solution (y : I.Gf) : I.fmat y⁻¹ * I.fmat y = 1 := by
  rw [show I.fmat y⁻¹ * I.fmat y = I.fmat (y⁻¹ * y) from rfl, inv_mul_cancel]
  rfl
end PI.WAU.B
