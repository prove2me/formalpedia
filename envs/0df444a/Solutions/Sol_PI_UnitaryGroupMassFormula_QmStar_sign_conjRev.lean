-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmStar.sign_conjRev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:25.722005+00:00
-- url     : https://prove2.me/submissions/c4fe0fd9-dfcd-48c4-80eb-42234d4361cc

import Definitions.Def_Formalism_PeriodIntegrals_QmStar
import Definitions.Def_Formalism_PeriodIntegrals_QmRowForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerProductCast_OfFnProdIntCast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmStar
namespace PI.UnitaryGroupMassFormula.QmStar
theorem _root_.solution {t : ℕ} (σ : Equiv.Perm (Fin t)) :
    Equiv.Perm.sign (conjRev t σ) = Equiv.Perm.sign σ := by
  simp only [conjRev, Equiv.coe_fn_mk, Equiv.Perm.sign_mul]
  rw [mul_comm, ← mul_assoc, Int.units_mul_self, one_mul]
end PI.UnitaryGroupMassFormula.QmStar
