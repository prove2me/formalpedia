-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmStar.arg_rev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:18:16.504084+00:00
-- url     : https://prove2.me/submissions/45dfc9fa-601d-44bf-b6f6-09014861ba85

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
theorem _root_.solution {t : ℕ} (w : ℂ) (j : Fin t) :
    star (w - (((Fin.rev j : Fin t) : ℕ) : ℂ)) = star w - (t : ℂ) + 1 + ((j : ℕ) : ℂ) := by
  have hj := j.isLt
  rw [star_sub, Fin.val_rev]
  have e : star (((t - (↑j + 1) : ℕ)) : ℂ) = ((t - (↑j + 1) : ℕ) : ℂ) := by simp
  rw [e, Nat.cast_sub (by omega)]
  push_cast
  ring
end PI.UnitaryGroupMassFormula.QmStar
