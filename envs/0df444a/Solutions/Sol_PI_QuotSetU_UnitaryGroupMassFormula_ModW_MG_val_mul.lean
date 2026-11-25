-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.ModW.MG.val_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:57:15.890594+00:00
-- url     : https://prove2.me/submissions/111af397-f4dd-4869-ab4d-a67536672576

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ModBase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open scoped ENNReal NNReal
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.ModW
open PI
variable {m : ℕ}
variable {G : Set (Matrix (Fin m) (Fin m) ℂ)} {hG : IsMatGroup G}
open PI.QuotSetU.UnitaryGroupMassFormula.ModW.MG
namespace PI.QuotSetU.UnitaryGroupMassFormula.ModW.MG
theorem _root_.solution (x y : MG G hG) : (x * y).val = lmulQ x.toM y.val := rfl
end PI.QuotSetU.UnitaryGroupMassFormula.ModW.MG
