-- Prove2me | solution 2 for P2M_PI_QuotSetU_UnitaryGroupMassFormula_ModW_MG_val_mul__7724171e7634
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:18:39.518894+00:00
-- url     : https://prove2.me/submissions/341f55ac-397c-4739-a6cd-5b8ef84fa84a

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
theorem _root_.solution (x y : MG G hG) : (x * y).val = rmulQ y.toM x.val := rfl
end PI.QuotSetU.UnitaryGroupMassFormula.ModW.MG
