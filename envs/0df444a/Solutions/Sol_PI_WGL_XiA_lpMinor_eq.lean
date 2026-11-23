-- Prove2me | solution 1 for PI.WGL.XiA.lpMinor_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:06:35.142217+00:00
-- url     : https://prove2.me/submissions/0ea7949c-9b29-4702-8469-b124ab83d860

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_MultisetProdNormLeOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_RowsZStrictMono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.XiA
open Formalism.BasicNotions MvPolynomial
namespace PI.WGL.XiA
theorem _root_.solution {N : ℕ} (s : ℕ) (hr : s ≤ N) (hn : s ≤ N) :
    Formalism.GradedWeylDivisibility.lpMinor ℂ (r := N) (n := N) s hr hn = Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) (Fin.castLE hr) hn := rfl
end PI.WGL.XiA
