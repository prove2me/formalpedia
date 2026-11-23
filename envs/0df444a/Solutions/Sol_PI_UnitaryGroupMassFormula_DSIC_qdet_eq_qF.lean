-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DSIC.qdet_eq_qF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:36:09.560798+00:00
-- url     : https://prove2.me/submissions/04960aad-9cea-4a27-877d-2cc7bb5fc3d0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_CentralScalar
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_QuasiDeterminantConjInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.DSIC
open Finset
open scoped Matrix
namespace PI.UnitaryGroupMassFormula.DSIC
theorem _root_.solution {R : Type*} [Ring R] [Algebra ℂ R] {n : ℕ} (E : Fin n → Fin n → R) (u : ℂ) :
    Formalism.REAL.qdet E u = qF (Formalism.REAL.Tm E) u := rfl
end PI.UnitaryGroupMassFormula.DSIC
