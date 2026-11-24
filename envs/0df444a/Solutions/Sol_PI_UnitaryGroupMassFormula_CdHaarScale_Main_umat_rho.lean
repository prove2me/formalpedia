-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CdHaarScale.Main.umat_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:43:45.590407+00:00
-- url     : https://prove2.me/submissions/f484a81d-c468-4fd6-8687-cdefe6aee6ec

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CdHaarScale
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarScaling_MapEqSelfOfIterate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MeasureTheory.Measure Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CdHaarScale PI.UnitaryGroupMassFormula.CdHaarScale.Main
namespace PI.UnitaryGroupMassFormula.CdHaarScale.Main
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} (π : Fin n ≃ Fin n) (hπ : ∀ i, ε (π i) = ε i)
    (a : Formalism.REAL.UJ ε) :
    PI.CdHaarScale.umat (rho π hπ a) = reindex π π (PI.CdHaarScale.umat a) := rfl
end PI.UnitaryGroupMassFormula.CdHaarScale.Main
