-- Prove2me | solution 1 for PI.QuotInvW.measurableSet_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:12:04.10464+00:00
-- url     : https://prove2.me/submissions/a5475e98-b3a0-402e-821c-a499646d5281

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_QuotInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientInvariantMeasurability_MeasurableMmRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal
noncomputable section
open PI PI.QuotInvW
variable {m : ℕ}
namespace PI.QuotInvW
theorem _root_.solution {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : IsMatGroup G) :
    MeasurableSet {x : MtM m | Matrix.of x ∈ G} := by
  have hc : Continuous (fun x : MtM m => (Matrix.of x : Matrix (Fin m) (Fin m) ℂ)) := continuous_id
  exact (hG.1.preimage hc).measurableSet
end PI.QuotInvW
