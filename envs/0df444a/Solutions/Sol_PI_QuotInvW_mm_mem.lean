-- Prove2me | solution 1 for PI.QuotInvW.mm_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:20.448743+00:00
-- url     : https://prove2.me/submissions/382c42d4-77c4-44d9-a23c-5698011111c6

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
theorem _root_.solution {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : IsMatGroup G) {a b : MtM m}
    (ha : Matrix.of a ∈ G) (hb : Matrix.of b ∈ G) : Matrix.of (mm a b) ∈ G :=
  hG.2.2.1 _ ha _ hb
end PI.QuotInvW
