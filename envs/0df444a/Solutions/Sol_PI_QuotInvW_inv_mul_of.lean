-- Prove2me | solution 1 for PI.QuotInvW.inv_mul_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:20.146179+00:00
-- url     : https://prove2.me/submissions/1e0a5040-17b4-4a85-8b88-ce343efe8d91

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
theorem _root_.solution {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : IsMatGroup G) {a : Matrix (Fin m) (Fin m) ℂ}
    (ha : a ∈ G) : a⁻¹ * a = 1 :=
  mul_eq_one_comm.mp (hG.2.2.2 a ha).2
end PI.QuotInvW
