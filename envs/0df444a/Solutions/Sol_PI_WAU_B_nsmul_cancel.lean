-- Prove2me | solution 1 for PI.WAU.B.nsmul_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:04:29.504666+00:00
-- url     : https://prove2.me/submissions/a37b9170-efdb-47b4-a2c1-7cbf4247a603

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_KCountable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ConstructionB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU PI.WAU.B
open Formalism.MainNotions.S MeasureTheory NumberField IsDedekindDomain Formalism.UG Matrix PI.WAU.B
open scoped TensorProduct
namespace PI.WAU.B
theorem _root_.solution {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {N : ℕ}
    (hN : 0 < N) {v w : V} (h : N • v = N • w) : v = w := by
  have h' : (N : K) • v = (N : K) • w := by
    rw [Nat.cast_smul_eq_nsmul K, Nat.cast_smul_eq_nsmul K]
    exact h
  exact smul_right_injective V (Nat.cast_ne_zero.mpr hN.ne') h'
end PI.WAU.B
