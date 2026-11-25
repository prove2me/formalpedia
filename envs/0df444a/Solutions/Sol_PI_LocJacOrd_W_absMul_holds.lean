-- Prove2me | solution 1 for PI.LocJacOrd.W.absMul_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:52:25.040348+00:00
-- url     : https://prove2.me/submissions/65d5ac05-bb05-46b8-84a8-483163651d17

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_AbsVNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_SecondCountableFv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocJacOrd PI.LocJacOrd.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacOrd
open scoped TensorProduct Classical
namespace PI.LocJacOrd.W
theorem _root_.solution : AbsMul := fun v => ⟨Ar.absV_mul v, Ar.absV_one v, fun x hx => by
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  simp only [absV, dif_neg hx']
  exact zpow_pos (lt_of_le_of_ne (Nat.cast_nonneg _) (Ar.absNorm_ne_zero v).symm) _⟩
end PI.LocJacOrd.W
