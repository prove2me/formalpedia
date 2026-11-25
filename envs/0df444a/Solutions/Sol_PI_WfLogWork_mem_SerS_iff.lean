-- Prove2me | solution 1 for PI.WfLogWork.mem_SerS_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:07:25.537777+00:00
-- url     : https://prove2.me/submissions/7c7ebb02-680e-4d40-8cc6-466ffd9982f9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittLogarithm_CoefWfIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DXEqDerivative
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittLogarithm_FormalLogarithmHolds
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WfLogWork
open PI.ExpIntWProof PI.AddIntG.Wk
namespace PI.WfLogWork
theorem _root_.solution {K : Type*} [CommRing K] (S : Subring K) (f : PowerSeries K) :
    (f : MvPowerSeries Unit K) ∈ SerS S Unit ↔ ∀ n, PowerSeries.coeff n f ∈ S := by
  rw [mem_SerS]
  constructor
  · intro h n
    exact h _
  · intro h e
    have he : e = Finsupp.single () (e ()) := by
      ext u
      simp
    rw [he]
    exact h (e ())
end PI.WfLogWork
