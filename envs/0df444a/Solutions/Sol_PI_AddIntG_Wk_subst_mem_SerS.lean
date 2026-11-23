-- Prove2me | solution 1 for PI.AddIntG.Wk.subst_mem_SerS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:42.264919+00:00
-- url     : https://prove2.me/submissions/4641716c-9f84-4a15-ac55-b45da7c4d160

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Theorems.Thm_PI_AddIntG_Wk_mvsubst_mem_SerS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AddIntG PI.AddIntG.Wk
namespace PI.AddIntG.Wk
theorem _root_.solution {K : Type*} [CommRing K] (S : Subring K) {τ : Type*} {a : MvPowerSeries τ K}
    {f : PowerSeries K} (ha0 : MvPowerSeries.constantCoeff a = 0) (ha : a ∈ SerS S τ)
    (hf : (f : MvPowerSeries Unit K) ∈ SerS S Unit) : PowerSeries.subst a f ∈ SerS S τ :=
  mvsubst_mem_SerS S (a := fun _ : Unit => a) (fun _ => ha0) (fun _ => ha) hf
end PI.AddIntG.Wk
