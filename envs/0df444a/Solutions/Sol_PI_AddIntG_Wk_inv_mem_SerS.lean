-- Prove2me | solution 1 for PI.AddIntG.Wk.inv_mem_SerS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:19:58.09319+00:00
-- url     : https://prove2.me/submissions/0d13d677-1f84-4508-87b9-2fb586fdb4a0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Theorems.Thm_PI_AddIntG_Wk_SerS_eq_map
import Theorems.Thm_PI_AddIntG_Wk_constantCoeff_lift

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
theorem _root_.solution {K : Type*} [Field K] (S : Subring K) {σ : Type*} {f : MvPowerSeries σ K}
    (h0 : MvPowerSeries.constantCoeff f = 1) (hf : f ∈ SerS S σ) : f⁻¹ ∈ SerS S σ := by
  obtain ⟨g, rfl⟩ := SerS_eq_map S hf
  have hg : MvPowerSeries.constantCoeff g = 1 :=
    constantCoeff_lift S g (c := 1) (by rw [h0]; rfl)
  have h1 : g * MvPowerSeries.invOfUnit g 1 = 1 :=
    MvPowerSeries.mul_invOfUnit g 1 (by rw [hg]; rfl)
  rw [SerS, RingHom.mem_range]
  refine ⟨MvPowerSeries.invOfUnit g 1, ?_⟩
  symm
  rw [MvPowerSeries.inv_eq_iff_mul_eq_one (by rw [h0]; exact one_ne_zero), ← map_mul, mul_comm, h1,
    map_one]
end PI.AddIntG.Wk
