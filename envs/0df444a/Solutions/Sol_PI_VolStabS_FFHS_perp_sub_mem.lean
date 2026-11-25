-- Prove2me | solution 1 for PI.VolStabS.FFHS.perp_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:50:48.693579+00:00
-- url     : https://prove2.me/submissions/0d1fba21-541c-496b-81a6-f098fb5f0e95

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFHS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFCnt
import Theorems.Thm_PI_VolStabS_FFHS_IsSq_sub_right
import Theorems.Thm_PI_VolStabS_FFHS_mem_perp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS PI.VolStabS.FFHS
open Module
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {σ : K →+* K}
namespace PI.VolStabS.FFHS
theorem _root_.solution {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K} (hs : IsSq σ h)
    (e x : V) (he : h e e ≠ 0) : x - ((h e e)⁻¹ * h e x) • e ∈ perp hs e := by
  rw [mem_perp, hs.sub_right, hs.smul_right]
  rw [mul_comm (h e e)⁻¹ (h e x), mul_assoc, inv_mul_cancel₀ he, mul_one, sub_self]
end PI.VolStabS.FFHS
