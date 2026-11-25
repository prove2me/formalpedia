-- Prove2me | solution 1 for PI.VolStabSW.FFHS.perp_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:54:15.048889+00:00
-- url     : https://prove2.me/submissions/9f68d2fb-85d9-4205-94b3-b189b6fd9d4f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFHS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFCnt
import Theorems.Thm_PI_VolStabSW_FFHS_IsSq_sub_right
import Theorems.Thm_PI_VolStabSW_FFHS_mem_perp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.FFHS
open Module
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {σ : K →+* K}
namespace PI.VolStabSW.FFHS
theorem _root_.solution {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K} (hs : IsSq σ h)
    (e x : V) (he : h e e ≠ 0) : x - ((h e e)⁻¹ * h e x) • e ∈ perp hs e := by
  rw [mem_perp, hs.sub_right, hs.smul_right, mul_right_comm, inv_mul_cancel₀ he, one_mul, sub_self]
end PI.VolStabSW.FFHS
