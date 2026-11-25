-- Prove2me | solution 1 for PI.VolStabW.FFHS.perp_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:59:24.575921+00:00
-- url     : https://prove2.me/submissions/42044b4c-e869-43cb-8076-5492aacd9c00

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFHS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFCnt
import Theorems.Thm_PI_VolStabW_FFHS_IsSq_sub_right
import Theorems.Thm_PI_VolStabW_FFHS_mem_perp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.FFHS
open Module
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {σ : K →+* K}
namespace PI.VolStabW.FFHS
theorem _root_.solution {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K} (hs : IsSq σ h)
    (e x : V) (he : h e e ≠ 0) : x - ((h e e)⁻¹ * h e x) • e ∈ perp hs e := by
  have : (h e e)⁻¹ * h e x * h e e = h e x := by
    rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ he, one_mul]
  rw [mem_perp, hs.sub_right, hs.smul_right, this, sub_self]
end PI.VolStabW.FFHS
