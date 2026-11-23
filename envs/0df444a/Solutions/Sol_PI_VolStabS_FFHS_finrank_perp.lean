-- Prove2me | solution 1 for PI.VolStabS.FFHS.finrank_perp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:11:23.533678+00:00
-- url     : https://prove2.me/submissions/b42e3131-c377-43ce-b4c0-28641a275373

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFHS
import Theorems.Thm_PI_VolStabS_FFHS_IsSq_lin_apply

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
variable {K : Type} [Field K] {σ : K →+* K}
variable {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K}
namespace PI.VolStabS.FFHS
theorem _root_.solution [FiniteDimensional K V] (hs : IsSq σ h) (e : V) (he : h e e ≠ 0) :
    finrank K (perp hs e) + 1 = finrank K V := by
  have hsurj : Function.Surjective (hs.lin e) := fun c =>
    ⟨(c * (h e e)⁻¹) • e, by rw [IsSq.lin_apply, hs.smul_right, mul_assoc, inv_mul_cancel₀ he,
      mul_one]⟩
  have := LinearMap.finrank_range_add_finrank_ker (hs.lin e)
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, finrank_self] at this
  unfold perp
  omega
end PI.VolStabS.FFHS
