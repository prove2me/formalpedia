-- Prove2me | solution 1 for PI.OmLocU.CntFF.exists_aniso2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:53:49.505875+00:00
-- url     : https://prove2.me/submissions/1a245dd9-6579-462e-b0e9-979c9ae2e4a1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFIn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnitaryOrbits_FFInert2Holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmLocU PI.OmLocU.CntFF
open Module PI.VolStabSW PI.VolStabSW.FFHS
variable {K : Type} [Field K] {σ : K →+* K} {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K}
namespace PI.OmLocU.CntFF
theorem _root_.solution (h2 : ∃ z : K, z + σ z ≠ 0) (hs : IsHS σ h) (x : V) (hx : x ≠ 0) :
    ∃ e, h e e ≠ 0 := by
  by_contra hne
  push_neg at hne
  obtain ⟨z, hz⟩ := h2
  obtain ⟨y, hy⟩ : ∃ y, h x y ≠ 0 := by
    by_contra hy
    push_neg at hy
    exact hx (hs.nondeg x hy)
  have hσσ : σ (σ (h x y)) = h x y := by
    rw [← hs.herm x y, ← hs.herm y x]
  have hxu : h x (x + (z * (h x y)⁻¹) • y) = z * (h x y)⁻¹ * h x y := by
    rw [hs.add_right, hs.smul_right, hne x, zero_add]
  have hyu : h y (x + (z * (h x y)⁻¹) • y) = σ (h x y) := by
    rw [hs.add_right, hs.smul_right, hne y, mul_zero, add_zero, hs.herm x y]
  have key := hne (x + (z * (h x y)⁻¹) • y)
  rw [hs.add_right, hs.smul_right, hs.herm x (x + (z * (h x y)⁻¹) • y),
    hs.herm y (x + (z * (h x y)⁻¹) • y), hxu, hyu, hσσ, inv_mul_cancel_right₀ hy] at key
  exact hz (by rw [add_comm]; exact key)
end PI.OmLocU.CntFF
