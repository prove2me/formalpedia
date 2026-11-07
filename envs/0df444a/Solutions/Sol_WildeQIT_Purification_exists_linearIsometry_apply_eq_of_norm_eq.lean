-- Prove2me | solution 1 for WildeQIT.Purification.exists_linearIsometry_apply_eq_of_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T19:24:46.075542+00:00
-- url     : https://prove2.me/submissions/febc7a14-9189-442f-9b22-391d8b775414

import Mathlib

open Matrix

theorem solution {𝕜 E F : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (f g : E →ₗ[𝕜] F) (h : ∀ v, ‖f v‖ = ‖g v‖) :
    ∃ T : F →ₗᵢ[𝕜] F, ∀ v, T (g v) = f v := by
  have hle : LinearMap.ker g ≤ LinearMap.ker f := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [← norm_eq_zero, h v, hv, norm_zero]
  let L0 : LinearMap.range g →ₗ[𝕜] F :=
    ((LinearMap.ker g).liftQ f hle).comp g.quotKerEquivRange.symm.toLinearMap
  have hL0 : ∀ v, L0 ⟨g v, LinearMap.mem_range_self g v⟩ = f v := by
    intro v
    have : g.quotKerEquivRange.symm ⟨g v, LinearMap.mem_range_self g v⟩
        = Submodule.Quotient.mk v := by
      rw [LinearEquiv.symm_apply_eq]
      ext
      simp [LinearMap.quotKerEquivRange_apply_mk]
    simp only [L0, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  let L : LinearMap.range g →ₗᵢ[𝕜] F :=
    { toLinearMap := L0
      norm_map' := by
        rintro ⟨s, v, rfl⟩
        change ‖L0 ⟨g v, LinearMap.mem_range_self g v⟩‖ = ‖g v‖
        rw [hL0, h] }
  refine ⟨L.extend, fun v => ?_⟩
  have := LinearIsometry.extend_apply L ⟨g v, LinearMap.mem_range_self g v⟩
  simpa [L, hL0] using this
