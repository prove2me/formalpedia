-- Prove2me | solution 1 for PettisIntegral.exists_continuousLinearMap_hasPettisIntegral_apply
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:31:44.847683+00:00
-- url     : https://prove2.me/submissions/519daf3f-fa16-431c-ad75-0d6167219e69

import Mathlib
import Definitions.Def_PettisIntegral_Basic

open MeasureTheory

set_option autoImplicit false

open PettisIntegral

theorem solution {𝕜 H X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] [MeasurableSpace X]
    (μ : Measure X) (f : X → H →L[𝕜] H)
    (hmeas : ∀ u : H, WeaklyMeasurable 𝕜 μ (fun x => f x u))
    (hint : Integrable (fun x => ‖f x‖) μ) :
    ∃ T : H →L[𝕜] H, (∀ u : H, HasPettisIntegral 𝕜 μ (fun x => f x u) (T u)) ∧
      ‖T‖ ≤ ∫ x, ‖f x‖ ∂μ := by
  classical
  -- weak integrability of `x ↦ f x u`
  have hwi : ∀ u : H, ∀ φ : StrongDual 𝕜 H, Integrable (fun x => φ (f x u)) μ := by
    intro u φ
    refine Integrable.mono' (hint.mul_const (‖φ‖ * ‖u‖)) (hmeas u φ).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    calc ‖φ (f x u)‖ ≤ ‖φ‖ * ‖f x u‖ := φ.le_opNorm _
      _ ≤ ‖φ‖ * (‖f x‖ * ‖u‖) := by gcongr; exact (f x).le_opNorm u
      _ = ‖f x‖ * (‖φ‖ * ‖u‖) := by ring
  have hJ : ∀ u w : H, Integrable (fun x => inner 𝕜 w (f x u)) μ := by
    intro u w
    simpa using hwi u (innerSL 𝕜 w)
  have hptw : ∀ u w : H, ∀ x : X, ‖inner 𝕜 (f x u) w‖ ≤ ‖f x‖ * (‖u‖ * ‖w‖) := by
    intro u w x
    calc ‖inner 𝕜 (f x u) w‖ ≤ ‖f x u‖ * ‖w‖ := norm_inner_le_norm _ _
      _ ≤ (‖f x‖ * ‖u‖) * ‖w‖ := by gcongr; exact (f x).le_opNorm u
      _ = ‖f x‖ * (‖u‖ * ‖w‖) := by ring
  have hI : ∀ u w : H, Integrable (fun x => inner 𝕜 (f x u) w) μ := by
    intro u w
    have h1 : AEMeasurable (fun x => (starRingEnd 𝕜) ((innerSL 𝕜 w) (f x u))) μ :=
      RCLike.continuous_conj.measurable.comp_aemeasurable (hmeas u (innerSL 𝕜 w))
    refine Integrable.mono' (hint.mul_const (‖u‖ * ‖w‖)) ?_
      (Filter.Eventually.of_forall (hptw u w))
    refine (h1.congr ?_).aestronglyMeasurable
    refine Filter.Eventually.of_forall (fun x => ?_)
    simp [inner_conj_symm]
  have hbound : ∀ u w : H,
      ‖∫ x, inner 𝕜 (f x u) w ∂μ‖ ≤ (‖u‖ * ∫ x, ‖f x‖ ∂μ) * ‖w‖ := by
    intro u w
    calc ‖∫ x, inner 𝕜 (f x u) w ∂μ‖ ≤ ∫ x, ‖f x‖ * (‖u‖ * ‖w‖) ∂μ :=
          norm_integral_le_of_norm_le (hint.mul_const _)
            (Filter.Eventually.of_forall (hptw u w))
      _ = (‖u‖ * ∫ x, ‖f x‖ ∂μ) * ‖w‖ := by rw [integral_mul_const]; ring
  have hC0 : 0 ≤ ∫ x, ‖f x‖ ∂μ := integral_nonneg (fun x => norm_nonneg _)
  -- the continuous linear forms `w ↦ ∫ ⟪f x u, w⟫ dμ`
  let ℓ : H → StrongDual 𝕜 H := fun u =>
    LinearMap.mkContinuous
      { toFun := fun w => ∫ x, inner 𝕜 (f x u) w ∂μ
        map_add' := fun w₁ w₂ => by
          simp only [inner_add_right]
          exact integral_add (hI u w₁) (hI u w₂)
        map_smul' := fun c w => by
          simp only [inner_smul_right, smul_eq_mul, RingHom.id_apply]
          exact integral_const_mul c _ }
      (‖u‖ * ∫ x, ‖f x‖ ∂μ) (hbound u)
  have hℓ : ∀ u w, ℓ u w = ∫ x, inner 𝕜 (f x u) w ∂μ := fun u w => rfl
  have hℓn : ∀ u, ‖ℓ u‖ ≤ ‖u‖ * ∫ x, ‖f x‖ ∂μ := fun u =>
    LinearMap.mkContinuous_norm_le _ (mul_nonneg (norm_nonneg _) hC0) _
  -- Riesz representation
  let A : H → H := fun u => (InnerProductSpace.toDual 𝕜 H).symm (ℓ u)
  have hA : ∀ u w, inner 𝕜 w (A u) = ∫ x, inner 𝕜 w (f x u) ∂μ := by
    intro u w
    have h : inner 𝕜 (A u) w = ∫ x, inner 𝕜 (f x u) w ∂μ := by
      simp only [A, InnerProductSpace.toDual_symm_apply, hℓ]
    rw [← inner_conj_symm, h, ← integral_conj]
    simp only [inner_conj_symm]
  have hAadd : ∀ u₁ u₂, A (u₁ + u₂) = A u₁ + A u₂ := by
    intro u₁ u₂
    refine ext_inner_left 𝕜 (fun w => ?_)
    rw [inner_add_right, hA, hA, hA, ← integral_add (hJ u₁ w) (hJ u₂ w)]
    simp only [map_add, inner_add_right]
  have hAsmul : ∀ (c : 𝕜) u, A (c • u) = c • A u := by
    intro c u
    refine ext_inner_left 𝕜 (fun w => ?_)
    rw [inner_smul_right, hA, hA, ← integral_const_mul]
    simp only [map_smul, inner_smul_right]
  have hAn : ∀ u, ‖A u‖ ≤ (∫ x, ‖f x‖ ∂μ) * ‖u‖ := by
    intro u
    rw [LinearIsometryEquiv.norm_map, mul_comm]
    exact hℓn u
  let T : H →L[𝕜] H :=
    LinearMap.mkContinuous
      { toFun := A
        map_add' := hAadd
        map_smul' := hAsmul }
      (∫ x, ‖f x‖ ∂μ) hAn
  refine ⟨T, fun u => ⟨hwi u, fun φ => ?_⟩, LinearMap.mkContinuous_norm_le _ hC0 _⟩
  have hTu : T u = A u := rfl
  rw [hTu]
  calc φ (A u) = inner 𝕜 ((InnerProductSpace.toDual 𝕜 H).symm φ) (A u) :=
        InnerProductSpace.toDual_symm_apply.symm
    _ = ∫ x, inner 𝕜 ((InnerProductSpace.toDual 𝕜 H).symm φ) (f x u) ∂μ := hA _ _
    _ = ∫ x, φ (f x u) ∂μ := by
        congr 1
        funext x
        exact InnerProductSpace.toDual_symm_apply
