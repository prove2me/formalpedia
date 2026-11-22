-- Prove2me | solution 1 for PettisIntegral.HasComplexPettisIntegral.seminorm_le_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:44:08.729791+00:00
-- url     : https://prove2.me/submissions/59fd5987-e13c-49a1-9c42-fdc7ffa939e1

import Mathlib
import Definitions.Def_PettisIntegral_Basic
import Definitions.Def_PettisIntegral_ComplexMeasure

open MeasureTheory

set_option autoImplicit false

namespace Sol_PettisIntegral_HasComplexPettisIntegral_seminorm_le_lintegral

/-- Hahn–Banach: for a continuous seminorm `p` on a polynormable space and a vector `a`, there is
a continuous linear form `φ` with `φ a = p a` and `‖φ x‖ ≤ p x` for all `x`. -/
theorem exists_dual_eq_seminorm {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [PolynormableSpace 𝕜 E] (p : Seminorm 𝕜 E) (hp : Continuous p) (a : E) :
    ∃ φ : StrongDual 𝕜 E, φ a = (p a : 𝕜) ∧ ∀ x, ‖φ x‖ ≤ p x := by
  by_cases ha : a = 0
  · refine ⟨0, ?_, fun x => ?_⟩
    · simp [ha]
    · simp
  · -- the linear form `c • a ↦ c * p a` on the line `𝕜 ∙ a`
    let f : E →ₗ.[𝕜] 𝕜 := LinearPMap.mkSpanSingleton a (p a : 𝕜) ha
    have hdom : ∀ x : f.domain, ‖f.toFun x‖ ≤ p x := by
      rintro ⟨x, hx⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      have h1 : f.toFun ⟨c • a, hx⟩ = c • (p a : 𝕜) :=
        LinearPMap.mkSpanSingleton'_apply a (p a : 𝕜) _ c hx
      rw [h1]
      simp only [smul_eq_mul, norm_mul, map_smul_eq_mul]
      rw [RCLike.norm_ofReal, abs_of_nonneg (apply_nonneg p a)]
    obtain ⟨g, hg, hgp⟩ :=
      Module.Dual.exists_continuous_extension_of_le_seminorm f.domain f.toFun hp hdom
    refine ⟨g, ?_, hgp⟩
    have hmem : a ∈ f.domain := Submodule.mem_span_singleton_self a
    have h2 := hg ⟨a, hmem⟩
    have h3 : f.toFun ⟨a, hmem⟩ = (p a : 𝕜) :=
      LinearPMap.mkSpanSingleton_apply 𝕜 𝕜 ha (p a : 𝕜)
    rw [← h3]
    exact h2

end Sol_PettisIntegral_HasComplexPettisIntegral_seminorm_le_lintegral

open PettisIntegral Sol_PettisIntegral_HasComplexPettisIntegral_seminorm_le_lintegral

theorem solution {E X : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    [PolynormableSpace ℂ E] [T2Space E] [MeasurableSpace X] {μ : ComplexMeasure X}
    {f : X → E} {a : E}
    (ha : HasComplexPettisIntegral μ f a) (p : Seminorm ℂ E) (hp : Continuous p)
    (hpf : AEMeasurable (fun x => p (f x)) μ.variation) :
    ENNReal.ofReal (p a) ≤ ∫⁻ x, ENNReal.ofReal (p (f x)) ∂μ.variation := by
  have _ := hpf
  obtain ⟨φ, hφa, hφp⟩ := exists_dual_eq_seminorm p hp a
  have hnorm : p a =
      ‖VectorMeasure.integral μ (fun x => φ (f x)) (ContinuousLinearMap.mul ℝ ℂ)‖ := by
    rw [← complexWeakIntegral_apply, ← ha.2 φ, hφa, RCLike.norm_ofReal,
      abs_of_nonneg (apply_nonneg p a)]
  calc ENNReal.ofReal (p a)
      = ‖VectorMeasure.integral μ (fun x => φ (f x)) (ContinuousLinearMap.mul ℝ ℂ)‖ₑ := by
        rw [hnorm, ofReal_norm]
    _ ≤ ‖ContinuousLinearMap.mul ℝ ℂ‖ₑ * ∫⁻ x, ‖φ (f x)‖ₑ ∂μ.variation :=
        VectorMeasure.enorm_integral_le_lintegral_enorm
    _ = ∫⁻ x, ‖φ (f x)‖ₑ ∂μ.variation := by
        rw [ContinuousLinearMap.opENorm_mul, one_mul]
    _ ≤ ∫⁻ x, ENNReal.ofReal (p (f x)) ∂μ.variation := by
        refine lintegral_mono fun x => ?_
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hφp (f x))
