-- Prove2me | solution 1 for PettisIntegral.HasPettisIntegral.seminorm_le_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T11:54:47.474216+00:00
-- url     : https://prove2.me/submissions/40c72fd7-0421-4bfa-baac-ea8a58fd2416

import Mathlib
import Definitions.Def_PettisIntegral_Basic

open MeasureTheory

set_option autoImplicit false

namespace Sol_PettisIntegral_HasPettisIntegral_seminorm_le_lintegral

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

end Sol_PettisIntegral_HasPettisIntegral_seminorm_le_lintegral

open PettisIntegral Sol_PettisIntegral_HasPettisIntegral_seminorm_le_lintegral

theorem solution {𝕜 E X : Type*} [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    [PolynormableSpace 𝕜 E] [T2Space E] [MeasurableSpace X] {μ : Measure X} {f : X → E} {a : E}
    (ha : HasPettisIntegral 𝕜 μ f a) (p : Seminorm 𝕜 E) (hp : Continuous p)
    (hpf : AEMeasurable (fun x => p (f x)) μ) :
    ENNReal.ofReal (p a) ≤ ∫⁻ x, ENNReal.ofReal (p (f x)) ∂μ := by
  have _ := hpf
  obtain ⟨φ, hφa, hφp⟩ := exists_dual_eq_seminorm p hp a
  have hnorm : p a = ‖∫ x, φ (f x) ∂μ‖ := by
    rw [← ha.2 φ, hφa, RCLike.norm_ofReal, abs_of_nonneg (apply_nonneg p a)]
  calc ENNReal.ofReal (p a)
      = ‖∫ x, φ (f x) ∂μ‖ₑ := by rw [hnorm, ofReal_norm]
    _ ≤ ∫⁻ x, ‖φ (f x)‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x, ENNReal.ofReal (p (f x)) ∂μ := by
        refine lintegral_mono fun x => ?_
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hφp (f x))
