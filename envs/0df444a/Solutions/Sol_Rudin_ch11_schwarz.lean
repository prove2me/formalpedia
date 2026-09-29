-- Prove2me | solution 1 for Rudin.ch11_schwarz
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:42:42.422625+00:00
-- url     : https://prove2.me/submissions/44c9c839-8b8f-4e30-b668-8f150bbf5922

import Mathlib
import Definitions.Def_Rudin_ch11_L2
open Filter Topology MeasureTheory Rudin
open scoped ENNReal
set_option maxHeartbeats 1000000
set_option autoImplicit false
noncomputable section
namespace RudinSetup
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {f g : X → ℝ}
theorem memLp_of_mem (hf : Rudin.MemL2 μ f) : MemLp f 2 μ :=
  (memLp_two_iff_integrable_sq hf.1.aestronglyMeasurable).mpr hf.2

theorem inner_eq (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp only [hx, hy, RCLike.inner_apply, conj_trivial, mul_comm]

theorem norm_eq (hf : MemLp f 2 μ) : ‖hf.toLp f‖ = Rudin.L2Norm μ f := by
  rw [← Real.sqrt_sq (norm_nonneg (hf.toLp f)), Rudin.L2Norm]
  congr 1
  rw [← real_inner_self_eq_norm_sq, inner_eq hf hf]
  simp only [pow_two]
theorem dist_eq (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    dist (hf.toLp f) (hg.toLp g) = Rudin.L2Norm μ (fun x => f x - g x) := by
  rw [dist_eq_norm, ← MemLp.toLp_sub, norm_eq]
  rfl
end RudinSetup
/-- Rudin, Theorem 11.35 (Schwarz inequality in `ℒ²`): if `f, g ∈ ℒ²(μ)` then `f g` is
integrable and `|∫ f g dμ| ≤ ‖f‖₂ ‖g‖₂`. -/
theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X) (f g : X → ℝ)
    (hf : MemL2 μ f) (hg : MemL2 μ g) :
    Integrable (fun x => f x * g x) μ ∧
      |∫ x, f x * g x ∂μ| ≤ L2Norm μ f * L2Norm μ g := by
  have hfp := RudinSetup.memLp_of_mem hf
  have hgp := RudinSetup.memLp_of_mem hg
  refine ⟨hfp.integrable_mul hgp, ?_⟩
  rw [← RudinSetup.inner_eq hfp hgp]
  simpa only [Real.norm_eq_abs, RudinSetup.norm_eq] using norm_inner_le_norm (𝕜 := ℝ) (hfp.toLp f) (hgp.toLp g)

#print axioms solution
