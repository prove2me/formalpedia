-- Prove2me | solution 1 for Rudin.ch11_riesz_fischer
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:42:43.928641+00:00
-- url     : https://prove2.me/submissions/1b942214-6612-4efd-b79d-d2fe6445fc6b

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
/-- Rudin, Theorem 11.42 (Riesz–Fischer): every Cauchy sequence in `ℒ²(μ)` converges in the mean
to a function of `ℒ²(μ)`; that is, `ℒ²(μ)` is complete. -/
theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : ℕ → X → ℝ)
    (hmem : ∀ n, MemL2 μ (f n)) (hcauchy : CauchyL2 μ f) :
    ∃ g : X → ℝ, MemL2 μ g ∧ TendstoL2 μ f g := by
  let F : ℕ → Lp ℝ 2 μ := fun n => (RudinSetup.memLp_of_mem (hmem n)).toLp (f n)
  have hF : CauchySeq F := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    change dist ((RudinSetup.memLp_of_mem (hmem m)).toLp (f m))
      ((RudinSetup.memLp_of_mem (hmem n)).toLp (f n)) < ε
    rw [RudinSetup.dist_eq]
    exact hN n hn m hm
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hF
  refine ⟨G, ⟨(Lp.stronglyMeasurable G).measurable, (Lp.memLp G).integrable_sq⟩, ?_⟩
  have hdist : ∀ n, L2Norm μ (fun x => f n x - G x) = dist (F n) G := by
    intro n
    simpa only [F, Lp.toLp_coeFn] using
      (RudinSetup.dist_eq (RudinSetup.memLp_of_mem (hmem n)) (Lp.memLp G)).symm
  change Tendsto (fun n => L2Norm μ (fun x => f n x - G x)) atTop (𝓝 0)
  simpa only [hdist] using tendsto_iff_dist_tendsto_zero.mp hG

#print axioms solution
