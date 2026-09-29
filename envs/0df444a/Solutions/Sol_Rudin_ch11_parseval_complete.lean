-- Prove2me | solution 1 for Rudin.ch11_parseval_complete
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:42:44.777575+00:00
-- url     : https://prove2.me/submissions/b5fc9d9a-8c84-485e-8946-69747cff99fe

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
/-- Rudin, Theorem 11.45: if `{φₙ}` is a complete orthonormal set in `ℒ²(μ)` and `cₙ` are the
Fourier coefficients of `f ∈ ℒ²(μ)`, then `∑ cₙ² = ∫ f² dμ` (Parseval's identity). -/
theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X) (φ : ℕ → X → ℝ)
    (hmem : ∀ n, MemL2 μ (φ n))
    (horth : ∀ m n, m ≠ n → (∫ x, φ m x * φ n x ∂μ) = 0)
    (hnorm : ∀ n, (∫ x, (φ n x) ^ 2 ∂μ) = 1)
    (hcomplete : ∀ g : X → ℝ, MemL2 μ g → (∀ n, (∫ x, g x * φ n x ∂μ) = 0) → L2Norm μ g = 0)
    (f : X → ℝ) (hf : MemL2 μ f) (c : ℕ → ℝ) (hc : ∀ n, c n = ∫ x, f x * φ n x ∂μ) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, (c n) ^ 2) atTop (𝓝 (∫ x, (f x) ^ 2 ∂μ)) := by
  classical
  let v : ℕ → Lp ℝ 2 μ := fun n => (RudinSetup.memLp_of_mem (hmem n)).toLp (φ n)
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    change inner ℝ ((RudinSetup.memLp_of_mem (hmem i)).toLp (φ i))
      ((RudinSetup.memLp_of_mem (hmem j)).toLp (φ j)) = _
    rw [RudinSetup.inner_eq]
    by_cases hij : i = j
    · subst j
      simpa [pow_two] using hnorm i
    · simpa only [if_neg hij] using horth i j hij
  have hsp : (Submodule.span ℝ (Set.range v))ᗮ = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro G hG
    change G = 0
    have hzero : L2Norm μ (G : X → ℝ) = 0 := by
      apply hcomplete G ⟨(Lp.stronglyMeasurable G).measurable, (Lp.memLp G).integrable_sq⟩
      intro n
      rw [← RudinSetup.inner_eq (Lp.memLp G) (RudinSetup.memLp_of_mem (hmem n)), Lp.toLp_coeFn]
      have hvn : v n ∈ Submodule.span ℝ (Set.range v) := Submodule.subset_span ⟨n, rfl⟩
      exact Submodule.inner_left_of_mem_orthogonal hvn hG
    apply norm_eq_zero.mp
    simpa only [Lp.toLp_coeFn] using (RudinSetup.norm_eq (Lp.memLp G)).trans hzero
  let b : HilbertBasis ℕ ℝ (Lp ℝ 2 μ) := HilbertBasis.mkOfOrthogonalEqBot hv hsp
  have hb : ∀ n, b n = v n := fun n =>
    congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot hv hsp) n
  let F : Lp ℝ 2 μ := (RudinSetup.memLp_of_mem hf).toLp f
  have hc' : ∀ n, inner ℝ F (b n) = c n := by
    intro n
    rw [hb n]
    exact (RudinSetup.inner_eq (RudinSetup.memLp_of_mem hf)
      (RudinSetup.memLp_of_mem (hmem n))).trans (hc n).symm
  have hterm : (fun n => inner ℝ F (b n) * inner ℝ (b n) F) = fun n => (c n) ^ 2 := by
    funext n
    rw [real_inner_comm F (b n), hc' n, pow_two]
  have htotal : inner ℝ F F = ∫ x, (f x) ^ 2 ∂μ := by
    rw [show inner ℝ F F = ∫ x, f x * f x ∂μ from
      RudinSetup.inner_eq (RudinSetup.memLp_of_mem hf) (RudinSetup.memLp_of_mem hf)]
    simp only [pow_two]
  have hsum := b.hasSum_inner_mul_inner F F
  rw [hterm, htotal] at hsum
  exact hsum.tendsto_sum_nat

#print axioms solution
