-- Prove2me | solution 1 for UnderstandingML.gaussian_kernel
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T19:03:57.996241+00:00
-- url     : https://prove2.me/submissions/9f535f32-fd53-4e94-b0ca-18393ff05cb4

import Definitions.Def_UnderstandingML_Kernel
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory
open scoped InnerProductSpace

open UnderstandingML

namespace GaussianKernelAux

/-- The exponential series `∑ yⁿ/n! = eʸ`. -/
lemma tsum_pow_div_factorial (y : ℝ) : ∑' n : ℕ, y ^ n / (Nat.factorial n) = Real.exp y := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-- If `a` and `b` are square-summable then `a * b` is summable. -/
lemma summable_mul_of_sq {ι : Type*} {a b : ι → ℝ} (ha : Summable fun i => a i ^ 2)
    (hb : Summable fun i => b i ^ 2) : Summable fun i => a i * b i := by
  refine Summable.of_norm_bounded ((ha.add hb).div_const 2) fun i => ?_
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|a i| - |b i|), sq_abs (a i), sq_abs (b i)]

/-- Square-summable coordinates define a feature map into `ℓ²`, whose inner products are the
sums of products of coordinates. -/
lemma exists_lp_feature {α ι : Type*} (c : α → ι → ℝ) (hc : ∀ a, Summable fun i => c a i ^ 2) :
    ∃ ψ : α → lp (fun _ : ι => ℝ) 2, ∀ a b, ⟪ψ a, ψ b⟫_ℝ = ∑' i, c a i * c b i := by
  have hmem : ∀ a, Memℓp (c a) 2 := by
    intro a
    refine (memℓp_gen_iff (by norm_num)).2 ?_
    refine (hc a).congr fun i => ?_
    simp [Real.norm_eq_abs, sq_abs]
  refine ⟨fun a => ⟨c a, hmem a⟩, fun a b => ?_⟩
  rw [lp.inner_eq_tsum]
  refine tsum_congr fun i => ?_
  simp [mul_comm]

end GaussianKernelAux

open GaussianKernelAux in
theorem solution :
    (∃ ψ : ℝ → lp (fun _ : ℕ ↦ ℝ) 2,
      ∀ x x' : ℝ, ⟪ψ x, ψ x'⟫_ℝ = Real.exp (-((x - x') ^ 2) / 2)) ∧
    ∀ (n : ℕ) (σ : ℝ), 0 < σ → IsKernel (gaussianKernel (n := n) σ) := by
  constructor
  · -- coordinates `ψ(x)ₙ = e^{-x²/2} xⁿ / √n!`
    let c : ℝ → ℕ → ℝ := fun x k => Real.exp (-(x ^ 2) / 2) * x ^ k / Real.sqrt (Nat.factorial k)
    have hprod : ∀ x x' : ℝ, ∀ k, c x k * c x' k =
        Real.exp (-(x ^ 2) / 2) * Real.exp (-(x' ^ 2) / 2) * ((x * x') ^ k / Nat.factorial k) := by
      intro x x' k
      simp only [c]
      rw [div_mul_div_comm, Real.mul_self_sqrt (Nat.cast_nonneg _), mul_pow]
      ring
    have hc : ∀ x, Summable fun k => c x k ^ 2 := by
      intro x
      have := (Real.summable_pow_div_factorial (x * x)).mul_left
        (Real.exp (-(x ^ 2) / 2) * Real.exp (-(x ^ 2) / 2))
      refine this.congr fun k => ?_
      rw [sq (c x k), hprod]
    obtain ⟨ψ, hψ⟩ := exists_lp_feature c hc
    refine ⟨ψ, fun x x' => ?_⟩
    rw [hψ]
    simp_rw [hprod]
    rw [tsum_mul_left, tsum_pow_div_factorial, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  · intro n σ hσ
    -- coordinates indexed by `(k, J)` with `J ∈ {1, …, n}^k`:
    -- `ψ(x)_{k,J} = e^{-‖x‖²/(2σ)} ∏ᵢ x_{Jᵢ} / √(σ^k k!)`
    let E : Vec n → ℝ := fun x => Real.exp (-(‖x‖ ^ 2) / (2 * σ))
    let c : Vec n → (Σ k : ℕ, (Fin k → Fin n)) → ℝ := fun x p =>
      E x * (∏ i, x (p.2 i)) / Real.sqrt (σ ^ p.1 * Nat.factorial p.1)
    have hprod : ∀ x x' p, c x p * c x' p =
        E x * E x' * (∏ i, x (p.2 i) * x' (p.2 i)) / (σ ^ p.1 * Nat.factorial p.1) := by
      intro x x' p
      simp only [c]
      rw [div_mul_div_comm, Real.mul_self_sqrt (by positivity), Finset.prod_mul_distrib]
      ring
    have hfiber : ∀ x x' : Vec n, ∀ k : ℕ,
        ∑ J : Fin k → Fin n, ∏ i, x (J i) * x' (J i) = ⟪x, x'⟫_ℝ ^ k := by
      intro x x' k
      have hin : ⟪x, x'⟫_ℝ = ∑ j, x j * x' j := by simp [PiLp.inner_apply, mul_comm]
      rw [hin, ← Fin.prod_const, Fintype.prod_sum]
    have hsum : ∀ x x' : Vec n, ∀ k : ℕ, ∑' J : Fin k → Fin n, c x ⟨k, J⟩ * c x' ⟨k, J⟩ =
        E x * E x' * ((⟪x, x'⟫_ℝ / σ) ^ k / Nat.factorial k) := by
      intro x x' k
      rw [tsum_fintype]
      simp_rw [hprod]
      rw [← Finset.sum_div, ← Finset.mul_sum, hfiber, div_pow]
      field_simp
    have hc : ∀ x, Summable fun p => c x p ^ 2 := by
      intro x
      refine (summable_sigma_of_nonneg fun p => sq_nonneg _).2 ⟨fun k => Summable.of_finite, ?_⟩
      simp_rw [sq, hsum]
      exact (Real.summable_pow_div_factorial _).mul_left _
    obtain ⟨ψ, hψ⟩ := exists_lp_feature c hc
    refine ⟨lp (fun _ : (Σ k : ℕ, (Fin k → Fin n)) => ℝ) 2, inferInstance, inferInstance,
      inferInstance, ψ, fun x x' => ?_⟩
    rw [hψ, (summable_mul_of_sq (hc x) (hc x')).tsum_sigma]
    simp_rw [hsum]
    rw [tsum_mul_left, tsum_pow_div_factorial]
    simp only [gaussianKernel, E]
    rw [← Real.exp_add, ← Real.exp_add, norm_sub_sq_real]
    congr 1
    field_simp
    ring
