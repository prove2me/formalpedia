-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.card_support_le_and_sum_two_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:09:55.406146+00:00
-- url     : https://prove2.me/submissions/7cbb1029-e881-44a7-8fdc-c28a8f16fbd7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegralMulConjGaussianEqCoeffNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CardSupportLeAndSumTwoPowLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {g c : ℕ} (p : MvPolynomial (Fin g) ℂ) (hp : p.totalDegree ≤ c) :
    (p.support.card : ℝ) ≤ 2 ^ (g + c) ∧
      ∑ α ∈ p.support, (2 : ℝ) ^ (g + ∑ i, α i) ≤ 2 ^ (g + c) * 2 ^ (g + c) := by
  have hdeg : ∀ α ∈ p.support, ∑ i, α i ≤ c := fun α hα => by
    have := MvPolynomial.le_totalDegree hα
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at this
    exact this.trans hp
  have h1 : (p.support.card : ℝ) ≤ ∑ α ∈ p.support, (2 : ℝ) ^ c * ∏ i, (1 / 2 : ℝ) ^ α i := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_le_sum fun α hα => ?_
    rw [Nat.cast_one, Finset.prod_pow_eq_pow_sum, one_div, inv_pow, ← div_eq_mul_inv,
      one_le_div (by positivity)]
    exact pow_le_pow_right₀ (by norm_num) (hdeg α hα)
  have hsub : p.support.image (fun α : Fin g →₀ ℕ => (α : Fin g → ℕ)) ⊆
      Fintype.piFinset (fun _ : Fin g => Finset.range (c + 1)) := by
    intro x hx
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 hx
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact (Finset.single_le_sum (fun j _ => Nat.zero_le (α j)) (Finset.mem_univ i)).trans
      (hdeg α hα)
  have h2 : ∑ α ∈ p.support, ∏ i, (1 / 2 : ℝ) ^ α i ≤
      ∏ _i : Fin g, ∑ k ∈ Finset.range (c + 1), (1 / 2 : ℝ) ^ k := by
    calc ∑ α ∈ p.support, ∏ i, (1 / 2 : ℝ) ^ α i
        = ∑ x ∈ p.support.image (fun α : Fin g →₀ ℕ => (α : Fin g → ℕ)),
            ∏ i, (1 / 2 : ℝ) ^ x i :=
          (Finset.sum_image (f := fun x : Fin g → ℕ => ∏ i, (1 / 2 : ℝ) ^ x i) (s := p.support)
            (g := fun α : Fin g →₀ ℕ => (α : Fin g → ℕ))
            (fun a _ b _ h => Finsupp.ext (congrFun h))).symm
      _ ≤ ∑ x ∈ Fintype.piFinset (fun _ : Fin g => Finset.range (c + 1)),
            ∏ i, (1 / 2 : ℝ) ^ x i :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = _ := (Finset.prod_univ_sum _ _).symm
  have hcard : (p.support.card : ℝ) ≤ 2 ^ (g + c) := by
    calc (p.support.card : ℝ) ≤ ∑ α ∈ p.support, (2 : ℝ) ^ c * ∏ i, (1 / 2 : ℝ) ^ α i := h1
      _ = 2 ^ c * ∑ α ∈ p.support, ∏ i, (1 / 2 : ℝ) ^ α i := by rw [Finset.mul_sum]
      _ ≤ 2 ^ c * ∏ _i : Fin g, ∑ k ∈ Finset.range (c + 1), (1 / 2 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ 2 ^ c * ∏ _i : Fin g, (2 : ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _ => by positivity)
            (fun _ _ => sum_geometric_two_le _)) (by positivity)
      _ = 2 ^ (g + c) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_add]
          ring
  refine ⟨hcard, ?_⟩
  calc ∑ α ∈ p.support, (2 : ℝ) ^ (g + ∑ i, α i) ≤ ∑ α ∈ p.support, (2 : ℝ) ^ (g + c) :=
        Finset.sum_le_sum fun α hα => pow_le_pow_right₀ (by norm_num) (by have := hdeg α hα; omega)
    _ = p.support.card * 2 ^ (g + c) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ (g + c) * 2 ^ (g + c) := mul_le_mul_of_nonneg_right hcard (by positivity)
end ReciprocityTheory.ChartRestriction.G.I2
