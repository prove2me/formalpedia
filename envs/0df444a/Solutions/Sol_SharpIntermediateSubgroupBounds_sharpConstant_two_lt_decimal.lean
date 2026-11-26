-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.sharpConstant_two_lt_decimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:00:25.374276+00:00
-- url     : https://prove2.me/submissions/68df674d-4e58-479e-bb8e-6a19104f4ebc

import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Decimal
import Theorems.Thm_SharpIntermediateSubgroupBounds_eulerC_partial_tendsto
import Theorems.Thm_SharpIntermediateSubgroupBounds_gaussianTheta_pos
import Theorems.Thm_SharpIntermediateSubgroupBounds_gaussianTheta_summable

section
namespace SharpIntermediateSubgroupBounds
open scoped BigOperators
open Filter Finset Topology
private theorem exact_decimal_comparison :
    eulerUpper20 * thetaUpper4 < (3685984401 : ℝ) / 500000000 := by
  norm_num [eulerUpper20, thetaUpper4, Finset.prod_range_succ,
    Finset.sum_range_succ]
private lemma one_sub_sum_le_prod_one_sub { α : Type* } [DecidableEq α]
    (s : Finset α) (x : α → ℝ)
    (hx0 : ∀ i ∈ s, 0 ≤ x i) (hx1 : ∀ i ∈ s, x i ≤ 1) :
    1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hxa0 : 0 ≤ x a := hx0 a (by simp)
      have hxa1 : x a ≤ 1 := hx1 a (by simp)
      have hsum0 : 0 ≤ ∑ i ∈ s, x i :=
        Finset.sum_nonneg fun i hi ↦ hx0 i (by simp [hi])
      calc
        1 - (x a + ∑ i ∈ s, x i) ≤
            (1 - x a) * (1 - ∑ i ∈ s, x i) := by
              nlinarith [mul_nonneg hxa0 hsum0]
        _ ≤ (1 - x a) * ∏ i ∈ s, (1 - x i) :=
          mul_le_mul_of_nonneg_left
            (ih (fun i hi ↦ hx0 i (by simp [hi]))
              (fun i hi ↦ hx1 i (by simp [hi]))) (sub_nonneg.mpr hxa1)
private lemma dyadic_euler_tail_product_lower (k : ℕ) :
    1 - (1 / 2 : ℝ) ^ 20 ≤
      ∏ n ∈ Finset.range k, (1 - (1 / 2 : ℝ) ^ (20 + n + 1)) := by
  have hsum :
      (∑ n ∈ Finset.range k, (1 / 2 : ℝ) ^ (20 + n + 1)) ≤
        (1 / 2 : ℝ) ^ 20 := by
    calc
      (∑ n ∈ Finset.range k, (1 / 2 : ℝ) ^ (20 + n + 1)) =
          (1 / 2 : ℝ) ^ 21 *
            ∑ n ∈ Finset.range k, (1 / 2 : ℝ) ^ n := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro n hn
              rw [← pow_add]
              congr 1
              omega
      _ ≤ (1 / 2 : ℝ) ^ 21 * 2 :=
        mul_le_mul_of_nonneg_left (sum_geometric_two_le k) (by positivity)
      _ = (1 / 2 : ℝ) ^ 20 := by norm_num
  calc
    1 - (1 / 2 : ℝ) ^ 20 ≤
        1 - ∑ n ∈ Finset.range k, (1 / 2 : ℝ) ^ (20 + n + 1) :=
      sub_le_sub_left hsum 1
    _ ≤ ∏ n ∈ Finset.range k, (1 - (1 / 2 : ℝ) ^ (20 + n + 1)) :=
      one_sub_sum_le_prod_one_sub _ _
        (fun n hn ↦ pow_nonneg (by norm_num) _)
        (fun n hn ↦ pow_le_one₀ (by norm_num) (by norm_num))
private lemma one_le_dyadic_euler_factor (n : ℕ) :
    1 ≤ (1 - (1 / 2 : ℝ) ^ (n + 1))⁻¹ := by
  have hpow : (1 / 2 : ℝ) ^ (n + 1) < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hnonneg : 0 ≤ (1 / 2 : ℝ) ^ (n + 1) := by positivity
  exact (one_le_inv₀ (by linarith)).2 (by linarith)
private lemma dyadic_euler_partial_nonneg (r : ℕ) :
    0 ≤ ∏ n ∈ Finset.range r, (1 - (1 / 2 : ℝ) ^ (n + 1))⁻¹ := by
  exact Finset.prod_nonneg fun n hn ↦
    zero_le_one.trans (one_le_dyadic_euler_factor n)
private lemma eulerUpper20_nonneg : 0 ≤ eulerUpper20 := by
  rw [eulerUpper20]
  exact mul_nonneg (dyadic_euler_partial_nonneg 20)
    (zero_le_one.trans ((one_le_inv₀ (by norm_num)).2 (by norm_num)))
private lemma dyadic_euler_partial_le (r : ℕ) :
    (∏ n ∈ Finset.range r, (1 - (1 / 2 : ℝ) ^ (n + 1))⁻¹) ≤
      eulerUpper20 := by
  by_cases hr : r ≤ 20
  · have hprefix :
        (∏ n ∈ Finset.range r, (1 - (1 / 2 : ℝ) ^ (n + 1))⁻¹) ≤
          ∏ n ∈ Finset.range 20, (1 - (1 / 2 : ℝ) ^ (n + 1))⁻¹ := by
      apply Finset.prod_le_prod_of_subset_of_one_le
      · exact Finset.range_mono hr
      · intro n hn
        exact zero_le_one.trans (one_le_dyadic_euler_factor n)
      · intro n hn hnr
        exact one_le_dyadic_euler_factor n
    have htail : 1 ≤ (1 - (1 / 2 : ℝ) ^ 20)⁻¹ :=
      (one_le_inv₀ (by norm_num)).2 (by norm_num)
    exact hprefix.trans (by
      rw [eulerUpper20]
      exact le_mul_of_one_le_right (dyadic_euler_partial_nonneg 20) htail)
  · have h20 : 20 ≤ r := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h20
    rw [Finset.prod_range_add]
    have htailpos :
        0 < ∏ n ∈ Finset.range k,
          (1 - (1 / 2 : ℝ) ^ (20 + n + 1)) := by
      apply Finset.prod_pos
      intro n hn
      exact sub_pos.mpr (pow_lt_one₀ (by norm_num) (by norm_num) (by omega))
    have hbasepos : 0 < 1 - (1 / 2 : ℝ) ^ 20 := by norm_num
    have htail :
        (∏ n ∈ Finset.range k,
            (1 - (1 / 2 : ℝ) ^ (20 + n + 1))⁻¹) ≤
          (1 - (1 / 2 : ℝ) ^ 20)⁻¹ := by
      have hinv := (inv_le_inv₀ htailpos hbasepos).2
        (dyadic_euler_tail_product_lower k)
      simpa only [Finset.prod_inv_distrib] using hinv
    rw [eulerUpper20]
    exact mul_le_mul_of_nonneg_left htail (by positivity)
private lemma eulerC_two_le : eulerC 2 ≤ eulerUpper20 := by
  apply le_of_tendsto (eulerC_partial_tendsto (p := (2 : ℝ)) (by norm_num))
  filter_upwards [] with r
  simpa [one_div] using dyadic_euler_partial_le r
private lemma gaussian_two_nat (n : ℕ) :
    Real.exp (-Real.log 2 * (n : ℝ) ^ 2) =
      (1 / 2 : ℝ) ^ (n ^ 2) := by
  rw [show -Real.log 2 * (n : ℝ) ^ 2 =
      (n ^ 2 : ℕ) * (-Real.log 2) by norm_num [Nat.cast_pow]; ring]
  rw [Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num
private lemma gaussianTheta_two_eq :
    gaussianTheta 2 =
      1 + 2 * ∑' n : ℕ, (1 / 2 : ℝ) ^ ((n + 1) ^ 2) := by
  let f : ℤ → ℝ := fun z ↦ Real.exp (-Real.log 2 * (z : ℝ) ^ 2)
  have hf : Summable f := gaussianTheta_summable (p := (2 : ℝ)) (by norm_num)
  have hpos : Summable (fun n : ℕ ↦ f (n + 1)) := by
    exact hf.comp_injective (fun a b h ↦ by omega)
  have hneg : Summable (fun n : ℕ ↦ f (-(n + 1))) := by
    exact hf.comp_injective (fun a b h ↦ by omega)
  rw [gaussianTheta, tsum_of_add_one_of_neg_add_one hpos hneg]
  have hpos_eq :
      (∑' n : ℕ, f (n + 1)) =
        ∑' n : ℕ, (1 / 2 : ℝ) ^ ((n + 1) ^ 2) := by
    apply tsum_congr
    intro n
    simpa [f] using gaussian_two_nat (n + 1)
  have hneg_eq :
      (∑' n : ℕ, f (-(n + 1))) =
        ∑' n : ℕ, (1 / 2 : ℝ) ^ ((n + 1) ^ 2) := by
    apply tsum_congr
    intro n
    dsimp [f]
    convert gaussian_two_nat (n + 1) using 1 <;> norm_num <;> ring
  rw [hpos_eq, hneg_eq]
  simp [f]
  ring
private lemma dyadic_theta_summable :
    Summable (fun n : ℕ ↦ (1 / 2 : ℝ) ^ ((n + 1) ^ 2)) := by
  let f : ℤ → ℝ := fun z ↦ Real.exp (-Real.log 2 * (z : ℝ) ^ 2)
  have hf : Summable f := gaussianTheta_summable (p := (2 : ℝ)) (by norm_num)
  have hpos : Summable (fun n : ℕ ↦ f (n + 1)) :=
    hf.comp_injective (fun a b h ↦ by omega)
  exact hpos.congr fun n ↦ by simpa [f] using gaussian_two_nat (n + 1)
private lemma dyadic_theta_tail_le :
    (∑' n : ℕ, (1 / 2 : ℝ) ^ ((n + 4 + 1) ^ 2)) ≤
      (1 / 2 : ℝ) ^ 25 * (1 - (1 / 2 : ℝ) ^ 11)⁻¹ := by
  let g : ℕ → ℝ := fun n ↦
    (1 / 2 : ℝ) ^ 25 * ((1 / 2 : ℝ) ^ 11) ^ n
  have hg : Summable g := by
    exact (summable_geometric_of_lt_one (by positivity)
      (by norm_num : (1 / 2 : ℝ) ^ 11 < 1)).mul_left _
  have hterm : ∀ n : ℕ,
      (1 / 2 : ℝ) ^ ((n + 4 + 1) ^ 2) ≤ g n := by
    intro n
    have hn : 25 + 11 * n ≤ (n + 4 + 1) ^ 2 := by
      nlinarith [Nat.le_mul_self n]
    calc
      (1 / 2 : ℝ) ^ ((n + 4 + 1) ^ 2) ≤
          (1 / 2 : ℝ) ^ (25 + 11 * n) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
      _ = g n := by simp [g, pow_add, pow_mul]
  have hf : Summable (fun n : ℕ ↦
      (1 / 2 : ℝ) ^ ((n + 4 + 1) ^ 2)) :=
    hg.of_nonneg_of_le (fun n ↦ by positivity) hterm
  calc
    (∑' n : ℕ, (1 / 2 : ℝ) ^ ((n + 4 + 1) ^ 2)) ≤ ∑' n, g n :=
      hf.tsum_le_tsum hterm hg
    _ = (1 / 2 : ℝ) ^ 25 * (1 - (1 / 2 : ℝ) ^ 11)⁻¹ := by
      rw [show (∑' n, g n) = (1 / 2 : ℝ) ^ 25 *
          ∑' n : ℕ, ((1 / 2 : ℝ) ^ 11) ^ n by
        simp only [g, tsum_mul_left]]
      rw [tsum_geometric_of_lt_one (by positivity) (by norm_num)]
private lemma gaussianTheta_two_le : gaussianTheta 2 ≤ thetaUpper4 := by
  rw [gaussianTheta_two_eq, thetaUpper4]
  have hsplit := dyadic_theta_summable.sum_add_tsum_nat_add 4
  rw [← hsplit]
  have htail :
      (∑' n : ℕ, (1 / 2 : ℝ) ^ ((n + 4 + 1) ^ 2)) ≤
        (1 / 2 : ℝ) ^ 25 * (1 - (1 / 2 : ℝ) ^ 11)⁻¹ :=
    dyadic_theta_tail_le
  nlinarith
end SharpIntermediateSubgroupBounds
end

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
open Filter Finset Topology
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution :
    sharpConstant 2 < (3685984401 : ℝ) / 500000000 := by
  rw [sharpConstant]
  have hT0 : 0 ≤ gaussianTheta 2 :=
    (gaussianTheta_pos (p := (2 : ℝ)) (by norm_num)).le
  calc
    eulerC 2 * gaussianTheta 2 ≤ eulerUpper20 * thetaUpper4 :=
      mul_le_mul eulerC_two_le gaussianTheta_two_le hT0 eulerUpper20_nonneg
    _ < (3685984401 : ℝ) / 500000000 := exact_decimal_comparison
end SharpIntermediateSubgroupBounds
