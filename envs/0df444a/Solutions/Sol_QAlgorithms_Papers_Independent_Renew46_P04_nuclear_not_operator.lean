-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P04.nuclear_not_operator
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:33:35.531801+00:00
-- url     : https://prove2.me/submissions/973b3f3d-9f01-4fb2-a904-1c4cfac32ca7

import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_c0_l1_attainment
import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_bilinear_extension
import Mathlib.Tactic

noncomputable section
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
open QAlgorithms.Papers.Independent.Renew46.P04
open scoped BigOperators ENNReal Topology Classical
open Filter

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNorm
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorSeminormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedSpace
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedSpace

namespace X9CZero
variable {K I : Type*} [RCLike K]

-- Coordinate vectors and evaluation functionals on the discrete c0 space.
def single (i : I) (a : K) : CZero K I := by
  classical
  exact
    { toFun := fun j => if j.ofTopology = i then a else 0
      continuous_toFun := continuous_of_discreteTopology
      zero_at_infty' := by
        rw [Filter.cocompact_eq_cofinite]
        apply tendsto_const_nhds.congr'
        filter_upwards [Filter.eventually_cofinite_ne (WithTopology.toTopology ⊥ i)] with j hj
        have hj' : j.ofTopology ≠ i := by intro h; apply hj; cases j; cases h; rfl
        simp [hj'] }

@[simp] lemma single_apply (i j : I) (a : K) :
    single i a (WithTopology.toTopology ⊥ j) = if j = i then a else 0 := by
  classical
  rfl

lemma norm_le (x : CZero K I) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, ‖x (WithTopology.toTopology ⊥ i)‖ ≤ C) : ‖x‖ ≤ C := by
  change ‖x.toBCF‖ ≤ C
  apply (BoundedContinuousFunction.norm_le hC).2
  intro i
  exact h i.ofTopology

lemma apply_le (x : CZero K I) (i : I) : ‖x (WithTopology.toTopology ⊥ i)‖ ≤ ‖x‖ :=
  x.toBCF.norm_coe_le_norm _

def eval (i : I) : CZero K I →L[K] K :=
  LinearMap.mkContinuous
    { toFun := fun x => x (WithTopology.toTopology ⊥ i)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    1 (fun x => by simpa using apply_le x i)

@[simp] lemma eval_apply (i : I) (x : CZero K I) :
    eval i x = x (WithTopology.toTopology ⊥ i) := rfl

lemma dual_coeff_sum (f : CZero K I →L[K] K) (s : Finset I) :
    ∑ i ∈ s, ‖f (single i 1)‖ ≤ ‖f‖ := by
  classical
  choose c hc he using fun i : I => RCLike.exists_norm_eq_mul_self (f (single i 1))
  let x : CZero K I := ∑ i ∈ s, c i • single i 1
  have hx : ‖x‖ ≤ 1 := by
    apply norm_le _ zero_le_one
    intro j
    change ‖eval j (∑ i ∈ s, c i • single i 1 : CZero K I)‖ ≤ 1
    simp only [map_sum, map_smul, eval_apply, single_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero]
    by_cases hj : j ∈ s <;> simp [Finset.sum_ite_eq', hj, hc]
  have heq : f x = ((∑ i ∈ s, ‖f (single i 1)‖ : ℝ) : K) := by
    simp only [x, map_sum, map_smul, smul_eq_mul, ← he, RCLike.ofReal_sum]
  have h := (f.le_opNorm x).trans (mul_le_of_le_one_right (norm_nonneg _) hx)
  rw [heq, RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))] at h
  exact h

end X9CZero

namespace X9Nonattainment
variable {K : Type*} [RCLike K]

abbrev weight (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

lemma weight_pos (n : ℕ) : 0 < weight n := pow_pos (by norm_num) n

lemma weight_summable : Summable weight := summable_geometric_of_norm_lt_one (by norm_num)

lemma norm_weight (n : ℕ) : ‖(weight n : K)‖ = weight n := by
  rw [RCLike.norm_ofReal, abs_of_pos (weight_pos n)]

lemma norm_term_le (n : ℕ) :
    ‖(weight n : K) • X9CZero.eval (K := K) n‖ ≤ weight n := by
  apply ContinuousLinearMap.opNorm_le_bound _ (weight_pos n).le
  intro x
  change ‖(weight n : K) * x (WithTopology.toTopology ⊥ n)‖ ≤ weight n * ‖x‖
  rw [norm_mul, norm_weight]
  exact mul_le_mul_of_nonneg_left (X9CZero.apply_le x n) (weight_pos n).le

lemma terms_norm_summable :
    Summable (fun n : ℕ => ‖(weight n : K) • X9CZero.eval (K := K) n‖) :=
  weight_summable.of_nonneg_of_le (fun _ => ContinuousLinearMap.opNorm_nonneg _) norm_term_le

lemma terms_summable : Summable (fun n : ℕ => (weight n : K) • X9CZero.eval (K := K) n) :=
  Summable.of_norm (f := fun n : ℕ => (weight n : K) • X9CZero.eval (K := K) n)
    terms_norm_summable

def functional : CZero K ℕ →L[K] K := ∑' n : ℕ, (weight n : K) • X9CZero.eval (K := K) n

lemma functional_apply (x : CZero K ℕ) :
    functional x = ∑' n : ℕ, (weight n : K) * x (WithTopology.toTopology ⊥ n) := by
  have h := (terms_summable (K := K)).hasSum.map (ContinuousLinearMap.apply K K x) (by fun_prop)
  exact h.tsum_eq.symm

lemma functional_single (n : ℕ) : functional (X9CZero.single (K := K) n 1) = (weight n : K) := by
  rw [functional_apply]
  simp only [X9CZero.single_apply, mul_ite, mul_one, mul_zero]
  simp

lemma functional_norm : ‖functional (K := K)‖ = ∑' n, weight n := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (tsum_nonneg (fun n => (weight_pos n).le))
    intro x
    have hle (n : ℕ) : ‖(weight n : K) * x (WithTopology.toTopology ⊥ n)‖ ≤ weight n * ‖x‖ := by
      rw [norm_mul, norm_weight]
      exact mul_le_mul_of_nonneg_left (X9CZero.apply_le x n) (weight_pos n).le
    have hs : Summable (fun n : ℕ => weight n * ‖x‖) := weight_summable.mul_right ‖x‖
    have hsn : Summable (fun n : ℕ => ‖(weight n : K) * x (WithTopology.toTopology ⊥ n)‖) :=
      hs.of_nonneg_of_le (fun _ => norm_nonneg _) hle
    rw [functional_apply]
    calc
      ‖∑' n : ℕ, (weight n : K) * x (WithTopology.toTopology ⊥ n)‖ ≤
          ∑' n : ℕ, ‖(weight n : K) * x (WithTopology.toTopology ⊥ n)‖ := norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' n : ℕ, weight n * ‖x‖ := hsn.tsum_le_tsum hle hs
      _ = (∑' n : ℕ, weight n) * ‖x‖ := tsum_mul_right
  · apply Real.tsum_le_of_sum_le (fun n => (weight_pos n).le)
    intro s
    simpa only [functional_single, norm_weight] using X9CZero.dual_coeff_sum (functional (K := K)) s

lemma exists_small_coordinate (x : CZero K ℕ) :
    ∃ n : ℕ, ‖x (WithTopology.toTopology ⊥ n)‖ < 1 := by
  have h := Metric.tendsto_nhds.mp x.zero_at_infty' 1 zero_lt_one
  rw [Filter.cocompact_eq_cofinite] at h
  obtain ⟨j, hj⟩ := h.exists
  refine ⟨j.ofTopology, ?_⟩
  have hj' : ‖x.toFun j‖ < 1 := by simpa only [dist_zero_right] using hj
  change ‖x.toFun (WithTopology.toTopology ⊥ j.ofTopology)‖ < 1
  rw [WithTopology.toTopology_ofTopology]
  exact hj'

lemma functional_strict (x : CZero K ℕ) (hx : ‖x‖ = 1) :
    ‖functional x‖ < ‖functional (K := K)‖ := by
  have hle (n : ℕ) : ‖(weight n : K) * x (WithTopology.toTopology ⊥ n)‖ ≤ weight n := by
    rw [norm_mul, norm_weight]
    exact mul_le_of_le_one_right (weight_pos n).le ((X9CZero.apply_le x n).trans_eq hx)
  have hs : Summable (fun n : ℕ => ‖(weight n : K) * x (WithTopology.toTopology ⊥ n)‖) :=
    weight_summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle
  obtain ⟨i, hi⟩ := exists_small_coordinate x
  have hlt : ‖(weight i : K) * x (WithTopology.toTopology ⊥ i)‖ < weight i := by
    rw [norm_mul, norm_weight]
    exact mul_lt_of_lt_one_right (weight_pos i) hi
  rw [functional_apply, functional_norm]
  exact (norm_tsum_le_tsum_norm hs).trans_lt
    (Summable.tsum_lt_tsum hle hlt hs weight_summable)

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]

lemma realization_pure (f : CZero K ℕ →L[K] K) (y : Y) :
    projectiveRealization (K := K) (X := CZero K ℕ) (Y := Y) (pure f y) = f.smulRight y :=
  (bilinear_extension (K := K) (X := CZero K ℕ →L[K] K) (Y := Y)
    (Z := CZero K ℕ →L[K] Y)).2.1 _ f y

lemma quotient_operator (f : CZero K ℕ →L[K] K) (y : Y) :
    nuclearOperator (nuclearQuotient (pure f y)) = f.smulRight y := by
  change projectiveRealization (K := K) (X := CZero K ℕ) (Y := Y) (pure f y) = _
  exact realization_pure f y

end X9Nonattainment

variable {K : Type*} [RCLike K]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]

theorem solution (hi : ¬ FiniteDimensional K Y) (_hc : StrictlyConvex Y) :
    ∃ T : Nuclear K (CZero K ℕ) Y, NuclearAttains T ∧ ¬ OperatorAttains (nuclearOperator T) := by
  have hn : Nontrivial Y := not_subsingleton_iff_nontrivial.mp (by
    intro h
    letI : Subsingleton Y := h
    exact hi (inferInstance : FiniteDimensional K Y))
  letI := hn
  obtain ⟨y, hy⟩ := exists_ne (0 : Y)
  let f : CZero K ℕ →L[K] K := X9Nonattainment.functional
  let T : Nuclear K (CZero K ℕ) Y := nuclearQuotient (pure f y)
  refine ⟨T, (c0_l1_attainment (K := K) (Y := Y)).1 T, ?_⟩
  rw [show nuclearOperator T = f.smulRight y from X9Nonattainment.quotient_operator f y]
  rintro ⟨x, hx, hnorm⟩
  have hlt := mul_lt_mul_of_pos_right (X9Nonattainment.functional_strict x hx) (norm_pos_iff.mpr hy)
  have heq : ‖f x‖ * ‖y‖ = ‖f‖ * ‖y‖ := by
    simpa only [ContinuousLinearMap.smulRight_apply, norm_smul,
      ContinuousLinearMap.norm_smulRight_apply] using hnorm
  exact (ne_of_lt hlt) heq
