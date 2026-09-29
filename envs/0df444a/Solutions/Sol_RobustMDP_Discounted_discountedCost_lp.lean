-- Prove2me | solution 1 for RobustMDP.Discounted.discountedCost_lp
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:24:09.858734+00:00
-- url     : https://prove2.me/submissions/c113ddba-e937-49bd-9c99-d00218bdbb43

import Mathlib
import Definitions.Def_RobustMDP_Discounted_Model
import Definitions.Def_RobustMDP_Discounted_discountedCost

namespace RobustMDP.Discounted

lemma aux_dlp_row_nonneg {n : ℕ} {A : Type} (M : Model n A) (P : M.StationaryNature) (a : A)
    (i j : Fin n) : 0 ≤ P.1 a i j :=
  (M.rows_subset_simplex a i (P.2 a i)).1 j

lemma aux_dlp_row_sum {n : ℕ} {A : Type} (M : Model n A) (P : M.StationaryNature) (a : A)
    (i : Fin n) : ∑ j, P.1 a i j = 1 :=
  (M.rows_subset_simplex a i (P.2 a i)).2

lemma aux_dlp_dist_nonneg {n : ℕ} {A : Type} (M : Model n A) (π : StationaryPolicy n A)
    (P : M.StationaryNature) (i₀ : Fin n) : ∀ t k, 0 ≤ stateDist π P.1 i₀ t k := by
  intro t
  induction t with
  | zero => intro k; simp only [stateDist]; split_ifs <;> norm_num
  | succ t ih =>
    intro k
    simp only [stateDist]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (ih i) (aux_dlp_row_nonneg M P _ _ _))

lemma aux_dlp_dist_sum {n : ℕ} {A : Type} (M : Model n A) (π : StationaryPolicy n A)
    (P : M.StationaryNature) (i₀ : Fin n) : ∀ t, ∑ k, stateDist π P.1 i₀ t k = 1 := by
  intro t
  induction t with
  | zero => simp [stateDist]
  | succ t ih =>
    simp only [stateDist]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, aux_dlp_row_sum M P, mul_one]
    exact ih

lemma aux_dlp_dist_le_one {n : ℕ} {A : Type} (M : Model n A) (π : StationaryPolicy n A)
    (P : M.StationaryNature) (i₀ : Fin n) (t : ℕ) (k : Fin n) :
    stateDist π P.1 i₀ t k ≤ 1 := by
  rw [← aux_dlp_dist_sum M π P i₀ t]
  exact Finset.single_le_sum (fun j _ => aux_dlp_dist_nonneg M π P i₀ t j) (Finset.mem_univ k)

lemma aux_dlp_first_step {n : ℕ} {A : Type} (π : StationaryPolicy n A)
    (P : A → Fin n → Fin n → ℝ) (i : Fin n) :
    ∀ t k, stateDist π P i (t + 1) k = ∑ j, P (π i) i j * stateDist π P j t k := by
  intro t
  induction t with
  | zero => intro k; simp [stateDist]
  | succ t ih =>
    intro k
    rw [stateDist.eq_2]
    simp only []
    simp_rw [ih]
    simp only [stateDist]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma aux_dlp_summable {n : ℕ} {A : Type} (M : Model n A) (π : StationaryPolicy n A)
    (P : M.StationaryNature) (i₀ : Fin n) :
    Summable (fun t : ℕ => M.discount ^ t * ∑ i, stateDist π P.1 i₀ t i * M.cost i (π i)) := by
  apply Summable.of_nonneg_of_le (f := fun t => M.discount ^ t * ∑ i, M.cost i (π i))
  · intro t
    exact mul_nonneg (pow_nonneg M.discount_nonneg t)
      (Finset.sum_nonneg fun i _ => mul_nonneg (aux_dlp_dist_nonneg M π P i₀ t i)
        (M.cost_nonneg _ _))
  · intro t
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg M.discount_nonneg t)
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_of_le_one_left (M.cost_nonneg _ _) (aux_dlp_dist_le_one M π P i₀ t i)
  · exact (summable_geometric_of_lt_one M.discount_nonneg M.discount_lt_one).mul_right _

lemma aux_dlp_bellman {n : ℕ} {A : Type} (M : Model n A) (π : StationaryPolicy n A)
    (P : M.StationaryNature) (i : Fin n) :
    M.discountedCost i π P =
      M.cost i (π i) + M.discount * ∑ j, P.1 (π i) i j * M.discountedCost j π P := by
  unfold Model.discountedCost
  rw [(aux_dlp_summable M π P i).tsum_eq_zero_add]
  have h0 : M.discount ^ 0 * ∑ k, stateDist π P.1 i 0 k * M.cost k (π k) = M.cost i (π i) := by
    simp [stateDist]
  rw [h0]
  congr 1
  have h1 : ∀ t : ℕ, M.discount ^ (t + 1) * ∑ k, stateDist π P.1 i (t + 1) k * M.cost k (π k) =
      M.discount * ∑ j, P.1 (π i) i j *
        (M.discount ^ t * ∑ k, stateDist π P.1 j t k * M.cost k (π k)) := by
    intro t
    simp_rw [aux_dlp_first_step π P.1 i t]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  simp_rw [h1]
  rw [tsum_mul_left]
  congr 1
  rw [Summable.tsum_finsetSum (fun j _ => (aux_dlp_summable M π P j).mul_left _)]
  exact Finset.sum_congr rfl fun j _ => tsum_mul_left

lemma aux_dlp_iter {n : ℕ} {A : Type} (M : Model n A) (i₀ : Fin n) (π : StationaryPolicy n A)
    (P : M.StationaryNature) (v : Fin n → ℝ)
    (hv : ∀ i, v i ≤ M.cost i (π i) + M.discount * ∑ j, P.1 (π i) i j * v j) :
    ∀ N : ℕ, v i₀ ≤ ∑ t ∈ Finset.range N,
        M.discount ^ t * ∑ i, stateDist π P.1 i₀ t i * M.cost i (π i) +
      M.discount ^ N * ∑ k, stateDist π P.1 i₀ N k * v k := by
  intro N
  induction N with
  | zero => simp [stateDist]
  | succ N ih =>
    have key : ∑ k, stateDist π P.1 i₀ N k * v k ≤
        ∑ k, stateDist π P.1 i₀ N k * M.cost k (π k) +
          M.discount * ∑ j, stateDist π P.1 i₀ (N + 1) j * v j := by
      have e : ∑ j, stateDist π P.1 i₀ (N + 1) j * v j =
          ∑ k, stateDist π P.1 i₀ N k * ∑ j, P.1 (π k) k j * v j := by
        simp only [stateDist]
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      rw [e, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro k _
      have := mul_le_mul_of_nonneg_left (hv k) (aux_dlp_dist_nonneg M π P i₀ N k)
      linarith
    have hpow : 0 ≤ M.discount ^ N := pow_nonneg M.discount_nonneg N
    have := mul_le_mul_of_nonneg_left key hpow
    rw [Finset.sum_range_succ, pow_succ]
    nlinarith

theorem aux_dlp_main {n : ℕ} {A : Type} (M : Model n A) (i₀ : Fin n)
    (π : StationaryPolicy n A) (P : M.StationaryNature) :
    IsGreatest
      ((fun v : Fin n → ℝ => v i₀) ''
        {v | ∀ i, v i ≤ M.cost i (π i) + M.discount * ∑ j, P.1 (π i) i j * v j})
      (M.discountedCost i₀ π P) := by
  constructor
  · refine ⟨fun i => M.discountedCost i π P, ?_, rfl⟩
    intro i
    exact le_of_eq (aux_dlp_bellman M π P i)
  · rintro _ ⟨v, hv, rfl⟩
    simp only []
    set B : ℝ := ∑ k, |v k| with hB
    have hbound : ∀ N : ℕ, v i₀ ≤ M.discountedCost i₀ π P + M.discount ^ N * B := by
      intro N
      have h1 := aux_dlp_iter M i₀ π P v hv N
      have h2 : ∑ t ∈ Finset.range N,
          M.discount ^ t * ∑ i, stateDist π P.1 i₀ t i * M.cost i (π i) ≤
          M.discountedCost i₀ π P := by
        unfold Model.discountedCost
        apply (aux_dlp_summable M π P i₀).sum_le_tsum
        intro t _
        exact mul_nonneg (pow_nonneg M.discount_nonneg t)
          (Finset.sum_nonneg fun i _ => mul_nonneg (aux_dlp_dist_nonneg M π P i₀ t i)
            (M.cost_nonneg _ _))
      have h3 : ∑ k, stateDist π P.1 i₀ N k * v k ≤ B := by
        apply Finset.sum_le_sum
        intro k _
        have hn := aux_dlp_dist_nonneg M π P i₀ N k
        have h1' := aux_dlp_dist_le_one M π P i₀ N k
        calc stateDist π P.1 i₀ N k * v k ≤ stateDist π P.1 i₀ N k * |v k| :=
              mul_le_mul_of_nonneg_left (le_abs_self _) hn
          _ ≤ |v k| := mul_le_of_le_one_left (abs_nonneg _) h1'
      have hpow : 0 ≤ M.discount ^ N := pow_nonneg M.discount_nonneg N
      have h4 := mul_le_mul_of_nonneg_left h3 hpow
      linarith
    have ht : Filter.Tendsto (fun N : ℕ => M.discountedCost i₀ π P + M.discount ^ N * B)
        Filter.atTop (nhds (M.discountedCost i₀ π P + 0 * B)) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one M.discount_nonneg M.discount_lt_one).mul_const
        B).const_add _
    have := ge_of_tendsto' ht hbound
    simpa using this

end RobustMDP.Discounted

open RobustMDP.Discounted

theorem solution {n : ℕ} {A : Type} (M : Model n A) (i₀ : Fin n)
    (π : StationaryPolicy n A) (P : M.StationaryNature) :
    IsGreatest
      ((fun v : Fin n → ℝ => v i₀) ''
        {v | ∀ i, v i ≤ M.cost i (π i) + M.discount * ∑ j, P.1 (π i) i j * v j})
      (M.discountedCost i₀ π P) :=
  aux_dlp_main M i₀ π P
