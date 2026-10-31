-- Prove2me | solution 1 for PersonalizedRM.RevenueGap.revenue_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T18:32:55.097553+00:00
-- url     : https://prove2.me/submissions/02fd7f92-f6f9-4f7c-9705-3552af62ba78

import Mathlib
import Definitions.Def_PersonalizedRM_RevenueGap_Model

open MeasureTheory ProbabilityTheory
open PersonalizedRM.RevenueGap Finset

/-- Key bound on the derivative numerator of the softmax probability. -/
lemma PRM_aux_coeff {J : ℕ} (S : Finset (Fin J)) (e b : Fin J → ℝ) (he : ∀ l, 0 < e l)
    (j : Fin J) (hj : j ∈ S) :
    |b j * e j * (1 + ∑ l ∈ S, e l) - e j * ∑ l ∈ S, b l * e l| ≤
      (1 + ∑ l ∈ S, e l) ^ 2 / 4 * ∑ l ∈ S, |b l| := by
  set D := 1 + ∑ l ∈ S, e l with hD
  have hrw : b j * e j * D - e j * ∑ l ∈ S, b l * e l =
      ∑ l ∈ S, ((if l = j then e j * D else 0) - e j * e l) * b l := by
    rw [Finset.mul_sum]
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq' S j,
      if_pos hj]
    congr 1
    · ring
    · exact Finset.sum_congr rfl (fun l _ => by ring)
  rw [hrw, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l hl => ?_)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  have hsum_nn : ∀ T ⊆ S, ∑ m ∈ T, e m ≤ ∑ m ∈ S, e m := fun T hT =>
    Finset.sum_le_sum_of_subset_of_nonneg hT (fun m _ _ => (he m).le)
  by_cases hlj : l = j
  · subst hlj
    simp only [if_true]
    have h1 : e l ≤ D := by
      have := hsum_nn {l} (by simpa using hl); simp at this; linarith
    rw [abs_of_nonneg (by nlinarith [he l])]
    nlinarith [sq_nonneg (D - 2 * e l)]
  · simp only [hlj, if_false, zero_sub, abs_neg]
    have h2 : e j + e l ≤ D := by
      have := hsum_nn {j, l} (by
        intro m hm; simp at hm; rcases hm with rfl | rfl <;> assumption)
      rw [Finset.sum_pair (Ne.symm hlj)] at this; linarith
    rw [abs_of_nonneg (by nlinarith [he l, he j])]
    nlinarith [sq_nonneg (e j - e l), he l, he j]

/-- One-dimensional MVT bound for the MNL probability along a segment of utilities. -/
lemma PRM_aux_prob {J : ℕ} (S : Finset (Fin J)) (a b : Fin J → ℝ) (j : Fin J) (hj : j ∈ S) :
    |Real.exp (a j + b j) / (1 + ∑ l ∈ S, Real.exp (a l + b l)) -
      Real.exp (a j) / (1 + ∑ l ∈ S, Real.exp (a l))| ≤ 1 / 4 * ∑ l ∈ S, |b l| := by
  let E : Fin J → ℝ → ℝ := fun l t => Real.exp (a l + t * b l)
  let Dt : ℝ → ℝ := fun t => 1 + ∑ l ∈ S, E l t
  let Q : ℝ → ℝ := fun t => E j t / Dt t
  let Q' : ℝ → ℝ := fun t =>
    (b j * E j t * Dt t - E j t * ∑ l ∈ S, b l * E l t) / Dt t ^ 2
  have hE : ∀ l t, HasDerivAt (E l) (b l * E l t) t := by
    intro l t
    have := (((hasDerivAt_id t).mul_const (b l)).const_add (a l)).exp
    have h2 : HasDerivAt (E l) (Real.exp (a l + id t * b l) * (1 * b l)) t := this
    convert h2 using 1
    show b l * Real.exp (a l + t * b l) = Real.exp (a l + id t * b l) * (1 * b l)
    simp only [id, one_mul]; ring
  have hDpos : ∀ t, 0 < Dt t := fun t => by
    have : 0 ≤ ∑ l ∈ S, E l t := Finset.sum_nonneg (fun l _ => (Real.exp_pos _).le)
    simp only [Dt]; linarith
  have hD : ∀ t, HasDerivAt Dt (∑ l ∈ S, b l * E l t) t := fun t =>
    (HasDerivAt.fun_sum (fun l _ => hE l t)).const_add 1
  have hQ : ∀ t, HasDerivAt Q (Q' t) t := fun t => by
    exact (hE j t).div (hD t) (hDpos t).ne'
  obtain ⟨c, -, hc⟩ := exists_hasDerivAt_eq_slope Q Q' zero_lt_one
    (fun x _ => (hQ x).continuousAt.continuousWithinAt) (fun x _ => hQ x)
  have h1 : Q 1 = Real.exp (a j + b j) / (1 + ∑ l ∈ S, Real.exp (a l + b l)) := by
    simp [Q, E, Dt]
  have h0 : Q 0 = Real.exp (a j) / (1 + ∑ l ∈ S, Real.exp (a l)) := by
    simp [Q, E, Dt]
  rw [← h1, ← h0, show Q 1 - Q 0 = Q' c by rw [hc]; ring]
  have key := PRM_aux_coeff S (fun l => E l c) b (fun l => Real.exp_pos _) j hj
  have hDc := hDpos c
  simp only [Q', abs_div, abs_of_pos (pow_pos hDc 2)]
  rw [div_le_iff₀ (pow_pos hDc 2)]
  calc _ ≤ Dt c ^ 2 / 4 * ∑ l ∈ S, |b l| := key
    _ = _ := by ring

theorem solution {J d : ℕ} (θ θ' : Param J d) (z : Fin d → ℝ) (hz : ∀ k, |z k| ≤ 1)
    (S : Finset (Fin J)) (p : Fin J → ℝ) (hp : p ∈ priceBox J 0) :
    |revenue θ z S p - revenue θ' z S p| ≤
      (J : ℝ) / 4 * Real.sqrt ((J : ℝ) * ((d : ℝ) + 1)) * ‖θ - θ'‖ := by
  simp only [priceBox, Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies] at hp
  set Δ := θ - θ' with hΔ
  -- coordinates of the feature-price vector are bounded by 1
  have hx : ∀ l k, |featPrice z (p l) k| ≤ 1 := by
    intro l k
    refine Fin.lastCases ?_ (fun i => ?_) k
    · simp only [featPrice, Fin.snoc_last]; rw [abs_le]; constructor <;> linarith [(hp l).1, (hp l).2]
    · simp only [featPrice, Fin.snoc_castSucc]; exact hz i
  set a : Fin J → ℝ := fun l => utility θ' z p l with ha
  set b : Fin J → ℝ := fun l => utility θ z p l - utility θ' z p l with hb
  have hbl : ∀ l, |b l| ≤ ∑ k, |Δ (l, k)| := by
    intro l
    have : b l = ∑ k, Δ (l, k) * featPrice z (p l) k := by
      simp only [hb, utility, hΔ, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]
    rw [this]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hx l k)
  have hprob : ∀ j ∈ S, |choiceProb θ z S p (some j) - choiceProb θ' z S p (some j)| ≤
      1 / 4 * ∑ l ∈ S, |b l| := by
    intro j hj
    have := PRM_aux_prob S a b j hj
    simp only [ha, hb, add_sub_cancel] at this
    simpa [choiceProb, hj] using this
  have hl1 : ∑ l ∈ S, |b l| ≤ ∑ jk, |Δ jk| := by
    calc ∑ l ∈ S, |b l| ≤ ∑ l ∈ S, ∑ k, |Δ (l, k)| := Finset.sum_le_sum fun l _ => hbl l
      _ ≤ ∑ l, ∑ k, |Δ (l, k)| := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun l _ _ => Finset.sum_nonneg fun k _ => abs_nonneg _)
      _ = ∑ jk, |Δ jk| := (Fintype.sum_prod_type (fun jk => |Δ jk|)).symm
  have hcs : ∑ jk, |Δ jk| ≤ Real.sqrt ((J : ℝ) * ((d : ℝ) + 1)) * ‖Δ‖ := by
    rw [EuclideanSpace.norm_eq, ← Real.sqrt_mul (by positivity)]
    apply Real.le_sqrt_of_sq_le
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin J × Fin (d + 1))))
      (f := fun jk => |Δ jk|)
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, sq_abs] at this
    simpa [Real.norm_eq_abs, sq_abs] using this
  have hS : (S.card : ℝ) ≤ J := by
    have := Finset.card_le_univ S; simp at this; exact_mod_cast this
  have hb0 : 0 ≤ ∑ l ∈ S, |b l| := Finset.sum_nonneg fun l _ => abs_nonneg _
  calc |revenue θ z S p - revenue θ' z S p|
      = |∑ j ∈ S, p j * (choiceProb θ z S p (some j) - choiceProb θ' z S p (some j))| := by
        simp only [revenue, mul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ j ∈ S, |p j * (choiceProb θ z S p (some j) - choiceProb θ' z S p (some j))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ S, 1 / 4 * ∑ l ∈ S, |b l| := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [abs_mul]
        have hpj : |p j| ≤ 1 := by rw [abs_le]; constructor <;> linarith [(hp j).1, (hp j).2]
        calc |p j| * _ ≤ 1 * (1 / 4 * ∑ l ∈ S, |b l|) :=
              mul_le_mul hpj (hprob j hj) (abs_nonneg _) zero_le_one
          _ = _ := one_mul _
    _ = (S.card : ℝ) / 4 * ∑ l ∈ S, |b l| := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ (J : ℝ) / 4 * ∑ jk, |Δ jk| := by
        apply mul_le_mul (by linarith) hl1 hb0 (by positivity)
    _ ≤ (J : ℝ) / 4 * (Real.sqrt ((J : ℝ) * ((d : ℝ) + 1)) * ‖Δ‖) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = _ := by ring
