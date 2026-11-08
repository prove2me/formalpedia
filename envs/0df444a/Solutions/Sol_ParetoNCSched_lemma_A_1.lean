-- Prove2me | solution 1 for ParetoNCSched.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:37:43.553134+00:00
-- url     : https://prove2.me/submissions/d74d72b9-bc6c-45f8-8828-a043046f248e

import Mathlib
import Definitions.Def_ParetoNCSched_Phi
import Definitions.Def_ParetoNCSched_Phis
open scoped ENNReal
open MeasureTheory Set

namespace Aux_PNCA1

noncomputable def ind (c s : ℝ) : ℝ := if s < c then 1 else 0

theorem int_ind (c : ℝ) (hc : 0 ≤ c) :
    IntegrableOn (ind c) (Ioi 0) ∧ ∫ s in Ioi (0 : ℝ), ind c s = c := by
  have hfun : ind c = (Iio c).indicator (fun _ => (1 : ℝ)) := by
    funext s; simp [ind, Set.indicator_apply]
  rw [hfun]
  constructor
  · rw [integrableOn_indicator_iff measurableSet_Iio]
    have hs : volume (Iio c ∩ Ioi (0 : ℝ)) ≠ ∞ := by
      rw [Set.Iio_inter_Ioi, Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top
    exact integrableOn_const hs
  · rw [setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio, setIntegral_const,
      Real.volume_real_Ioo_of_le hc]
    simp

theorem ind_sq (c s : ℝ) : ind c s * ind c s = ind c s := by
  unfold ind; split_ifs <;> norm_num

theorem ind_min (a b s : ℝ) : ind (min a b) s = ind a s * ind b s := by
  unfold ind
  by_cases ha : s < a <;> by_cases hb : s < b <;> simp [ha, hb, lt_min_iff]

end Aux_PNCA1

open ParetoNCSched Aux_PNCA1 in
theorem solution {n : ℕ} (e : Fin n → ℝ) (he : ∀ j, 0 ≤ e j) :
    IntegrableOn (Phis e) (Ioi 0) ∧ Phi e = ∫ s in Ioi (0 : ℝ), Phis e s := by
  have hid : Phis e = fun s => ∑ j, ind (e j) s +
      ∑ i, ∑ j, (if i < j then ind (min (e i) (e j)) s else 0) := by
    funext s
    have hk : (ks e s : ℝ) = ∑ j, ind (e j) s := by
      unfold ks
      rw [Finset.card_filter]
      push_cast
      apply Finset.sum_congr rfl
      intro j _
      simp [ind]
    have hT : ∑ i, ∑ j, (if i < j then ind (min (e i) (e j)) s else 0) =
        ∑ i, ∑ j, (if i < j then ind (e i) s * ind (e j) s else 0) := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [ind_min]
    have hsplit : ∀ i j : Fin n, ind (e i) s * ind (e j) s =
        (if i < j then ind (e i) s * ind (e j) s else 0) +
        (if j < i then ind (e i) s * ind (e j) s else 0) +
        (if i = j then ind (e i) s * ind (e j) s else 0) := by
      intro i j
      rcases lt_trichotomy i j with h | h | h
      · simp [h, ne_of_lt h, not_lt_of_gt h]
      · subst h; simp
      · simp [h, ne_of_gt h, not_lt_of_gt h]
    have hsq : (∑ j, ind (e j) s) ^ 2 =
        2 * (∑ i, ∑ j, (if i < j then ind (e i) s * ind (e j) s else 0)) + ∑ j, ind (e j) s := by
      rw [sq, Finset.sum_mul_sum]
      rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hsplit i j))]
      simp only [Finset.sum_add_distrib]
      have h1 : ∑ i, ∑ j, (if j < i then ind (e i) s * ind (e j) s else 0) =
          ∑ i, ∑ j, (if i < j then ind (e i) s * ind (e j) s else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        split_ifs <;> ring
      have h2 : ∑ i, ∑ j, (if i = j then ind (e i) s * ind (e j) s else 0) =
          ∑ j, ind (e j) s := by
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _), ind_sq]
      rw [h1, h2]
      ring
    unfold Phis
    rw [hk, hT]
    linear_combination hsq / 2
  have hint : ∀ j, IntegrableOn (ind (e j)) (Ioi 0) := fun j => (int_ind _ (he j)).1
  have hint2 : ∀ i j : Fin n,
      IntegrableOn (fun s => if i < j then ind (min (e i) (e j)) s else 0) (Ioi 0) := by
    intro i j
    by_cases h : i < j
    · simp only [h, if_true]
      exact (int_ind _ (le_min (he i) (he j))).1
    · simp only [h, if_false]
      exact integrableOn_zero
  have hint3 : ∀ i : Fin n,
      IntegrableOn (fun s => ∑ j, if i < j then ind (min (e i) (e j)) s else 0) (Ioi 0) := by
    intro i
    exact integrable_finsetSum _ (fun j _ => hint2 i j)
  constructor
  · rw [hid]
    exact (integrable_finsetSum _ (fun j _ => hint j)).add
      (integrable_finsetSum _ (fun i _ => hint3 i))
  · rw [hid, integral_add (integrable_finsetSum _ (fun j _ => hint j))
      (integrable_finsetSum _ (fun i _ => hint3 i)),
      integral_finsetSum _ (fun j _ => hint j), integral_finsetSum _ (fun i _ => hint3 i)]
    unfold Phi
    congr 1
    · apply Finset.sum_congr rfl; intro j _
      exact ((int_ind _ (he j)).2).symm
    · apply Finset.sum_congr rfl; intro i _
      rw [integral_finsetSum _ (fun j _ => hint2 i j)]
      apply Finset.sum_congr rfl; intro j _
      by_cases h : i < j
      · simp only [h, if_true]
        exact ((int_ind _ (le_min (he i) (he j))).2).symm
      · simp only [h, if_false]
        simp
