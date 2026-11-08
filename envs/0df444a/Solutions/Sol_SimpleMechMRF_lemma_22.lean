-- Prove2me | solution 1 for SimpleMechMRF.lemma_22
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:08:25.018063+00:00
-- url     : https://prove2.me/submissions/28f30d0d-1050-4c79-9be0-e52a7e5e49a6

import Mathlib
import Definitions.Def_SimpleMechMRF_TypeDist
import Definitions.Def_SimpleMechMRF_Mechanism
import Definitions.Def_SimpleMechMRF_Benchmark

open scoped NNReal

namespace Aux_SMMl22

open SimpleMechMRF

theorem prob_eq {n : ℕ} (D : TypeDist n) (S : Set (Fin n → ℝ≥0)) [DecidablePred (· ∈ S)] :
    D.prob S = ∑ t ∈ D.supp, if t ∈ S then D.pmf t else 0 := by
  unfold TypeDist.prob
  apply Finset.sum_congr rfl
  intro t _
  rw [Set.indicator_apply]

theorem marg_pos {n : ℕ} (D : TypeDist n) (i : Fin n) (s : ℝ≥0) (hs : s ∈ D.suppMarg i) :
    0 < D.marg i s := by
  classical
  unfold TypeDist.marg
  rw [prob_eq]
  obtain ⟨t, ht, hts⟩ := Finset.mem_image.mp hs
  apply lt_of_lt_of_le (D.pmf_pos t ht)
  have hnn : ∀ u ∈ D.supp, 0 ≤ (if u ∈ {t : Fin n → ℝ≥0 | t i = s} then D.pmf u else 0) := by
    intro u hu; split_ifs
    · exact (D.pmf_pos u hu).le
    · exact le_rfl
  have := Finset.single_le_sum hnn ht
  simp only [Set.mem_setOf_eq, hts, if_true] at this
  exact this

theorem fiber {n : ℕ} (D : TypeDist n) (i : Fin n) (F : (Fin n → ℝ≥0) → ℝ) :
    ∑ t ∈ D.supp, F t = ∑ s ∈ D.suppMarg i, ∑ t ∈ D.supp.filter (fun t => t i = s), F t := by
  rw [Finset.sum_fiberwise_of_maps_to]
  intro t ht
  exact Finset.mem_image_of_mem _ ht

end Aux_SMMl22

open SimpleMechMRF Aux_SMMl22 in
theorem solution {n : ℕ} (D : TypeDist n) (I : Finset (Finset (Fin n))) (M : Mechanism n)
    (hM : M.IsLottery I) (r : ℝ) :
    D.nonFavorite I M ≤ D.tail r + D.core r := by
  classical
  have halloc : ∀ i t, 0 ≤ M.alloc I i t ∧ M.alloc I i t ≤ 1 := by
    intro i t
    unfold Mechanism.alloc
    refine ⟨Finset.sum_nonneg (fun S _ => (hM t).1 S), ?_⟩
    calc ∑ S ∈ I.filter (fun S => i ∈ S), M.σ t S ≤ ∑ S ∈ I, M.σ t S :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun S _ _ => (hM t).1 S)
      _ ≤ 1 := (hM t).2
  set nf : Fin n → (Fin n → ℝ≥0) → ℝ := fun i t => if Favorite i t then 0 else 1 with hnf
  have hstep : D.nonFavorite I M ≤
      ∑ i, ∑ t ∈ D.supp, D.pmf t * (t i : ℝ) * nf i t * (if r < (t i : ℝ) then 1 else 0) +
      ∑ i, ∑ t ∈ D.supp, D.pmf t * (t i : ℝ) * (if (t i : ℝ) ≤ r then 1 else 0) := by
    unfold TypeDist.nonFavorite
    rw [Finset.sum_comm (s := D.supp), ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro t ht
    have hp := (D.pmf_pos t ht).le
    have hti : (0 : ℝ) ≤ (t i : ℝ) := (t i).2
    obtain ⟨ha0, ha1⟩ := halloc i t
    have hnf01 : 0 ≤ nf i t ∧ nf i t ≤ 1 := by simp only [hnf]; split_ifs <;> norm_num
    have hA1 : D.pmf t * M.alloc I i t * (t i : ℝ) * (if Favorite i t then 0 else 1) ≤
        D.pmf t * (t i : ℝ) * nf i t := by
      simp only [hnf]
      have : D.pmf t * M.alloc I i t * (t i : ℝ) ≤ D.pmf t * (t i : ℝ) := by
        nlinarith [mul_nonneg hp hti]
      split_ifs <;> nlinarith
    have hA2 : D.pmf t * (t i : ℝ) * nf i t ≤ D.pmf t * (t i : ℝ) := by
      nlinarith [mul_nonneg hp hti, hnf01.2]
    by_cases hr : r < (t i : ℝ)
    · rw [if_pos hr, if_neg (not_le.mpr hr)]
      linarith
    · rw [if_neg hr, if_pos (le_of_not_gt hr)]
      linarith [mul_nonneg (mul_nonneg hp hti) hnf01.1]
  refine hstep.trans (add_le_add (le_of_eq ?_) (le_of_eq ?_))
  · unfold TypeDist.tail
    apply Finset.sum_congr rfl; intro i _
    rw [fiber D i]
    conv_rhs => rw [Finset.sum_filter]
    apply Finset.sum_congr rfl; intro s hs
    have hm := marg_pos D i s hs
    have hinner : ∑ t ∈ D.supp.filter (fun t => t i = s),
        D.pmf t * (t i : ℝ) * nf i t * (if r < (t i : ℝ) then 1 else 0) =
        (if r < (s : ℝ) then (s : ℝ) else 0) *
          D.prob {u | u i = s ∧ u ∈ {u | ¬ Favorite i u}} := by
      rw [prob_eq, Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl; intro t _
      by_cases hts : t i = s
      · simp only [hts, if_true, Set.mem_setOf_eq, true_and, hnf]
        split_ifs <;> ring
      · simp only [hts, if_false, Set.mem_setOf_eq, false_and]
        ring
    rw [hinner]
    unfold TypeDist.condOnItem
    split_ifs with hr
    · field_simp
    · ring
  · unfold TypeDist.core
    apply Finset.sum_congr rfl; intro i _
    rw [fiber D i]
    conv_rhs => rw [Finset.sum_filter]
    apply Finset.sum_congr rfl; intro s _
    have hinner : ∑ t ∈ D.supp.filter (fun t => t i = s),
        D.pmf t * (t i : ℝ) * (if (t i : ℝ) ≤ r then 1 else 0) =
        (if (s : ℝ) ≤ r then (s : ℝ) else 0) * D.marg i s := by
      unfold TypeDist.marg
      rw [prob_eq, Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl; intro t _
      by_cases hts : t i = s
      · simp only [hts, if_true, Set.mem_setOf_eq]
        split_ifs <;> ring
      · simp only [hts, if_false, Set.mem_setOf_eq]
        ring
    rw [hinner]
    split_ifs <;> ring
