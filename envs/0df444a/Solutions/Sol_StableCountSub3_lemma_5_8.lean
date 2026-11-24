-- Prove2me | solution 1 for StableCountSub3.lemma_5_8
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T18:06:54.257524+00:00
-- url     : https://prove2.me/submissions/ba5526d3-6680-4404-911e-d8eec2cf3a27
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_StableCountSub3_Credits
import Theorems.Thm_StableCountSub3_lemma_5_5

open StableMatching

namespace StableCountSub3.L58

open Classical

variable {n : ℕ}

theorem two_ne_three : (2 : ℕ∞) ≠ 3 := by
  intro h
  have : ((2 : ℕ) : ℕ∞) = ((3 : ℕ) : ℕ∞) := by exact_mod_cast h
  exact absurd (ENat.natCast_inj.mp this) (by decide)

theorem not_four_le_three : ¬ (4 : ℕ∞) ≤ 3 := by
  intro h
  have : ((4 : ℕ) : ℕ∞) ≤ ((3 : ℕ) : ℕ∞) := by exact_mod_cast h
  exact absurd (ENat.natCast_le_natCast.mp this) (by decide)

theorem inC_not_inB (I : Instance n) (D : Finset (Rot n)) (m : Fin n) (dir : Dir)
    (hC : InC I D m dir) : ¬ InB I D m dir := by
  intro hB
  have h := hB.2
  rw [hC.2] at h
  exact not_four_le_three h

theorem inI_not_simple (I : Instance n) (D : Finset (Rot n)) (hD : IsDownset I D) (dir : Dir)
    (a : Fin n) (ha : InI I D a dir) : ¬ InB I D a dir ∧ ¬ InC I D a dir := by
  obtain ⟨m, hm, rfl⟩ := ha
  have h := ((lemma_5_5 I D hD dir).1 m hm).2.1
  refine ⟨fun hB => ?_, fun hC => ?_⟩
  · rw [hB.1] at h; exact two_ne_three h
  · rw [hC.1] at h; exact two_ne_three h

theorem card_I_eq_card_C (I : Instance n) (D : Finset (Rot n)) (hD : IsDownset I D) (dir : Dir) :
    (Finset.univ.filter fun m => InI I D m dir).card =
      (Finset.univ.filter fun m => InC I D m dir).card := by
  have hset : (Finset.univ.filter fun m => InI I D m dir) =
      (Finset.univ.filter fun m => InC I D m dir).image fun m => image I D m dir := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    rfl
  rw [hset]
  apply Finset.card_image_of_injOn
  intro m hm m' hm' h
  simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hm hm'
  exact (lemma_5_5 I D hD dir).2 m m' hm hm' h

theorem basicCredit_eq (I : Instance n) (D : Finset (Rot n)) (hD : IsDownset I D) (dir : Dir)
    (m : Fin n) :
    basicCredit I D m dir =
      delta 1 - delta 1 * (if InC I D m dir then 1 else 0) +
        (delta 2 - delta 1) * (if InB I D m dir then 1 else 0) +
        delta 2 * (if InI I D m dir then 1 else 0) := by
  unfold basicCredit
  by_cases hC : InC I D m dir
  · have hB := inC_not_inB I D m dir hC
    have hI : ¬ InI I D m dir := fun hI => (inI_not_simple I D hD dir m hI).2 hC
    simp [hC, hB, hI]
  · by_cases hB : InB I D m dir
    · have hI : ¬ InI I D m dir := fun hI => (inI_not_simple I D hD dir m hI).1 hB
      simp [hC, hB, hI]
    · by_cases hI : InI I D m dir
      · simp [hC, hB, hI]
      · simp [hC, hB, hI]

end StableCountSub3.L58

open StableCountSub3 in
open Classical in
theorem solution {n : ℕ} (I : Instance n) (D : Finset (Rot n)) (hD : IsDownset I D)
    (dir : Dir) :
    ∑ m : Fin n, basicCredit I D m dir =
      n * delta 1 - (delta 1 - delta 2) *
        (((Finset.univ.filter fun m => InB I D m dir).card : ℝ) +
          ((Finset.univ.filter fun m => InC I D m dir).card : ℝ)) := by
  simp only [StableCountSub3.L58.basicCredit_eq I D hD dir]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [StableCountSub3.L58.card_I_eq_card_C I D hD dir]
  ring
