-- Prove2me | solution 1 for TarchaBraids.thm_3_15_adjacent_word_one_endpoints_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T08:34:16.733856+00:00
-- url     : https://prove2.me/submissions/e1e52900-48e4-4608-be4b-c9e4637717d7

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1

namespace TarchaBraids

open BraidsLinksMCG

lemma braid_strand_eq_endpoint {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) : strandIdx j = strandIdxSucc i := by
  apply Fin.ext
  simp [strandIdx, strandIdxSucc, hji]

lemma halfTwistConfig_one_rev_endpoint (n : ℕ) (i : Fin (n - 1)) :
    (halfTwistConfig n i 1).1 =
      (baseOrdered n).1 ∘ Equiv.swap (strandIdx i) (strandIdxSucc i) := by
  funext k
  have h := congrFun (halfTwistConfig_one n i)
    ((Equiv.swap (strandIdx i) (strandIdxSucc i)) k)
  simpa [Function.comp_apply] using h.symm

lemma adjacent_swap_word_left_endpoint {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) :
    Equiv.swap (strandIdx i) (strandIdxSucc i) *
          Equiv.swap (strandIdx j) (strandIdxSucc j) *
          Equiv.swap (strandIdx i) (strandIdxSucc i) =
      Equiv.swap (strandIdx i) (strandIdxSucc j) := by
  have hbc : strandIdx j = strandIdxSucc i := braid_strand_eq_endpoint i j hji
  rw [hbc]
  set a := strandIdx i with ha
  set b := strandIdxSucc i with hb
  set d := strandIdxSucc j with hd
  have hda : d ≠ a := by
    simp [ha, hd, strandIdx, strandIdxSucc, Fin.ext_iff]
    omega
  have hdb : d ≠ b := by
    simp [hb, hd, strandIdxSucc, Fin.ext_iff]
    omega
  have h := Equiv.swap_apply_apply (Equiv.swap a b) b d
  rw [Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne hda hdb, Equiv.swap_inv] at h
  exact h.symm

lemma adjacent_swap_word_right_endpoint {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) :
    Equiv.swap (strandIdx j) (strandIdxSucc j) *
          Equiv.swap (strandIdx i) (strandIdxSucc i) *
          Equiv.swap (strandIdx j) (strandIdxSucc j) =
      Equiv.swap (strandIdx i) (strandIdxSucc j) := by
  have hbc : strandIdx j = strandIdxSucc i := braid_strand_eq_endpoint i j hji
  rw [hbc]
  set a := strandIdx i with ha
  set b := strandIdxSucc i with hb
  set d := strandIdxSucc j with hd
  have hda : d ≠ a := by
    simp [ha, hd, strandIdx, strandIdxSucc, Fin.ext_iff]
    omega
  have hab : a ≠ b := by
    simp [ha, hb, strandIdx, strandIdxSucc, Fin.ext_iff]
  have h := Equiv.swap_apply_apply (Equiv.swap b d) a b
  rw [Equiv.swap_apply_of_ne_of_ne hab (fun hc => hda hc.symm),
    Equiv.swap_apply_left, Equiv.swap_inv] at h
  exact h.symm

lemma leftBraidFun_one_endpoint {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) :
    leftBraidFun n i j 1 =
      (baseOrdered n).1 ∘ Equiv.swap (strandIdx i) (strandIdxSucc j) := by
  let si := Equiv.swap (strandIdx i) (strandIdxSucc i)
  let sj := Equiv.swap (strandIdx j) (strandIdxSucc j)
  let so := Equiv.swap (strandIdx i) (strandIdxSucc j)
  have hperm : si * sj * si = so := by
    simpa [si, sj, so] using adjacent_swap_word_left_endpoint i j hji
  funext k
  have hi1 := congrFun (halfTwistConfig_one_rev_endpoint n i) (sj (si k))
  have hp := DFunLike.congr_fun hperm k
  simp only [leftBraidFun, if_neg (by norm_num : ¬ (1 : ℝ) ≤ 1 / 2),
    if_neg (by norm_num : ¬ (1 : ℝ) ≤ 3 / 4), Function.comp_apply]
  norm_num
  change (halfTwistConfig n i 1).1 (sj (si k)) = (baseOrdered n).1 (so k)
  rw [hi1]
  exact congrArg (baseOrdered n).1 hp

lemma rightBraidFun_one_endpoint {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) :
    rightBraidFun n i j 1 =
      (baseOrdered n).1 ∘ Equiv.swap (strandIdx i) (strandIdxSucc j) := by
  let si := Equiv.swap (strandIdx i) (strandIdxSucc i)
  let sj := Equiv.swap (strandIdx j) (strandIdxSucc j)
  let so := Equiv.swap (strandIdx i) (strandIdxSucc j)
  have hperm : sj * si * sj = so := by
    simpa [si, sj, so] using adjacent_swap_word_right_endpoint i j hji
  funext k
  have hj1 := congrFun (halfTwistConfig_one_rev_endpoint n j) (si (sj k))
  have hp := DFunLike.congr_fun hperm k
  simp only [rightBraidFun, if_neg (by norm_num : ¬ (1 : ℝ) ≤ 1 / 2),
    if_neg (by norm_num : ¬ (1 : ℝ) ≤ 3 / 4), Function.comp_apply]
  norm_num
  change (halfTwistConfig n j 1).1 (si (sj k)) = (baseOrdered n).1 (so k)
  rw [hj1]
  exact congrArg (baseOrdered n).1 hp

end TarchaBraids

open BraidsLinksMCG TarchaBraids

theorem solution :
    ∀ {n : ℕ} (i j : Fin (n - 1)), (j : ℕ) = (i : ℕ) + 1 →
      leftBraidFun n i j 1 =
        (baseOrdered n).1 ∘ Equiv.swap (strandIdx i) (strandIdxSucc j) ∧
      rightBraidFun n i j 1 =
        (baseOrdered n).1 ∘ Equiv.swap (strandIdx i) (strandIdxSucc j) := by
  intro n i j hji
  exact ⟨leftBraidFun_one_endpoint i j hji, rightBraidFun_one_endpoint i j hji⟩
