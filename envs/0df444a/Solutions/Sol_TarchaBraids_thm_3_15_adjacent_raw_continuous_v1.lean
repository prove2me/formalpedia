-- Prove2me | solution 1 for TarchaBraids.thm_3_15_adjacent_raw_continuous_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T08:26:03.32745+00:00
-- url     : https://prove2.me/submissions/71fa310e-09fb-417d-a9b2-8457069ad1c5

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1

namespace TarchaBraids

open BraidsLinksMCG

lemma halfTwistConfig_one_rev (n : ℕ) (i : Fin (n - 1)) :
    (halfTwistConfig n i 1).1 =
      (baseOrdered n).1 ∘ (Equiv.swap (strandIdx i) (strandIdxSucc i)) := by
  funext k
  have h := congrFun (halfTwistConfig_one n i)
    ((Equiv.swap (strandIdx i) (strandIdxSucc i)) k)
  simpa [Function.comp_apply] using h.symm

lemma halfTwistConfig_zero_fun (n : ℕ) (i : Fin (n - 1)) :
    (halfTwistConfig n i 0).1 = (baseOrdered n).1 := by
  exact congrArg Subtype.val (halfTwistConfig_zero n i)

lemma continuous_leftBraidFun_coord (n : ℕ) (i j : Fin (n - 1)) (k : Fin n) :
    Continuous (fun q : ℝ => leftBraidFun n i j q k) := by
  let si := Equiv.swap (strandIdx i) (strandIdxSucc i)
  let sj := Equiv.swap (strandIdx j) (strandIdxSucc j)
  have htail : Continuous (fun q : ℝ =>
      if q ≤ 3 / 4 then halfTwistFun n j (4 * q - 2) (si k)
      else halfTwistFun n i (4 * q - 3) (sj (si k))) := by
    apply continuous_if_le continuous_id continuous_const
    · simp only [halfTwistFun, twistPoint]; split_ifs <;> fun_prop
    · simp only [halfTwistFun, twistPoint]; split_ifs <;> fun_prop
    · intro q hq
      have hq' : q = (3 / 4 : ℝ) := hq
      subst q
      have hj1 := congrFun (halfTwistConfig_one_rev n j) (si k)
      have hi0 := congrFun (halfTwistConfig_zero_fun n i) (sj (si k))
      change halfTwistFun n j (4 * (3 / 4 : ℝ) - 2) (si k) =
        halfTwistFun n i (4 * (3 / 4 : ℝ) - 3) (sj (si k))
      norm_num
      exact hj1.trans hi0.symm
  unfold leftBraidFun
  change Continuous (fun q : ℝ =>
    if q ≤ 1 / 2 then halfTwistFun n i (2 * q) k
    else if q ≤ 3 / 4 then halfTwistFun n j (4 * q - 2) (si k)
    else halfTwistFun n i (4 * q - 3) (sj (si k)))
  apply continuous_if_le continuous_id continuous_const
  · simp only [halfTwistFun, twistPoint]; split_ifs <;> fun_prop
  · exact htail.continuousOn
  · intro q hq
    have hq' : q = (1 / 2 : ℝ) := hq
    subst q
    have hi1 := congrFun (halfTwistConfig_one_rev n i) k
    have hj0 := congrFun (halfTwistConfig_zero_fun n j) (si k)
    norm_num
    exact hi1.trans hj0.symm

lemma continuous_rightBraidFun_coord (n : ℕ) (i j : Fin (n - 1)) (k : Fin n) :
    Continuous (fun q : ℝ => rightBraidFun n i j q k) := by
  let si := Equiv.swap (strandIdx i) (strandIdxSucc i)
  let sj := Equiv.swap (strandIdx j) (strandIdxSucc j)
  have htail : Continuous (fun q : ℝ =>
      if q ≤ 3 / 4 then halfTwistFun n i (4 * q - 2) (sj k)
      else halfTwistFun n j (4 * q - 3) (si (sj k))) := by
    apply continuous_if_le continuous_id continuous_const
    · simp only [halfTwistFun, twistPoint]; split_ifs <;> fun_prop
    · simp only [halfTwistFun, twistPoint]; split_ifs <;> fun_prop
    · intro q hq
      have hq' : q = (3 / 4 : ℝ) := hq
      subst q
      have hi1 := congrFun (halfTwistConfig_one_rev n i) (sj k)
      have hj0 := congrFun (halfTwistConfig_zero_fun n j) (si (sj k))
      change halfTwistFun n i (4 * (3 / 4 : ℝ) - 2) (sj k) =
        halfTwistFun n j (4 * (3 / 4 : ℝ) - 3) (si (sj k))
      norm_num
      exact hi1.trans hj0.symm
  unfold rightBraidFun
  change Continuous (fun q : ℝ =>
    if q ≤ 1 / 2 then halfTwistFun n j (2 * q) k
    else if q ≤ 3 / 4 then halfTwistFun n i (4 * q - 2) (sj k)
    else halfTwistFun n j (4 * q - 3) (si (sj k)))
  apply continuous_if_le continuous_id continuous_const
  · simp only [halfTwistFun, twistPoint]; split_ifs <;> fun_prop
  · exact htail.continuousOn
  · intro q hq
    have hq' : q = (1 / 2 : ℝ) := hq
    subst q
    have hj1 := congrFun (halfTwistConfig_one_rev n j) k
    have hi0 := congrFun (halfTwistConfig_zero_fun n i) (sj k)
    norm_num
    exact hj1.trans hi0.symm

lemma continuous_outerRotateFun_coord (n : ℕ) (i : Fin (n - 1)) (k : Fin n) :
    Continuous (fun q : ℝ => outerRotateFun n i q k) := by
  unfold outerRotateFun
  split_ifs
  · simp only [twistPoint]; fun_prop
  · exact continuous_const
  · simp only [twistPoint]; fun_prop
  · exact continuous_const


end TarchaBraids

open BraidsLinksMCG TarchaBraids
theorem solution :
    (∀ (n : ℕ) (i j : Fin (n - 1)) (k : Fin n),
      Continuous (fun q : ℝ => leftBraidFun n i j q k)) ∧
    (∀ (n : ℕ) (i j : Fin (n - 1)) (k : Fin n),
      Continuous (fun q : ℝ => rightBraidFun n i j q k)) ∧
    (∀ (n : ℕ) (i : Fin (n - 1)) (k : Fin n),
      Continuous (fun q : ℝ => outerRotateFun n i q k)) := by
  exact ⟨continuous_leftBraidFun_coord,
    ⟨continuous_rightBraidFun_coord, continuous_outerRotateFun_coord⟩⟩

