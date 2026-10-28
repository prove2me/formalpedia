-- Prove2me | solution 2 for ProjSchedTW.Complexity.maxCut_iff_stableSchedule
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T06:37:22.679364+00:00
-- url     : https://prove2.me/submissions/6e4f9980-d14c-4971-850e-c7cea091f276

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_ProjSchedTW_Complexity_TimeConstrained

set_option autoImplicit false

namespace SolMaxCutIffStableSchedule

open Classical ProjSchedTW.Complexity

lemma mid_ne_zero {ν : ℕ} (u : Fin ν) : (u.castSucc.succ : Fin (ν + 2)) ≠ 0 := Fin.succ_ne_zero _

lemma mid_ne_last {ν : ℕ} (u : Fin ν) : (u.castSucc.succ : Fin (ν + 2)) ≠ Fin.last (ν + 1) := by
  intro h; have := congrArg Fin.val h; simp at this; omega

lemma zero_ne_last' (ν : ℕ) : (0 : Fin (ν + 2)) ≠ Fin.last (ν + 1) := by
  intro h; have := congrArg Fin.val h; simp at this

lemma last_ne_zero' (ν : ℕ) : Fin.last (ν + 1) ≠ (0 : Fin (ν + 2)) := (zero_ne_last' ν).symm

def Emc (ν : ℕ) : Finset (Fin (ν + 2) × Fin (ν + 2)) :=
  Finset.univ.filter fun e : Fin (ν + 2) × Fin (ν + 2) =>
    (e.1 = 0 ∧ e.2 ≠ 0 ∧ e.2 ≠ Fin.last (ν + 1)) ∨
      (e.1 ≠ 0 ∧ e.1 ≠ Fin.last (ν + 1) ∧ e.2 = Fin.last (ν + 1))

def δmc (ν : ℕ) (i j : Fin (ν + 2)) : ℤ :=
  if i ≠ 0 ∧ j = Fin.last (ν + 1) then 1 else 0

noncomputable def wmc {ν : ℕ} (G : SimpleGraph (Fin ν)) (i j : Fin (ν + 2)) : ℕ :=
  if h : 0 < i.val ∧ i.val < ν + 1 ∧ 0 < j.val ∧ j.val < ν + 1 then
    (if G.Adj ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩ then 1 else 0)
  else 0

lemma mem_Emc (ν : ℕ) (i j : Fin (ν + 2)) : (i, j) ∈ Emc ν ↔
    (i = 0 ∧ j ≠ 0 ∧ j ≠ Fin.last (ν + 1)) ∨
      (i ≠ 0 ∧ i ≠ Fin.last (ν + 1) ∧ j = Fin.last (ν + 1)) := by
  unfold Emc; rw [Finset.mem_filter]; simp

noncomputable def S_of_cut {ν : ℕ} (A : Finset (Fin ν)) (i : Fin (ν + 2)) : ℝ :=
  if h0 : i = 0 then 0
  else if hl : i = Fin.last (ν + 1) then 2
  else if (⟨i.val - 1, by
    have := i.isLt
    simp only [Fin.ext_iff, Fin.val_zero, Fin.val_last] at h0 hl
    omega⟩ : Fin ν) ∈ A then 1 else 0

lemma S_of_cut_zero {ν : ℕ} (A : Finset (Fin ν)) : S_of_cut A 0 = 0 := by simp [S_of_cut]

lemma S_of_cut_last {ν : ℕ} (A : Finset (Fin ν)) : S_of_cut A (Fin.last (ν + 1)) = 2 := by
  unfold S_of_cut
  rw [dif_neg (last_ne_zero' ν), dif_pos rfl]

lemma S_of_cut_mid {ν : ℕ} (A : Finset (Fin ν)) (u : Fin ν) :
    S_of_cut A u.castSucc.succ = if u ∈ A then 1 else 0 := by
  unfold S_of_cut
  rw [dif_neg (mid_ne_zero u), dif_neg (mid_ne_last u)]
  simp

lemma S_of_cut_nonneg {ν : ℕ} (A : Finset (Fin ν)) (i : Fin (ν + 2)) : 0 ≤ S_of_cut A i := by
  unfold S_of_cut; split_ifs <;> norm_num

lemma S_of_cut_real_le_one {ν : ℕ} (A : Finset (Fin ν)) (i : Fin (ν + 2))
    (h0 : i ≠ 0) (hl : i ≠ Fin.last (ν + 1)) : S_of_cut A i ≤ 1 := by
  unfold S_of_cut
  rw [dif_neg h0, dif_neg hl]
  split_ifs <;> norm_num

lemma S_of_cut_binary {ν : ℕ} (A : Finset (Fin ν)) (i : Fin (ν + 2))
    (h0 : i ≠ 0) (hl : i ≠ Fin.last (ν + 1)) : S_of_cut A i = 0 ∨ S_of_cut A i = 1 := by
  unfold S_of_cut
  rw [dif_neg h0, dif_neg hl]
  split_ifs <;> simp

lemma S_of_cut_arcs {ν : ℕ} (A : Finset (Fin ν)) :
    ∀ e ∈ Emc ν, (δmc ν e.1 e.2 : ℝ) ≤ S_of_cut A e.2 - S_of_cut A e.1 := by
  rintro ⟨i, j⟩ he
  rw [mem_Emc] at he
  rcases he with ⟨rfl, hj0, hjl⟩ | ⟨hi0, hil, rfl⟩
  · simp only [δmc, ne_eq, not_true_eq_false, false_and, if_false, Int.cast_zero, S_of_cut_zero, sub_zero]
    exact S_of_cut_nonneg A j
  · simp only [δmc, ne_eq, hi0, not_false_eq_true, true_and, if_true, Int.cast_one, S_of_cut_last]
    have := S_of_cut_real_le_one A i hi0 hil
    linarith

lemma S_of_cut_timeFeasible {ν : ℕ} (G : SimpleGraph (Fin ν)) (M : ℕ) (A : Finset (Fin ν)) :
    (maxCutProject G M).TimeFeasible (S_of_cut A) :=
  ⟨S_of_cut_zero A, S_of_cut_nonneg A, S_of_cut_arcs A, by
    change S_of_cut A (Fin.last (ν + 1)) ≤ (2 : ℝ); rw [S_of_cut_last]⟩

lemma wmc_zero_left {ν : ℕ} (G : SimpleGraph (Fin ν)) (j : Fin (ν + 2)) :
    wmc G 0 j = 0 := by simp [wmc]

lemma wmc_last_left {ν : ℕ} (G : SimpleGraph (Fin ν)) (j : Fin (ν + 2)) :
    wmc G (Fin.last (ν + 1)) j = 0 := by simp [wmc]

lemma wmc_zero_right {ν : ℕ} (G : SimpleGraph (Fin ν)) (i : Fin (ν + 2)) :
    wmc G i 0 = 0 := by simp [wmc]

lemma wmc_last_right {ν : ℕ} (G : SimpleGraph (Fin ν)) (i : Fin (ν + 2)) :
    wmc G i (Fin.last (ν + 1)) = 0 := by simp [wmc]

lemma wmc_mid_mid {ν : ℕ} (G : SimpleGraph (Fin ν)) (u v : Fin ν) :
    wmc G u.castSucc.succ v.castSucc.succ = if G.Adj u v then 1 else 0 := by
  have hu := u.isLt
  have hv := v.isLt
  simp only [wmc, Fin.val_succ, Fin.val_castSucc]
  rw [dif_pos ⟨by omega, by omega, by omega, by omega⟩]
  simp

lemma sum_filter_gt_last {ν : ℕ} (f : Fin (ν + 2) → ℝ) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin (ν + 2) => Fin.last (ν + 1) < j), f j = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  exact absurd hj (not_lt.mpr (Fin.le_last j))

lemma inner_sum_mid {ν : ℕ} (G : SimpleGraph (Fin ν)) (S : Fin (ν + 2) → ℝ) (u : Fin ν) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin (ν + 2) => u.castSucc.succ < j),
      (wmc G u.castSucc.succ j : ℝ) * |S j - S u.castSucc.succ| =
    ∑ v : Fin ν, if u < v ∧ G.Adj u v then |S v.castSucc.succ - S u.castSucc.succ| else 0 := by
  rw [Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_castSucc, Fin.succ_last]
  simp only [wmc_zero_right, wmc_last_right, Nat.cast_zero, zero_mul,
    ite_self, zero_add, add_zero, wmc_mid_mid]
  apply Finset.sum_congr rfl
  intro v _
  have hlt : (u.castSucc.succ < v.castSucc.succ) ↔ u < v := by
    simp only [Fin.lt_def, Fin.val_succ, Fin.val_castSucc]; omega
  by_cases huv : u < v <;> by_cases hadj : G.Adj u v
  · rw [if_pos (hlt.mpr huv)]; simp [huv, hadj]
  · rw [if_pos (hlt.mpr huv)]; simp [huv, hadj]
  · rw [if_neg (fun h => huv (hlt.mp h))]; simp [huv, hadj]
  · rw [if_neg (fun h => huv (hlt.mp h))]; simp [huv, hadj]

lemma deviation_eq_sum_pairs {ν : ℕ} (G : SimpleGraph (Fin ν)) (M : ℕ) (S : Fin (ν + 2) → ℝ) :
    (maxCutProject G M).deviation S =
      ∑ u : Fin ν, ∑ v : Fin ν,
        if u < v ∧ G.Adj u v then |S v.castSucc.succ - S u.castSucc.succ| else 0 := by
  change (∑ i : Fin (ν + 2), ∑ j ∈ Finset.univ.filter (fun j : Fin (ν + 2) => i < j),
    (wmc G i j : ℝ) * |S j - S i|) = _
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc, Fin.succ_last]
  have h0 : ∑ j ∈ Finset.univ.filter (fun j : Fin (ν + 2) => (0 : Fin (ν + 2)) < j),
      (wmc G 0 j : ℝ) * |S j - S 0| = 0 := by
    apply Finset.sum_eq_zero; intro j _; simp [wmc_zero_left]
  have hl : ∑ j ∈ Finset.univ.filter (fun j : Fin (ν + 2) => Fin.last (ν + 1) < j),
      (wmc G (Fin.last (ν + 1)) j : ℝ) * |S j - S (Fin.last (ν + 1))| = 0 :=
    sum_filter_gt_last _
  rw [h0, hl, zero_add, add_zero]
  exact Finset.sum_congr rfl (fun u _ => inner_sum_mid G S u)

lemma cutSize_cast {ν : ℕ} (G : SimpleGraph (Fin ν)) (A : Finset (Fin ν)) :
    (cutSize G A : ℝ) =
      ∑ u : Fin ν, ∑ v : Fin ν,
        if u < v ∧ G.Adj u v ∧ (u ∈ A ↔ v ∉ A) then (1 : ℝ) else 0 := by
  unfold cutSize
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one, Finset.sum_filter, Fintype.sum_prod_type]

lemma deviation_eq_cutSize {ν : ℕ} (G : SimpleGraph (Fin ν)) (M : ℕ) (S : Fin (ν + 2) → ℝ)
    (A : Finset (Fin ν))
    (hSA : ∀ u : Fin ν, S u.castSucc.succ = if u ∈ A then 1 else 0) :
    (maxCutProject G M).deviation S = (cutSize G A : ℝ) := by
  rw [deviation_eq_sum_pairs, cutSize_cast]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  rw [hSA u, hSA v]
  by_cases huv : u < v <;> by_cases hadj : G.Adj u v <;>
    by_cases hu : u ∈ A <;> by_cases hv : v ∈ A <;> simp [huv, hadj, hu, hv]

end SolMaxCutIffStableSchedule

open Classical ProjSchedTW.Complexity SolMaxCutIffStableSchedule in
theorem solution {ν : ℕ} (G : SimpleGraph (Fin ν)) (M : ℕ) :
    MaxCutYes G M ↔
      ∃ S, (maxCutProject G M).TimeFeasible S ∧
        (∀ i : Fin (ν + 2), i ≠ 0 → i ≠ Fin.last (ν + 1) → S i = 0 ∨ S i = 1) ∧
        (M : ℝ) ≤ (maxCutProject G M).deviation S := by
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨S_of_cut A, S_of_cut_timeFeasible G M A, S_of_cut_binary A, ?_⟩
    have hdev : (maxCutProject G M).deviation (S_of_cut A) = (cutSize G A : ℝ) :=
      deviation_eq_cutSize G M (S_of_cut A) A (S_of_cut_mid A)
    have hM : (M : ℝ) ≤ (cutSize G A : ℝ) := by exact_mod_cast hA
    exact hdev.symm ▸ hM
  · rintro ⟨S, _, hbin, hdev⟩
    let A : Finset (Fin ν) := Finset.univ.filter (fun u : Fin ν => S u.castSucc.succ = 1)
    have hSA : ∀ u : Fin ν, S u.castSucc.succ = if u ∈ A then 1 else 0 := by
      intro u
      have hb := hbin u.castSucc.succ (mid_ne_zero u) (mid_ne_last u)
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hb with h0 | h1
      · simp [h0]
      · simp [h1]
    have hdev' : (maxCutProject G M).deviation S = (cutSize G A : ℝ) :=
      deviation_eq_cutSize G M S A hSA
    have hM : (M : ℝ) ≤ (cutSize G A : ℝ) := hdev' ▸ hdev
    exact ⟨A, by exact_mod_cast hM⟩
