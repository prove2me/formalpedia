-- Prove2me | solution 1 for ProjSchedTW.Complexity.maxCut_iff_stableSchedule
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T06:28:23.122647+00:00
-- url     : https://prove2.me/submissions/e1761039-72f9-40c4-871c-7e59f2b26f8c

import Mathlib
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_ProjSchedTW_Complexity_TimeConstrained

open ProjSchedTW.Complexity

private lemma mid_ne_zero {V : ℕ} (i : Fin V) : (i.castSucc.succ : Fin (V + 2)) ≠ 0 :=
  Fin.succ_ne_zero _

private lemma mid_ne_last {V : ℕ} (i : Fin V) : (i.castSucc.succ : Fin (V + 2)) ≠ Fin.last (V + 1) := by
  intro h; have := congrArg Fin.val h; simp at this; omega

private lemma zero_ne_last' (V : ℕ) : (0 : Fin (V + 2)) ≠ Fin.last (V + 1) := by
  intro h; have := congrArg Fin.val h; simp at this

private lemma last_ne_zero' (V : ℕ) : Fin.last (V + 1) ≠ (0 : Fin (V + 2)) :=
  (zero_ne_last' V).symm

private def E_mc (ν : ℕ) : Finset (Fin (ν + 2) × Fin (ν + 2)) :=
  Finset.univ.filter fun e : Fin (ν + 2) × Fin (ν + 2) =>
    (e.1 = 0 ∧ e.2 ≠ 0 ∧ e.2 ≠ Fin.last (ν + 1)) ∨
      (e.1 ≠ 0 ∧ e.1 ≠ Fin.last (ν + 1) ∧ e.2 = Fin.last (ν + 1))

private def δ_mc (ν : ℕ) (i j : Fin (ν + 2)) : ℤ :=
  if i ≠ 0 ∧ j = Fin.last (ν + 1) then 1 else 0

private lemma mem_E_mc (ν : ℕ) (i j : Fin (ν + 2)) : (i, j) ∈ E_mc ν ↔
    (i = 0 ∧ j ≠ 0 ∧ j ≠ Fin.last (ν + 1)) ∨
      (i ≠ 0 ∧ i ≠ Fin.last (ν + 1) ∧ j = Fin.last (ν + 1)) := by
  unfold E_mc; rw [Finset.mem_filter]; simp

private lemma sum_split_real {ν : ℕ} (g : Fin (ν + 2) → ℝ) :
    ∑ j : Fin (ν + 2), g j = g 0 + (∑ u : Fin ν, g u.castSucc.succ) + g (Fin.last (ν + 1)) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc, Fin.succ_last]; ring

open Classical in
private noncomputable def w_mc {ν : ℕ} (G : SimpleGraph (Fin ν)) (i j : Fin (ν + 2)) : ℕ :=
  if h : 0 < i.val ∧ i.val < ν + 1 ∧ 0 < j.val ∧ j.val < ν + 1 then
    (if G.Adj ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩ then 1 else 0)
  else 0

private lemma w_zero_left {ν : ℕ} (G : SimpleGraph (Fin ν)) (j : Fin (ν + 2)) :
    w_mc G 0 j = 0 := by
  simp [w_mc]

private lemma w_last_left {ν : ℕ} (G : SimpleGraph (Fin ν)) (j : Fin (ν + 2)) :
    w_mc G (Fin.last (ν + 1)) j = 0 := by
  simp [w_mc]

private lemma w_zero_right {ν : ℕ} (G : SimpleGraph (Fin ν)) (i : Fin (ν + 2)) :
    w_mc G i 0 = 0 := by
  simp [w_mc]

private lemma w_last_right {ν : ℕ} (G : SimpleGraph (Fin ν)) (i : Fin (ν + 2)) :
    w_mc G i (Fin.last (ν + 1)) = 0 := by
  simp [w_mc]

open Classical in
private lemma w_mid {ν : ℕ} (G : SimpleGraph (Fin ν)) (u v : Fin ν) :
    w_mc G u.castSucc.succ v.castSucc.succ = if G.Adj u v then 1 else 0 := by
  have hu := u.isLt
  have hv := v.isLt
  unfold w_mc
  rw [dif_pos ⟨by simp, by simp, by simp, by simp⟩]
  simp

open Classical in
private lemma deviation_eq_cutSize {ν : ℕ} (G : SimpleGraph (Fin ν)) (M : ℕ)
    (S : Fin (ν + 2) → ℝ) (h01 : ∀ u : Fin ν, S u.castSucc.succ = 0 ∨ S u.castSucc.succ = 1) :
    (maxCutProject G M).deviation S =
      (cutSize G (Finset.univ.filter (fun u : Fin ν => S u.castSucc.succ = 0)) : ℝ) := by
  let A : Finset (Fin ν) := Finset.univ.filter (fun u : Fin ν => S u.castSucc.succ = 0)
  have hmemA : ∀ u : Fin ν, u ∈ A ↔ S u.castSucc.succ = 0 := by
    intro u; simp [A]
  have hdev : (maxCutProject G M).deviation S =
      ∑ i : Fin (ν + 2), ∑ j : Fin (ν + 2),
        if i < j then (w_mc G i j : ℝ) * |S j - S i| else 0 := by
    unfold TCInstance.deviation
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_filter]
    rfl
  rw [hdev, sum_split_real]
  have hz0 : (∑ j : Fin (ν + 2),
      if (0 : Fin (ν + 2)) < j then (w_mc G 0 j : ℝ) * |S j - S 0| else 0) = 0 := by
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [w_zero_left]; simp
  have hzl : (∑ j : Fin (ν + 2),
      if Fin.last (ν + 1) < j then (w_mc G (Fin.last (ν + 1)) j : ℝ) *
        |S j - S (Fin.last (ν + 1))| else 0) = 0 := by
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [w_last_left]; simp
  rw [hz0, hzl, zero_add, add_zero]
  have hmid : ∀ u : Fin ν,
      (∑ j : Fin (ν + 2), if u.castSucc.succ < j then
        (w_mc G u.castSucc.succ j : ℝ) * |S j - S u.castSucc.succ| else 0) =
      ∑ v : Fin ν, if u < v ∧ G.Adj u v ∧ (u ∈ A ↔ v ∉ A) then (1 : ℝ) else 0 := by
    intro u
    rw [sum_split_real]
    have h0' : (if u.castSucc.succ < (0 : Fin (ν + 2)) then
        (w_mc G u.castSucc.succ 0 : ℝ) * |S 0 - S u.castSucc.succ| else 0) = 0 := by
      rw [w_zero_right]; simp
    have hl' : (if u.castSucc.succ < Fin.last (ν + 1) then
        (w_mc G u.castSucc.succ (Fin.last (ν + 1)) : ℝ) *
          |S (Fin.last (ν + 1)) - S u.castSucc.succ| else 0) = 0 := by
      rw [w_last_right]; simp
    rw [h0', hl', zero_add, add_zero]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [w_mid]
    have hlt_iff : (u.castSucc.succ < v.castSucc.succ) ↔ u < v :=
      ⟨fun h => by rw [Fin.lt_def] at h ⊢; simp at h; omega,
       fun h => by rw [Fin.lt_def] at h ⊢; simp; omega⟩
    by_cases hlt' : u < v
    · have hlt'' : u.castSucc.succ < v.castSucc.succ := hlt_iff.mpr hlt'
      rw [if_pos hlt'']
      have hu_iff := hmemA u
      have hv_iff := hmemA v
      rcases h01 u with hu | hu <;> rcases h01 v with hv | hv
      · have huA : u ∈ A := hu_iff.mpr hu
        have hvA : v ∈ A := hv_iff.mpr hv
        have hnot : ¬ (u < v ∧ G.Adj u v ∧ (u ∈ A ↔ v ∉ A)) :=
          fun ⟨_, _, h⟩ => (h.mp huA) hvA
        rw [hu, hv, if_neg hnot]
        norm_num
      · have huA : u ∈ A := hu_iff.mpr hu
        have hvA : v ∉ A := fun h => by linarith [hv_iff.mp h]
        have hcut : u ∈ A ↔ v ∉ A := ⟨fun _ => hvA, fun _ => huA⟩
        rw [hu, hv]
        by_cases hadj : G.Adj u v
        · rw [if_pos hadj, if_pos ⟨hlt', hadj, hcut⟩]; norm_num
        · have hnot : ¬ (u < v ∧ G.Adj u v ∧ (u ∈ A ↔ v ∉ A)) :=
            fun ⟨_, h, _⟩ => hadj h
          rw [if_neg hadj, if_neg hnot]; norm_num
      · have huA : u ∉ A := fun h => by linarith [hu_iff.mp h]
        have hvA : v ∈ A := hv_iff.mpr hv
        have hcut : u ∈ A ↔ v ∉ A := ⟨fun h => absurd h huA, fun h => absurd hvA h⟩
        rw [hu, hv]
        by_cases hadj : G.Adj u v
        · rw [if_pos hadj, if_pos ⟨hlt', hadj, hcut⟩]; norm_num
        · have hnot : ¬ (u < v ∧ G.Adj u v ∧ (u ∈ A ↔ v ∉ A)) :=
            fun ⟨_, h, _⟩ => hadj h
          rw [if_neg hadj, if_neg hnot]; norm_num
      · have huA : u ∉ A := fun h => by linarith [hu_iff.mp h]
        have hvA : v ∉ A := fun h => by linarith [hv_iff.mp h]
        have hnot : ¬ (u < v ∧ G.Adj u v ∧ (u ∈ A ↔ v ∉ A)) :=
          fun ⟨_, _, h⟩ => huA (h.mpr hvA)
        rw [hu, hv, if_neg hnot]
        norm_num
    · have hlt'' : ¬ (u.castSucc.succ < v.castSucc.succ) := fun h => hlt' (hlt_iff.mp h)
      rw [if_neg hlt'']
      simp [hlt']
  simp_rw [hmid]
  rw [← Fintype.sum_prod_type']
  unfold cutSize
  rw [Finset.sum_boole]

open Classical in
private noncomputable def S_of_cut {ν : ℕ} (A : Finset (Fin ν)) (j : Fin (ν + 2)) : ℝ :=
  if h : j = 0 ∨ j = Fin.last (ν + 1) then (if j = 0 then 0 else 2)
  else (if (⟨j.val - 1, by
      have := j.isLt
      simp only [not_or, Fin.ext_iff, Fin.val_zero, Fin.val_last] at h
      omega⟩ : Fin ν) ∈ A then 0 else 1)

private lemma S_of_cut_zero {ν : ℕ} (A : Finset (Fin ν)) : S_of_cut A 0 = 0 := by
  simp [S_of_cut]

private lemma S_of_cut_last {ν : ℕ} (A : Finset (Fin ν)) : S_of_cut A (Fin.last (ν + 1)) = 2 := by
  simp [S_of_cut, last_ne_zero']

private lemma S_of_cut_mid {ν : ℕ} (A : Finset (Fin ν)) (u : Fin ν) :
    S_of_cut A u.castSucc.succ = if u ∈ A then 0 else 1 := by
  unfold S_of_cut
  rw [dif_neg (by simp [mid_ne_zero, mid_ne_last])]
  simp

private lemma S_of_cut_nonneg {ν : ℕ} (A : Finset (Fin ν)) (j : Fin (ν + 2)) :
    0 ≤ S_of_cut A j := by
  unfold S_of_cut; split_ifs <;> norm_num

private lemma S_of_cut_01 {ν : ℕ} (A : Finset (Fin ν)) (i : Fin (ν + 2))
    (hi0 : i ≠ 0) (hil : i ≠ Fin.last (ν + 1)) :
    S_of_cut A i = 0 ∨ S_of_cut A i = 1 := by
  unfold S_of_cut
  rw [dif_neg (not_or.mpr ⟨hi0, hil⟩)]
  split_ifs <;> simp

private lemma S_of_cut_arcs {ν : ℕ} (A : Finset (Fin ν)) :
    ∀ e ∈ E_mc ν, (δ_mc ν e.1 e.2 : ℝ) ≤ S_of_cut A e.2 - S_of_cut A e.1 := by
  rintro ⟨i, j⟩ he
  rw [mem_E_mc] at he
  rcases he with ⟨rfl, hj0, hjl⟩ | ⟨hi0, hil, rfl⟩
  · simp [δ_mc, S_of_cut_zero, S_of_cut_nonneg]
  · unfold δ_mc
    rw [if_pos ⟨hi0, rfl⟩, Int.cast_one, S_of_cut_last]
    rcases S_of_cut_01 A i hi0 hil with h0 | h1 <;> linarith

private lemma S_of_cut_dbar {ν : ℕ} (A : Finset (Fin ν)) :
    S_of_cut A (Fin.last (ν + 1)) ≤ (2 : ℕ) := by
  rw [S_of_cut_last]; norm_num

open Classical in
theorem solution {ν : ℕ} (G : SimpleGraph (Fin ν)) (M : ℕ) :
    MaxCutYes G M ↔
      ∃ S, (maxCutProject G M).TimeFeasible S ∧
        (∀ i : Fin (ν + 2), i ≠ 0 → i ≠ Fin.last (ν + 1) → S i = 0 ∨ S i = 1) ∧
        (M : ℝ) ≤ (maxCutProject G M).deviation S := by
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨@S_of_cut ν A,
      ⟨S_of_cut_zero A, fun i => S_of_cut_nonneg A i, S_of_cut_arcs A, S_of_cut_dbar A⟩,
      fun i hi0 hil => S_of_cut_01 A i hi0 hil, ?_⟩
    have h01 : ∀ u : Fin ν, S_of_cut A u.castSucc.succ = 0 ∨ S_of_cut A u.castSucc.succ = 1 :=
      fun u => S_of_cut_01 A u.castSucc.succ (mid_ne_zero u) (mid_ne_last u)
    rw [deviation_eq_cutSize G M (@S_of_cut ν A) h01]
    have hfilter : Finset.univ.filter (fun u : Fin ν => S_of_cut A u.castSucc.succ = 0) = A := by
      ext u
      simp [S_of_cut_mid]
    rw [hfilter]
    exact_mod_cast hA
  · rintro ⟨S, _, h01, hdev⟩
    have h01' : ∀ u : Fin ν, S u.castSucc.succ = 0 ∨ S u.castSucc.succ = 1 :=
      fun u => h01 u.castSucc.succ (mid_ne_zero u) (mid_ne_last u)
    have hdev' : (M : ℝ) ≤
        (cutSize G (Finset.univ.filter (fun u : Fin ν => S u.castSucc.succ = 0)) : ℝ) := by
      rw [← deviation_eq_cutSize G M S h01']
      exact hdev
    refine ⟨Finset.univ.filter (fun u : Fin ν => S u.castSucc.succ = 0), ?_⟩
    exact_mod_cast hdev'
