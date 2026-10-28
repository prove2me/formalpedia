-- Prove2me | solution 2 for ProjSchedTW.Complexity.partitionProject_feasible_iff
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T06:28:42.689222+00:00
-- url     : https://prove2.me/submissions/aad80591-df57-4ce7-bc6b-c5aa0fcafa85

import Mathlib
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_ProjSchedTW_Complexity_Cumulative

open ProjSchedTW.Complexity

private lemma mid_ne_zero {V : ℕ} (i : Fin V) : (i.castSucc.succ : Fin (V + 2)) ≠ 0 :=
  Fin.succ_ne_zero _

private lemma mid_ne_last {V : ℕ} (i : Fin V) : (i.castSucc.succ : Fin (V + 2)) ≠ Fin.last (V + 1) := by
  intro h; have := congrArg Fin.val h; simp at this; omega

private lemma zero_ne_last' (V : ℕ) : (0 : Fin (V + 2)) ≠ Fin.last (V + 1) := by
  intro h; have := congrArg Fin.val h; simp at this

private lemma last_ne_zero' (V : ℕ) : Fin.last (V + 1) ≠ (0 : Fin (V + 2)) :=
  (zero_ne_last' V).symm

private def Ep (ν : ℕ) : Finset (Fin (ν + 2) × Fin (ν + 2)) :=
  Finset.univ.filter fun e : Fin (ν + 2) × Fin (ν + 2) =>
    (e.1 = 0 ∧ e.2 ≠ 0) ∨ (e.1 ≠ 0 ∧ e.1 ≠ Fin.last (ν + 1) ∧ e.2 = Fin.last (ν + 1))

private def δp (ν : ℕ) (i j : Fin (ν + 2)) : ℤ :=
  if i = 0 ∧ j = Fin.last (ν + 1) then 1 else 0

private lemma mem_Ep (ν : ℕ) (i j : Fin (ν + 2)) : (i, j) ∈ Ep ν ↔
    (i = 0 ∧ j ≠ 0) ∨ (i ≠ 0 ∧ i ≠ Fin.last (ν + 1) ∧ j = Fin.last (ν + 1)) := by
  unfold Ep; rw [Finset.mem_filter]; simp

private def rp {ν : ℕ} (f : Fin ν → ℕ) (i : Fin (ν + 2)) : ℤ :=
  if i = 0 ∨ i = Fin.last (ν + 1) then -((∑ l, (f l : ℤ)) / 2) else (partitionSize f i : ℤ)

private lemma rp_mid {ν : ℕ} (f : Fin ν → ℕ) (i : Fin ν) : rp f i.castSucc.succ = (f i : ℤ) := by
  have := i.isLt
  simp only [rp, mid_ne_zero, mid_ne_last, or_self, if_false, partitionSize, Fin.val_succ,
    Fin.coe_castSucc]
  rw [dif_pos ⟨by omega, by omega⟩]
  simp

private lemma Ep_ord (ν : ℕ) : ∀ e ∈ Ep ν, e.1.val < e.2.val := by
  rintro ⟨i, j⟩ he
  rw [mem_Ep] at he
  rcases he with ⟨rfl, hj⟩ | ⟨-, hil, rfl⟩
  · have : j.val ≠ 0 := fun h => hj (Fin.ext (by simpa using h))
    simp only [Fin.val_zero]; omega
  · have : i.val ≠ ν + 1 := fun h => hil (Fin.ext (by simpa using h))
    have := i.isLt
    simp only [Fin.val_last]; omega

private lemma inv_formula {ν : ℕ} (f : Fin ν → ℕ) (S : Fin (ν + 2) → ℝ)
    (k : Fin (partitionProject f).m) (t : ℝ) :
    (partitionProject f).inventory S k t = ∑ j : Fin (ν + 2), if S j ≤ t then rp f j else 0 := by
  unfold CumInstance.inventory CumInstance.activeSet
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hr : (partitionProject f).r j k = rp f j := rfl
  have hp : ((partitionProject f).p j : ℝ) = 0 := by simp [partitionProject]
  rw [hr, hp]
  split_ifs with h1 h2 h2
  · rfl
  · exfalso; rcases h1 with ⟨-, h⟩ | ⟨-, h⟩ <;> linarith
  · rcases lt_trichotomy (rp f j) 0 with h | h | h
    · exact absurd (Or.inl ⟨h, h2⟩) h1
    · exact h.symm
    · exact absurd (Or.inr ⟨h, by linarith⟩) h1
  · rfl

private noncomputable def Sdef {ν : ℕ} (A : Finset (Fin ν)) (j : Fin (ν + 2)) : ℝ :=
  if h : j = 0 ∨ j = Fin.last (ν + 1) then (if j = 0 then 0 else 1)
  else (if (⟨j.val - 1, by
      have := j.isLt
      simp only [not_or, Fin.ext_iff, Fin.val_zero, Fin.val_last] at h
      omega⟩ : Fin ν) ∈ A then 0 else 1)

private lemma Sdef_zero {ν : ℕ} (A : Finset (Fin ν)) : Sdef A 0 = 0 := by simp [Sdef]

private lemma Sdef_last {ν : ℕ} (A : Finset (Fin ν)) : Sdef A (Fin.last (ν + 1)) = 1 := by
  simp [Sdef, last_ne_zero']

private lemma Sdef_mid {ν : ℕ} (A : Finset (Fin ν)) (i : Fin ν) :
    Sdef A i.castSucc.succ = if i ∈ A then 0 else 1 := by
  unfold Sdef
  rw [dif_neg (by simp [mid_ne_zero, mid_ne_last])]
  simp

private lemma Sdef_nonneg {ν : ℕ} (A : Finset (Fin ν)) (j : Fin (ν + 2)) : 0 ≤ Sdef A j := by
  unfold Sdef; split_ifs <;> norm_num

private lemma Sdef_le_one {ν : ℕ} (A : Finset (Fin ν)) (j : Fin (ν + 2)) : Sdef A j ≤ 1 := by
  unfold Sdef; split_ifs <;> norm_num

private lemma Sdef_arcs {ν : ℕ} (A : Finset (Fin ν)) :
    ∀ e ∈ Ep ν, (δp ν e.1 e.2 : ℝ) ≤ Sdef A e.2 - Sdef A e.1 := by
  rintro ⟨i, j⟩ he
  rw [mem_Ep] at he
  rcases he with ⟨rfl, hj⟩ | ⟨hi0, -, rfl⟩
  · simp only [δp, Sdef_zero, sub_zero, true_and]
    split_ifs with hjl
    · subst hjl; rw [Sdef_last]; norm_num
    · simpa using Sdef_nonneg A j
  · simp only [δp, hi0, false_and, if_false, Sdef_last, Int.cast_zero]
    linarith [Sdef_le_one A i]

private lemma sum_ite_mem_univ {ν : ℕ} (A : Finset (Fin ν)) (f : Fin ν → ℕ) :
    (∑ i, if i ∈ A then (f i : ℤ) else 0) = ((∑ i ∈ A, f i : ℕ) : ℤ) := by
  rw [Finset.sum_ite_mem, Finset.univ_inter]; push_cast; rfl

private lemma sum_split {ν : ℕ} (g : Fin (ν + 2) → ℤ) :
    ∑ j, g j = g 0 + ∑ i : Fin ν, g i.castSucc.succ + g (Fin.last (ν + 1)) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc, Fin.succ_last]; ring

private lemma inv_Sdef {ν : ℕ} (f : Fin ν → ℕ) (A : Finset (Fin ν))
    (hA : ∑ i ∈ A, f i = ∑ i ∈ Aᶜ, f i) (t : ℝ) (ht : 0 ≤ t) :
    (∑ j : Fin (ν + 2), if Sdef A j ≤ t then rp f j else 0) = 0 := by
  have htot := Finset.sum_add_sum_compl A f
  have hcast : (∑ l, (f l : ℤ)) = ((∑ l, f l : ℕ) : ℤ) := by push_cast; rfl
  have h0 : rp f 0 = -((∑ l, (f l : ℤ)) / 2) := by simp [rp]
  have hl : rp f (Fin.last (ν + 1)) = -((∑ l, (f l : ℤ)) / 2) := by simp [rp]
  rw [sum_split]
  simp only [Sdef_zero, Sdef_mid, Sdef_last, rp_mid, if_pos ht, h0, hl, hcast]
  by_cases h1 : 1 ≤ t
  · rw [if_pos h1]
    have : ∀ i : Fin ν, (if (if i ∈ A then (0 : ℝ) else 1) ≤ t then (f i : ℤ) else 0) = f i := by
      intro i; split_ifs with h <;> simp_all
    simp only [this, hcast]
    omega
  · rw [if_neg h1]
    have : ∀ i : Fin ν, (if (if i ∈ A then (0 : ℝ) else 1) ≤ t then (f i : ℤ) else 0) =
        if i ∈ A then (f i : ℤ) else 0 := by
      intro i; split_ifs with h h' h' <;> simp_all
    simp only [this, sum_ite_mem_univ]
    omega

theorem solution {ν : ℕ} (s : Fin ν → ℕ) (hs : Even (∑ i, s i)) :
    (partitionProject s).IsAcyclic ∧
      ((∃ S, (partitionProject s).Feasible S) ↔
        ∃ A : Finset (Fin ν), ∑ i ∈ A, s i = ∑ i ∈ Aᶜ, s i) := by
  refine ⟨⟨fun i => i.val, Ep_ord ν⟩, ?_, ?_⟩
  · rintro ⟨S, h⟩
    have hS0 : S (0 : Fin (ν + 2)) = 0 := h.1.1
    have harc : ((δp ν 0 (Fin.last (ν + 1)) : ℤ) : ℝ) ≤
        S (Fin.last (ν + 1) : Fin (ν + 2)) - S (0 : Fin (ν + 2)) :=
      h.1.2.2 ((0 : Fin (ν + 2)), Fin.last (ν + 1))
        (show ((0 : Fin (ν + 2)), Fin.last (ν + 1)) ∈ Ep ν from
          (mem_Ep ν _ _).2 (Or.inl ⟨rfl, last_ne_zero' ν⟩))
    have hlast : (1 : ℝ) ≤ S (Fin.last (ν + 1) : Fin (ν + 2)) := by
      simp [δp, hS0] at harc; linarith
    have h2 := h.2 ⟨0, Nat.one_pos⟩ 0 le_rfl
    rw [inv_formula s S] at h2
    change (0 : ℤ) ≤ _ ∧ _ ≤ (0 : ℤ) at h2
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc, Fin.succ_last] at h2
    simp only [hS0, le_refl, if_true, rp_mid] at h2
    rw [if_neg (by linarith)] at h2
    have h0 : rp s 0 = -((∑ l, (s l : ℤ)) / 2) := by simp [rp]
    rw [h0] at h2
    refine ⟨Finset.univ.filter (fun i : Fin ν => S (i.castSucc.succ : Fin (ν + 2)) ≤ 0), ?_⟩
    have hA : (∑ i : Fin ν, if S (i.castSucc.succ : Fin (ν + 2)) ≤ 0 then (s i : ℤ) else 0) =
        ((∑ i ∈ Finset.univ.filter (fun i : Fin ν => S (i.castSucc.succ : Fin (ν + 2)) ≤ 0),
          s i : ℕ) : ℤ) := by
      rw [Finset.sum_filter]; push_cast; rfl
    rw [hA] at h2
    have htot := Finset.sum_add_sum_compl
      (Finset.univ.filter (fun i : Fin ν => S (i.castSucc.succ : Fin (ν + 2)) ≤ 0)) s
    have hcast : (∑ l, (s l : ℤ)) = ((∑ l, s l : ℕ) : ℤ) := by push_cast; rfl
    rw [hcast] at h2
    rw [Nat.even_iff] at hs
    omega
  · rintro ⟨A, hA⟩
    refine ⟨@Sdef ν A, ⟨Sdef_zero A, fun i => Sdef_nonneg A i, Sdef_arcs A⟩, fun k t ht => ?_⟩
    rw [inv_formula s (@Sdef ν A)]
    change (0 : ℤ) ≤ _ ∧ _ ≤ (0 : ℤ)
    rw [inv_Sdef s A hA t ht]
    simp
