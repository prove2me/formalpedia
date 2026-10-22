-- Prove2me | solution 1 for StrategicAlloc.CutChoose.agent2_truthful_half
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:58:59.903465+00:00
-- url     : https://prove2.me/submissions/25656ea3-b525-4db0-9dd9-64d7c59a58d2

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_StrategicAlloc_CutChoose_Setting
import Definitions.Def_StrategicAlloc_CutChoose_ModCutChoose

set_option autoImplicit false
open StrategicAlloc.CutChoose

noncomputable def stepF {m : ℕ} (c : Fin m → ℝ) (E : Finset (Fin m) × Finset (Fin m)) (h : Fin m) :
    Finset (Fin m) × Finset (Fin m) :=
  if ∑ g ∈ E.1, c g ≤ ∑ g ∈ E.2, c g then (insert h E.1, E.2) else (E.1, insert h E.2)

lemma foldl_part {m : ℕ} (c : Fin m → ℝ) : ∀ (l : List (Fin m)), l.Nodup →
    ∀ (E : Finset (Fin m) × Finset (Fin m)), Disjoint E.1 E.2 →
    (∀ h ∈ l, h ∉ E.1 ∧ h ∉ E.2) →
    Disjoint (l.foldl (stepF c) E).1 (l.foldl (stepF c) E).2 ∧
      (l.foldl (stepF c) E).1 ∪ (l.foldl (stepF c) E).2 = E.1 ∪ E.2 ∪ l.toFinset := by
  intro l
  induction l with
  | nil =>
    intro _ E hd _
    simp [hd]
  | cons h t ih =>
    intro hl E hd hn
    rw [List.nodup_cons] at hl
    obtain ⟨hht, htn⟩ := hl
    have hhE := hn h (List.mem_cons_self)
    have hnt : ∀ x ∈ t, x ≠ h := fun x hx hxh => hht (hxh ▸ hx)
    rw [List.foldl_cons]
    by_cases hcnd : ∑ g ∈ E.1, c g ≤ ∑ g ∈ E.2, c g
    · have hs : stepF c E h = (insert h E.1, E.2) := by simp [stepF, hcnd]
      rw [hs]
      have hd' : Disjoint (insert h E.1, E.2).1 (insert h E.1, E.2).2 := by
        simp only
        rw [Finset.disjoint_insert_left]
        exact ⟨hhE.2, hd⟩
      have hn' : ∀ x ∈ t, x ∉ (insert h E.1, E.2).1 ∧ x ∉ (insert h E.1, E.2).2 := by
        intro x hx
        have := hn x (List.mem_cons_of_mem _ hx)
        simp only [Finset.mem_insert, not_or]
        exact ⟨⟨hnt x hx, this.1⟩, this.2⟩
      obtain ⟨a, b⟩ := ih htn (insert h E.1, E.2) hd' hn'
      refine ⟨a, ?_⟩
      rw [b]
      ext x
      simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]
      tauto
    · have hs : stepF c E h = (E.1, insert h E.2) := by simp [stepF, hcnd]
      rw [hs]
      have hd' : Disjoint (E.1, insert h E.2).1 (E.1, insert h E.2).2 := by
        simp only
        rw [Finset.disjoint_insert_right]
        exact ⟨hhE.1, hd⟩
      have hn' : ∀ x ∈ t, x ∉ (E.1, insert h E.2).1 ∧ x ∉ (E.1, insert h E.2).2 := by
        intro x hx
        have := hn x (List.mem_cons_of_mem _ hx)
        simp only [Finset.mem_insert, not_or]
        exact ⟨this.1, hnt x hx, this.2⟩
      obtain ⟨a, b⟩ := ih htn (E.1, insert h E.2) hd' hn'
      refine ⟨a, ?_⟩
      rw [b]
      ext x
      simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]
      tauto

lemma cut_part {m : ℕ} (c : Fin m → ℝ) :
    Disjoint (cut c).1 (cut c).2 ∧ (cut c).1 ∪ (cut c).2 = Finset.univ := by
  have hnd : (StrategicAlloc.RRFair.rank c).Nodup := by
    unfold StrategicAlloc.RRFair.rank
    exact (List.mergeSort_perm _ _).nodup_iff.mpr (List.nodup_finRange m)
  have hmem : ∀ x, x ∈ StrategicAlloc.RRFair.rank c := by
    intro x
    unfold StrategicAlloc.RRFair.rank
    exact (List.mergeSort_perm _ _).mem_iff.mpr (List.mem_finRange x)
  have key := foldl_part c (StrategicAlloc.RRFair.rank c) hnd (∅, ∅) (by simp) (by simp)
  have hcut : cut c = (StrategicAlloc.RRFair.rank c).foldl (stepF c) (∅, ∅) := rfl
  rw [hcut]
  refine ⟨key.1, ?_⟩
  rw [key.2]
  ext x
  simp [hmem x]

theorem solution {m : ℕ} (v : Fin 2 → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (b : Fin 2 → Fin m → ℝ) :
    StrategicAlloc.RRFair.val v 1 Finset.univ / 2 ≤
      StrategicAlloc.RRFair.val v 1 (modCutChoose (Function.update b 1 (v 1)) 1) := by
  have h0' : Function.update b 1 (v 1) 0 = b 0 := by simp [Function.update_apply]
  have h1' : Function.update b 1 (v 1) 1 = v 1 := by simp
  obtain ⟨hd, hu⟩ := cut_part (b 0)
  have hsum : StrategicAlloc.RRFair.val v 1 Finset.univ
      = ∑ g ∈ (cut (b 0)).1, v 1 g + ∑ g ∈ (cut (b 0)).2, v 1 g := by
    unfold StrategicAlloc.RRFair.val
    rw [← Finset.sum_union hd, hu]
  simp only [modCutChoose, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons, h0', h1']
  rw [hsum]
  unfold StrategicAlloc.RRFair.val
  split_ifs with hc <;> linarith
