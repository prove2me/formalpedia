-- Prove2me | solution 1 for Timetabling85.ClassTeacher.prop_2_1
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-13T09:53:45.042015+00:00
-- url     : https://prove2.me/submissions/8a83e806-8b13-4003-84a6-b16153257350

import Mathlib
import Definitions.Def_Timetabling85_ClassTeacher_Problems

namespace Timetabling85.ClassTeacher

theorem exists_injective_support {α : Type} [Fintype α] [DecidableEq α]
    (M : α → α → ℕ) (p : ℕ) (hp : 0 < p)
    (hrow : ∀ i : α, Finset.univ.sum (fun j : α => M i j) = p)
    (hcol : ∀ j : α, Finset.univ.sum (fun i : α => M i j) = p) :
    ∃ f : α → α, Function.Injective f ∧ ∀ i, 0 < M i (f i) := by
  classical
  let t (i : α) := Finset.univ.filter fun j => 0 < M i j
  have hrow' (i : α) : ∑ j ∈ t i, M i j = p := by
    rw [Finset.sum_filter]
    calc
      (∑ j ∈ Finset.univ, if 0 < M i j then M i j else 0) = ∑ j, M i j := by
        apply Finset.sum_congr rfl
        intro j hj
        split_ifs with h
        · rfl
        · have : M i j = 0 := by omega
          simp [this]
      _ = p := hrow i
  have hHall : ∀ s : Finset α, s.card ≤ (s.biUnion t).card := by
    intro s
    let u := s.biUnion t
    have hleft : (∑ i ∈ s, ∑ j ∈ t i, M i j) = s.card * p := by
      simp [hrow']
    have hright : (∑ i, ∑ j ∈ u, M i j) = u.card * p := by
      rw [Finset.sum_comm]
      simp [hcol]
    have hle1 : (∑ i ∈ s, ∑ j ∈ t i, M i j) ≤ ∑ i ∈ s, ∑ j ∈ u, M i j := by
      refine Finset.sum_le_sum fun i hi => ?_
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_biUnion_of_mem t hi) (by simp)
    have hle2 : (∑ i ∈ s, ∑ j ∈ u, M i j) ≤ ∑ i, ∑ j ∈ u, M i j := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (by simp) fun i hi hnot =>
        Finset.sum_nonneg fun j hj => Nat.zero_le _
    have hmul : s.card * p ≤ u.card * p := by
      rw [← hleft, ← hright]
      exact hle1.trans hle2
    exact Nat.le_of_mul_le_mul_right hmul hp
  obtain ⟨f, hf₁, hf₂⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hHall
  exact ⟨f, hf₁, fun i => by simpa [t] using hf₂ i⟩

private def matchEntry {α : Type} [DecidableEq α] (f : α → α) (i j : α) : ℕ :=
  if f i = j then 1 else 0

private def removeMatch {α : Type} [DecidableEq α] (M : α → α → ℕ) (f : α → α) (i j : α) : ℕ :=
  M i j - matchEntry f i j

theorem regularMatrixSchedule {α : Type} [Fintype α] [DecidableEq α] (p : ℕ) :
    ∀ (M : α → α → ℕ),
      (∀ i, ∑ j, M i j = p) →
      (∀ j, ∑ i, M i j = p) →
      ∃ x : α → α → Fin p → ℕ,
        (∀ i j, ∑ k, x i j k = M i j) ∧
        (∀ i k, ∑ j, x i j k ≤ 1) ∧
        (∀ j k, ∑ i, x i j k ≤ 1) ∧
        (∀ i j k, x i j k ≤ 1) := by
  induction p with
  | zero =>
      intro M hrow hcol
      have hzero (i j : α) : M i j = 0 := by
        have hle : M i j ≤ ∑ j, M i j :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
        rw [hrow i] at hle
        omega
      refine ⟨fun _ _ _ => 0, ?_, ?_, ?_, ?_⟩
      · intro i j
        simp [hzero]
      · intro i k
        exact Fin.elim0 k
      · intro j k
        exact Fin.elim0 k
      · intro i j k
        exact Fin.elim0 k
  | succ p ih =>
      intro M hrow hcol
      have hp : 0 < p.succ := by omega
      obtain ⟨f, hfinj, hpos⟩ := exists_injective_support M p.succ hp hrow hcol
      have hfsurj : Function.Surjective f := Finite.surjective_of_injective hfinj
      let g := matchEntry f
      let M' := removeMatch M f
      have hentry (i j : α) : M i j = g i j + M' i j := by
        by_cases h : f i = j
        · have hposij : 0 < M i j := by
            rw [← h]
            exact hpos i
          simp [g, M', matchEntry, removeMatch, h]
          omega
        · simp [g, M', matchEntry, removeMatch, h]
      have hsumg_row (i : α) : ∑ j, g i j = 1 := by
        rw [Finset.sum_eq_single_of_mem (f i) (Finset.mem_univ (f i)) (by
          intro j _ hne
          simp [g, matchEntry, Ne.symm hne])]
        simp [g, matchEntry]
      have hsumg_col (j : α) : ∑ i, g i j = 1 := by
        obtain ⟨i₀, hi₀⟩ := hfsurj j
        rw [Finset.sum_eq_single_of_mem i₀ (Finset.mem_univ i₀) (by
          intro i _ hne
          have hneq : f i ≠ j := by
            intro hij
            apply hne
            apply hfinj
            exact hij.trans hi₀.symm
          simp [g, matchEntry, hneq])]
        simp [g, matchEntry, hi₀]
      have hrow' (i : α) : ∑ j, M' i j = p := by
        have hsum : p.succ = 1 + ∑ j, M' i j := by
          calc
            p.succ = ∑ j, M i j := (hrow i).symm
            _ = ∑ j, (g i j + M' i j) := by
              apply Finset.sum_congr rfl
              intro j hj
              exact hentry i j
            _ = (∑ j, g i j) + ∑ j, M' i j := Finset.sum_add_distrib
            _ = 1 + ∑ j, M' i j := by rw [hsumg_row i]
        omega
      have hcol' (j : α) : ∑ i, M' i j = p := by
        have hsum : p.succ = 1 + ∑ i, M' i j := by
          calc
            p.succ = ∑ i, M i j := (hcol j).symm
            _ = ∑ i, (g i j + M' i j) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact hentry i j
            _ = (∑ i, g i j) + ∑ i, M' i j := Finset.sum_add_distrib
            _ = 1 + ∑ i, M' i j := by rw [hsumg_col j]
        omega
      obtain ⟨x', hxsum, hxrow, hxcol, hx01⟩ := ih M' hrow' hcol'
      let x : α → α → Fin p.succ → ℕ := fun i j k => Fin.cases (g i j) (x' i j) k
      refine ⟨x, ?_, ?_, ?_, ?_⟩
      · intro i j
        rw [Fin.sum_univ_succ]
        simp [x, hxsum]
        exact (hentry i j).symm
      · intro i k
        cases k using Fin.cases with
        | zero =>
            simpa [x] using (hsumg_row i).le
        | succ k =>
            simpa [x] using hxrow i k
      · intro j k
        cases k using Fin.cases with
        | zero =>
            simpa [x] using (hsumg_col j).le
        | succ k =>
            simpa [x] using hxcol j k
      · intro i j k
        cases k using Fin.cases with
        | zero =>
            change matchEntry f i j ≤ 1
            unfold matchEntry
            split_ifs <;> omega
        | succ k =>
            simpa [x] using hx01 i j k

theorem ct1_schedule_of_bounds {m n : ℕ} (R : Fin m → Fin n → ℕ) (p : ℕ)
    (hcol : ∀ j, colSum R j ≤ p) (hrow : ∀ i, rowSum R i ≤ p) :
    ∃ x : Fin m → Fin n → Fin p → ℕ, IsCT1 R p x := by
  classical
  let α := Fin m ⊕ Fin n
  let P : α → α → ℕ := fun u v =>
    match u, v with
    | Sum.inl i, Sum.inl i' => if i = i' then p - rowSum R i else 0
    | Sum.inl i, Sum.inr j => R i j
    | Sum.inr j, Sum.inl i => R i j
    | Sum.inr j, Sum.inr j' => if j = j' then p - colSum R j else 0
  have hProw : ∀ u, ∑ v, P u v = p := by
    intro u
    cases u with
    | inl i =>
        change (∑ v : Fin m ⊕ Fin n, P (Sum.inl i) v) = p
        rw [Fintype.sum_sum_type]
        simp [P, rowSum]
        have hi := hrow i
        unfold rowSum at hi
        omega
    | inr j =>
        change (∑ v : Fin m ⊕ Fin n, P (Sum.inr j) v) = p
        rw [Fintype.sum_sum_type]
        simp [P, colSum]
        have hj := hcol j
        unfold colSum at hj
        omega
  have hPcol : ∀ v, ∑ u, P u v = p := by
    intro v
    cases v with
    | inl i =>
        change (∑ u : Fin m ⊕ Fin n, P u (Sum.inl i)) = p
        rw [Fintype.sum_sum_type]
        simp [P, rowSum]
        have hi := hrow i
        unfold rowSum at hi
        omega
    | inr j =>
        change (∑ u : Fin m ⊕ Fin n, P u (Sum.inr j)) = p
        rw [Fintype.sum_sum_type]
        simp [P, colSum]
        have hj := hcol j
        unfold colSum at hj
        omega
  obtain ⟨y, hysum, hyrow, hycol, hy01⟩ := regularMatrixSchedule p P hProw hPcol
  let x : Fin m → Fin n → Fin p → ℕ := fun i j k => y (Sum.inl i) (Sum.inr j) k
  refine ⟨x, ?_, ?_, ?_, ?_⟩
  · intro i j
    have h := hysum (Sum.inl i) (Sum.inr j)
    simpa [x, P] using h
  · intro i k
    have h := hyrow (Sum.inl i) k
    change (∑ v : Fin m ⊕ Fin n, y (Sum.inl i) v k) ≤ 1 at h
    rw [Fintype.sum_sum_type] at h
    change ∑ j, y (Sum.inl i) (Sum.inr j) k ≤ 1
    omega
  · intro j k
    have h := hycol (Sum.inr j) k
    change (∑ u : Fin m ⊕ Fin n, y u (Sum.inr j) k) ≤ 1 at h
    rw [Fintype.sum_sum_type] at h
    change ∑ i, y (Sum.inl i) (Sum.inr j) k ≤ 1
    omega
  · intro i j k
    simpa [x] using hy01 (Sum.inl i) (Sum.inr j) k

end Timetabling85.ClassTeacher

open Timetabling85.ClassTeacher

theorem solution {m n : ℕ} (R : Fin m → Fin n → ℕ) (p : ℕ) :
    (∃ x : Fin m → Fin n → Fin p → ℕ, IsCT1 R p x) ↔
      (∀ j, colSum R j ≤ p) ∧ (∀ i, rowSum R i ≤ p) := by
  constructor
  · rintro ⟨x, hx⟩
    rcases hx with ⟨hsched, hclass, hteacher, h01⟩
    constructor
    · intro j
      calc
        colSum R j = ∑ i, ∑ k, x i j k := by
          simp only [colSum]
          apply Finset.sum_congr rfl
          intro i hi
          exact (hsched i j).symm
        _ = ∑ k, ∑ i, x i j k := Finset.sum_comm
        _ ≤ ∑ k, 1 := Finset.sum_le_sum fun k hk => hteacher j k
        _ = p := by simp
    · intro i
      calc
        rowSum R i = ∑ j, ∑ k, x i j k := by
          simp only [rowSum]
          apply Finset.sum_congr rfl
          intro j hj
          exact (hsched i j).symm
        _ = ∑ k, ∑ j, x i j k := Finset.sum_comm
        _ ≤ ∑ k, 1 := Finset.sum_le_sum fun k hk => hclass i k
        _ = p := by simp
  · rintro ⟨hcol, hrow⟩
    exact ct1_schedule_of_bounds R p hcol hrow

#print axioms solution
