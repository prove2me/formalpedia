-- Prove2me | solution 1 for TwoAgentSched.LateLate.theorem_7_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:36:22.021791+00:00
-- url     : https://prove2.me/submissions/adaecf81-94ce-4d01-8fac-6c260108999f

import Mathlib
import Definitions.Def_TwoAgentSched_LateLate_Model
import Definitions.Def_TwoAgentSched_LateLate_DPTable

set_option autoImplicit false
open TwoAgentSched.LateLate MooreLateJobs.Shared


lemma ll_ct_eq {ι : Type*} [DecidableEq ι] [Fintype ι] (t : ι → ℝ) (l : List ι)
    (hl : IsSchedule Finset.univ l) (j : ι) :
    completionTime t l j = ∑ y, if l.idxOf y ≤ l.idxOf j then t y else 0 := by
  have hj : j ∈ l := (hl.2 j).2 (Finset.mem_univ j)
  unfold completionTime completionAt
  have hnd' : (l.take (l.idxOf j + 1)).Nodup := hl.1.sublist (List.take_sublist _ _)
  rw [← List.sum_toFinset _ hnd', ← Finset.sum_filter]
  congr 1
  ext y
  have hyl : y ∈ l := (hl.2 y).2 (Finset.mem_univ y)
  simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [List.mem_take_iff_idxOf_lt hyl]
  omega

namespace LL
variable {n : ℕ} (p d : Fin n → ℕ) (ag : Fin n → Agent)

def fst {i : ℕ} (hi : i < n) (h k : ℕ) : WithTop ℕ :=
  C p d ag i h k + ((p ⟨i, hi⟩ : ℕ) : WithTop ℕ) +
    (if C p d ag i h k + ((p ⟨i, hi⟩ : ℕ) : WithTop ℕ) ≤ ((d ⟨i, hi⟩ : ℕ) : WithTop ℕ)
      then 0 else ⊤)

lemma C_succ_A {i : ℕ} (hi : i < n) (hA : ag ⟨i, hi⟩ = .A) (h k : ℕ) :
    C p d ag (i + 1) h k =
      min (fst p d ag hi h k) (if h = 0 then ⊤ else C p d ag i (h - 1) k) := by
  rw [C, dif_pos hi]
  simp only [hA]
  rfl

lemma C_succ_B {i : ℕ} (hi : i < n) (hB : ag ⟨i, hi⟩ = .B) (h k : ℕ) :
    C p d ag (i + 1) h k =
      min (fst p d ag hi h k) (if k = 0 then ⊤ else C p d ag i h (k - 1)) := by
  rw [C, dif_pos hi]
  simp only [hB]
  rfl

lemma prefix_succ {i : ℕ} (hi : i < n) :
    prefixJobs n (i + 1) = insert (⟨i, hi⟩ : Fin n) (prefixJobs n i) := by
  ext j
  simp only [prefixJobs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Fin.ext_iff]
  omega

lemma not_mem_prefix {i : ℕ} (hi : i < n) : (⟨i, hi⟩ : Fin n) ∉ prefixJobs n i := by
  simp [prefixJobs]

lemma diff_of_mem {i : ℕ} (hi : i < n) {E : Finset (Fin n)} (ha : (⟨i, hi⟩ : Fin n) ∈ E) :
    prefixJobs n (i + 1) \ E = prefixJobs n i \ E.erase ⟨i, hi⟩ := by
  ext j
  rw [prefix_succ hi]
  by_cases hj : j = ⟨i, hi⟩
  · subst hj; simp [ha, not_mem_prefix hi]
  · simp [hj]

lemma diff_of_not_mem {i : ℕ} (hi : i < n) {E : Finset (Fin n)} (ha : (⟨i, hi⟩ : Fin n) ∉ E) :
    prefixJobs n (i + 1) \ E = insert ⟨i, hi⟩ (prefixJobs n i \ E) := by
  rw [prefix_succ hi, Finset.insert_sdiff_of_notMem _ ha]

lemma ps_erase {i : ℕ} (hi : i < n) {h k : ℕ} {E : Finset (Fin n)}
    (hE : IsPartialSchedule p d ag (i + 1) h k E) (ha : (⟨i, hi⟩ : Fin n) ∈ E) :
    IsPartialSchedule p d ag i h k (E.erase ⟨i, hi⟩) := by
  obtain ⟨h1, h2, h3, h4⟩ := hE
  rw [diff_of_mem hi ha] at h3 h4
  refine ⟨?_, ?_, h3, h4⟩
  · intro j hj
    have := h1 (Finset.mem_of_mem_erase hj)
    rw [prefix_succ hi] at this
    rcases Finset.mem_insert.1 this with h | h
    · exact absurd h (Finset.ne_of_mem_erase hj)
    · exact h
  · intro j hj
    refine le_trans ?_ (h2 j (Finset.mem_of_mem_erase hj))
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset_filter _ (Finset.erase_subset _ _))

lemma ps_last {i : ℕ} (hi : i < n) {h k : ℕ} {E : Finset (Fin n)}
    (hE : IsPartialSchedule p d ag (i + 1) h k E) (ha : (⟨i, hi⟩ : Fin n) ∈ E) :
    ∑ j ∈ E, p j ≤ d ⟨i, hi⟩ := by
  obtain ⟨h1, h2, h3, h4⟩ := hE
  have := h2 _ ha
  have e : E.filter (fun x => x ≤ (⟨i, hi⟩ : Fin n)) = E := by
    apply Finset.filter_true_of_mem
    intro x hx
    have := h1 hx
    simp only [prefixJobs, Finset.mem_filter, Finset.mem_univ, true_and] at this
    rw [Fin.le_def]; show x.val ≤ i; omega
  rw [e] at this; exact this

lemma ps_insert {i : ℕ} (hi : i < n) {h k : ℕ} {E : Finset (Fin n)}
    (hE : IsPartialSchedule p d ag i h k E) (hd : ∑ j ∈ E, p j + p ⟨i, hi⟩ ≤ d ⟨i, hi⟩) :
    IsPartialSchedule p d ag (i + 1) h k (insert ⟨i, hi⟩ E) := by
  obtain ⟨h1, h2, h3, h4⟩ := hE
  have ha : (⟨i, hi⟩ : Fin n) ∉ E := fun h => not_mem_prefix hi (h1 h)
  have hdiff : prefixJobs n (i + 1) \ insert ⟨i, hi⟩ E = prefixJobs n i \ E := by
    ext j
    rw [prefix_succ hi]
    by_cases hj : j = ⟨i, hi⟩
    · subst hj; simp [not_mem_prefix hi]
    · simp [hj]
  rw [IsPartialSchedule, hdiff]
  refine ⟨?_, ?_, h3, h4⟩
  · intro j hj
    rw [prefix_succ hi]
    rcases Finset.mem_insert.1 hj with h | h
    · rw [h]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (h1 h)
  · intro j hj
    rcases Finset.mem_insert.1 hj with h | h
    · subst h
      have e : (insert (⟨i, hi⟩ : Fin n) E).filter (fun x => x ≤ (⟨i, hi⟩ : Fin n)) =
          insert ⟨i, hi⟩ E := by
        apply Finset.filter_true_of_mem
        intro x hx
        rcases Finset.mem_insert.1 hx with h | h
        · rw [h]
        · have := h1 h
          simp only [prefixJobs, Finset.mem_filter, Finset.mem_univ, true_and] at this
          rw [Fin.le_def]; show x.val ≤ i; omega
      rw [e, Finset.sum_insert ha]; omega
    · have hji : j < (⟨i, hi⟩ : Fin n) := by
        have := h1 h
        simp only [prefixJobs, Finset.mem_filter, Finset.mem_univ, true_and] at this
        rw [Fin.lt_def]; exact this
      have e : (insert (⟨i, hi⟩ : Fin n) E).filter (fun x => x ≤ j) = E.filter (fun x => x ≤ j) := by
        rw [Finset.filter_insert, if_neg (not_le.2 hji)]
      rw [e]; exact h2 j h

lemma ps_late_A {i : ℕ} (hi : i < n) (hA : ag ⟨i, hi⟩ = .A) {h k : ℕ} {E : Finset (Fin n)}
    (hE : IsPartialSchedule p d ag (i + 1) h k E) (ha : (⟨i, hi⟩ : Fin n) ∉ E) :
    ∃ h', h = h' + 1 ∧ IsPartialSchedule p d ag i h' k E := by
  obtain ⟨h1, h2, h3, h4⟩ := hE
  rw [diff_of_not_mem hi ha] at h3 h4
  have hn : (⟨i, hi⟩ : Fin n) ∉ prefixJobs n i \ E := fun h => not_mem_prefix hi (Finset.mem_sdiff.1 h).1
  rw [Finset.filter_insert, if_pos hA, Finset.card_insert_of_notMem
    (fun h => hn (Finset.mem_filter.1 h).1)] at h3
  rw [Finset.filter_insert, if_neg (by simp [hA])] at h4
  refine ⟨h - 1, by omega, ?_, h2, by omega, h4⟩
  intro j hj
  have := h1 hj
  rw [prefix_succ hi] at this
  rcases Finset.mem_insert.1 this with h | h
  · exact absurd (h ▸ hj) ha
  · exact h

lemma ps_late_B {i : ℕ} (hi : i < n) (hB : ag ⟨i, hi⟩ = .B) {h k : ℕ} {E : Finset (Fin n)}
    (hE : IsPartialSchedule p d ag (i + 1) h k E) (ha : (⟨i, hi⟩ : Fin n) ∉ E) :
    ∃ k', k = k' + 1 ∧ IsPartialSchedule p d ag i h k' E := by
  obtain ⟨h1, h2, h3, h4⟩ := hE
  rw [diff_of_not_mem hi ha] at h3 h4
  have hn : (⟨i, hi⟩ : Fin n) ∉ prefixJobs n i \ E := fun h => not_mem_prefix hi (Finset.mem_sdiff.1 h).1
  rw [Finset.filter_insert, if_pos hB, Finset.card_insert_of_notMem
    (fun h => hn (Finset.mem_filter.1 h).1)] at h4
  rw [Finset.filter_insert, if_neg (by simp [hB])] at h3
  refine ⟨k - 1, by omega, ?_, h2, h3, by omega⟩
  intro j hj
  have := h1 hj
  rw [prefix_succ hi] at this
  rcases Finset.mem_insert.1 this with h | h
  · exact absurd (h ▸ hj) ha
  · exact h

lemma ps_of_late_A {i : ℕ} (hi : i < n) (hA : ag ⟨i, hi⟩ = .A) {h k : ℕ} {E : Finset (Fin n)}
    (hE : IsPartialSchedule p d ag i h k E) :
    IsPartialSchedule p d ag (i + 1) (h + 1) k E := by
  obtain ⟨h1, h2, h3, h4⟩ := hE
  have ha : (⟨i, hi⟩ : Fin n) ∉ E := fun h => not_mem_prefix hi (h1 h)
  rw [IsPartialSchedule, diff_of_not_mem hi ha]
  have hfA : (insert (⟨i, hi⟩ : Fin n) (prefixJobs n i \ E)).filter (fun j => ag j = .A) =
      insert ⟨i, hi⟩ ((prefixJobs n i \ E).filter (fun j => ag j = .A)) := by
    rw [Finset.filter_insert, if_pos hA]
  have hfB : (insert (⟨i, hi⟩ : Fin n) (prefixJobs n i \ E)).filter (fun j => ag j = .B) =
      (prefixJobs n i \ E).filter (fun j => ag j = .B) := by
    rw [Finset.filter_insert, if_neg (by simp [hA])]
  rw [hfA, hfB]
  have hn : (⟨i, hi⟩ : Fin n) ∉ prefixJobs n i \ E := fun h => not_mem_prefix hi (Finset.mem_sdiff.1 h).1
  refine ⟨?_, h2, ?_, h4⟩
  · intro j hj; rw [prefix_succ hi]; exact Finset.mem_insert_of_mem (h1 hj)
  · rw [Finset.card_insert_of_notMem (fun h => hn (Finset.mem_filter.1 h).1)]; omega

lemma ps_of_late_B {i : ℕ} (hi : i < n) (hB : ag ⟨i, hi⟩ = .B) {h k : ℕ} {E : Finset (Fin n)}
    (hE : IsPartialSchedule p d ag i h k E) :
    IsPartialSchedule p d ag (i + 1) h (k + 1) E := by
  obtain ⟨h1, h2, h3, h4⟩ := hE
  have ha : (⟨i, hi⟩ : Fin n) ∉ E := fun h => not_mem_prefix hi (h1 h)
  rw [IsPartialSchedule, diff_of_not_mem hi ha]
  have hfB : (insert (⟨i, hi⟩ : Fin n) (prefixJobs n i \ E)).filter (fun j => ag j = .B) =
      insert ⟨i, hi⟩ ((prefixJobs n i \ E).filter (fun j => ag j = .B)) := by
    rw [Finset.filter_insert, if_pos hB]
  have hfA : (insert (⟨i, hi⟩ : Fin n) (prefixJobs n i \ E)).filter (fun j => ag j = .A) =
      (prefixJobs n i \ E).filter (fun j => ag j = .A) := by
    rw [Finset.filter_insert, if_neg (by simp [hB])]
  rw [hfA, hfB]
  have hn : (⟨i, hi⟩ : Fin n) ∉ prefixJobs n i \ E := fun h => not_mem_prefix hi (Finset.mem_sdiff.1 h).1
  refine ⟨?_, h2, h3, ?_⟩
  · intro j hj; rw [prefix_succ hi]; exact Finset.mem_insert_of_mem (h1 hj)
  · rw [Finset.card_insert_of_notMem (fun h => hn (Finset.mem_filter.1 h).1)]; omega


lemma fst_le {i : ℕ} (hi : i < n) {h k : ℕ} {E : Finset (Fin n)}
    (hIH : ∀ E, IsPartialSchedule p d ag i h k E → C p d ag i h k ≤ ((∑ j ∈ E, p j : ℕ) : WithTop ℕ))
    (hE : IsPartialSchedule p d ag (i + 1) h k E) (haE : (⟨i, hi⟩ : Fin n) ∈ E) :
    fst p d ag hi h k ≤ ((∑ j ∈ E, p j : ℕ) : WithTop ℕ) := by
  have h1 := hIH _ (ps_erase p d ag hi hE haE)
  have hsum := Finset.sum_erase_add E p haE
  have hd := ps_last p d ag hi hE haE
  have hle : C p d ag i h k + ((p ⟨i, hi⟩ : ℕ) : WithTop ℕ) ≤ ((∑ j ∈ E, p j : ℕ) : WithTop ℕ) := by
    calc C p d ag i h k + ((p ⟨i, hi⟩ : ℕ) : WithTop ℕ)
        ≤ ((∑ j ∈ E.erase ⟨i, hi⟩, p j : ℕ) : WithTop ℕ) + ((p ⟨i, hi⟩ : ℕ) : WithTop ℕ) :=
          add_le_add_left h1 _
      _ = ((∑ j ∈ E, p j : ℕ) : WithTop ℕ) := by rw [← hsum]; push_cast; rfl
  have hle2 : C p d ag i h k + ((p ⟨i, hi⟩ : ℕ) : WithTop ℕ) ≤ ((d ⟨i, hi⟩ : ℕ) : WithTop ℕ) :=
    hle.trans (by exact_mod_cast hd)
  unfold fst
  rw [if_pos hle2, add_zero]
  exact hle

lemma fst_att {i : ℕ} (hi : i < n) {h k : ℕ}
    (hIH : C p d ag i h k = ⊤ ∨ ∃ E, IsPartialSchedule p d ag i h k E ∧
      C p d ag i h k = ((∑ j ∈ E, p j : ℕ) : WithTop ℕ)) :
    fst p d ag hi h k = ⊤ ∨ ∃ E, IsPartialSchedule p d ag (i + 1) h k E ∧
      fst p d ag hi h k = ((∑ j ∈ E, p j : ℕ) : WithTop ℕ) := by
  rcases hIH with h0 | ⟨E, hE, hcE⟩
  · left; unfold fst; rw [h0]; simp
  · by_cases hle : C p d ag i h k + ((p ⟨i, hi⟩ : ℕ) : WithTop ℕ) ≤ ((d ⟨i, hi⟩ : ℕ) : WithTop ℕ)
    · right
      have hle' : ∑ j ∈ E, p j + p ⟨i, hi⟩ ≤ d ⟨i, hi⟩ := by
        rw [hcE] at hle; exact_mod_cast hle
      have ha : (⟨i, hi⟩ : Fin n) ∉ E := fun h => not_mem_prefix hi (hE.1 h)
      refine ⟨insert ⟨i, hi⟩ E, ps_insert p d ag hi hE hle', ?_⟩
      unfold fst
      rw [if_pos hle, add_zero, hcE, Finset.sum_insert ha]
      push_cast; rw [add_comm]
    · left; unfold fst; rw [if_neg hle]; simp


lemma C_spec : ∀ i, i ≤ n → ∀ h k : ℕ,
    (∀ E, IsPartialSchedule p d ag i h k E → C p d ag i h k ≤ ((∑ j ∈ E, p j : ℕ) : WithTop ℕ)) ∧
    (C p d ag i h k = ⊤ ∨ ∃ E, IsPartialSchedule p d ag i h k E ∧
        C p d ag i h k = ((∑ j ∈ E, p j : ℕ) : WithTop ℕ)) := by
  intro i
  induction i with
  | zero =>
    intro _ h k
    have hC : C p d ag 0 h k = 0 := by rw [C]
    have hps : IsPartialSchedule p d ag 0 h k ∅ := by
      refine ⟨Finset.empty_subset _, fun j hj => absurd hj (Finset.notMem_empty _), ?_, ?_⟩ <;>
      simp [prefixJobs]
    refine ⟨fun E hE => ?_, Or.inr ⟨∅, hps, by rw [hC]; simp⟩⟩
    have hE0 : E = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      have := hE.1 hx
      simp [prefixJobs] at this
    subst hE0
    rw [hC]; simp
  | succ i ih =>
    intro hi' h k
    have hi : i < n := hi'
    have ih' := ih hi.le
    have hfst_le : ∀ E, IsPartialSchedule p d ag (i + 1) h k E → (⟨i, hi⟩ : Fin n) ∈ E →
        fst p d ag hi h k ≤ ((∑ j ∈ E, p j : ℕ) : WithTop ℕ) :=
      fun E hE haE => fst_le p d ag hi (ih' h k).1 hE haE
    have hfst_att := fst_att p d ag hi (ih' h k).2
    rcases hag : ag ⟨i, hi⟩ with _ | _
    · -- A-job
      rw [C_succ_A p d ag hi hag]
      constructor
      · intro E hE
        by_cases haE : (⟨i, hi⟩ : Fin n) ∈ E
        · exact (min_le_left _ _).trans (hfst_le E hE haE)
        · obtain ⟨h', rfl, hE'⟩ := ps_late_A p d ag hi hag hE haE
          refine (min_le_right _ _).trans ?_
          simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, Nat.add_sub_cancel]
          exact (ih' (h' + 1 - 1) k).1 E (by simpa using hE')
      · rcases min_choice (fst p d ag hi h k)
            (if h = 0 then (⊤ : WithTop ℕ) else C p d ag i (h - 1) k) with hm | hm
        · rw [hm]; exact hfst_att.imp_right (fun ⟨E, hE, he⟩ => ⟨E, hE, he⟩)
        · rw [hm]
          by_cases h0 : h = 0
          · left; simp [h0]
          · rw [if_neg h0]
            rcases (ih' (h - 1) k).2 with h1 | ⟨E, hE, hcE⟩
            · left; exact h1
            · right
              refine ⟨E, ?_, hcE⟩
              have := ps_of_late_A p d ag hi hag hE
              rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero h0)] at this
    · -- B-job
      rw [C_succ_B p d ag hi hag]
      constructor
      · intro E hE
        by_cases haE : (⟨i, hi⟩ : Fin n) ∈ E
        · exact (min_le_left _ _).trans (hfst_le E hE haE)
        · obtain ⟨k', rfl, hE'⟩ := ps_late_B p d ag hi hag hE haE
          refine (min_le_right _ _).trans ?_
          simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, Nat.add_sub_cancel]
          exact (ih' h (k' + 1 - 1)).1 E (by simpa using hE')
      · rcases min_choice (fst p d ag hi h k)
            (if k = 0 then (⊤ : WithTop ℕ) else C p d ag i h (k - 1)) with hm | hm
        · rw [hm]; exact hfst_att
        · rw [hm]
          by_cases h0 : k = 0
          · left; simp [h0]
          · rw [if_neg h0]
            rcases (ih' h (k - 1)).2 with h1 | ⟨E, hE, hcE⟩
            · left; exact h1
            · right
              refine ⟨E, ?_, hcE⟩
              have := ps_of_late_B p d ag hi hag hE
              rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero h0)] at this

end LL

section lib
variable {n : ℕ} (p d : Fin n → ℕ) (ag : Fin n → Agent)

def cN (l : List (Fin n)) (j : Fin n) : ℕ :=
  ∑ y ∈ Finset.univ.filter (fun y => l.idxOf y ≤ l.idxOf j), p y

lemma ct_eq (l : List (Fin n)) (hl : IsSchedule Finset.univ l) (j : Fin n) :
    completionTime (fun j => (p j : ℝ)) l j = (cN p l j : ℝ) := by
  rw [ll_ct_eq _ l hl j]
  unfold cN
  push_cast
  rw [Finset.sum_filter]

lemma lateSet_eq (l : List (Fin n)) (hl : IsSchedule Finset.univ l) :
    MooreLateJobs.NumLate.lateSet (fun j => (p j : ℝ)) (fun j => (d j : ℝ)) l =
      Finset.univ.filter (fun j => d j < cN p l j) := by
  unfold MooreLateJobs.NumLate.lateSet
  ext j
  have hj : j ∈ l := (hl.2 j).2 (Finset.mem_univ j)
  simp only [Finset.mem_filter, List.mem_toFinset, Finset.mem_univ, true_and]
  rw [ct_eq p l hl j]
  constructor
  · rintro ⟨_, h⟩; exact_mod_cast h
  · intro h; exact ⟨hj, by exact_mod_cast h⟩

lemma numLate_eq (l : List (Fin n)) (hl : IsSchedule Finset.univ l) (X : Agent) :
    numLate p d ag X l =
      ((Finset.univ.filter (fun j => d j < cN p l j)).filter (fun j => ag j = X)).card := by
  unfold numLate
  rw [lateSet_eq p d l hl]

lemma jackson (l : List (Fin n)) (T : Finset (Fin n)) (hT : T.Nonempty) (D : ℕ)
    (hE : ∀ y ∈ T, cN p l y ≤ d y) (hD : ∀ y ∈ T, d y ≤ D) : ∑ y ∈ T, p y ≤ D := by
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image T (fun x => l.idxOf x) hT
  calc ∑ y ∈ T, p y ≤ cN p l m := by
        unfold cN
        refine Finset.sum_le_sum_of_subset (fun y hy => ?_)
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hmax y hy⟩
    _ ≤ d m := hE m hm
    _ ≤ D := hD m hm

end lib

section lib2
variable {n : ℕ} (p d : Fin n → ℕ) (ag : Fin n → Agent)

lemma early_feasible (hd : Monotone d) (l : List (Fin n)) :
    IsEarlyFeasible p d (Finset.univ.filter (fun j => cN p l j ≤ d j)) := by
  intro j hj
  refine jackson p d l ((Finset.univ.filter (fun j => cN p l j ≤ d j)).filter (fun i => i ≤ j))
    ⟨j, Finset.mem_filter.2 ⟨hj, le_refl _⟩⟩ (d j) ?_ ?_
  · intro y hy
    exact (Finset.mem_filter.1 (Finset.mem_filter.1 hy).1).2
  · intro y hy
    exact hd (Finset.mem_filter.1 hy).2

lemma prefix_n : prefixJobs n n = Finset.univ := by
  ext j; simp [prefixJobs, j.2]

lemma ps_of_sched (hd : Monotone d) (l : List (Fin n)) (hl : IsSchedule Finset.univ l) :
    IsPartialSchedule p d ag n (numLate p d ag .A l) (numLate p d ag .B l)
      (Finset.univ.filter (fun j => cN p l j ≤ d j)) := by
  have hdiff : prefixJobs n n \ (Finset.univ.filter (fun j => cN p l j ≤ d j)) =
      Finset.univ.filter (fun j => d j < cN p l j) := by
    ext j; simp [prefix_n]
  refine ⟨?_, early_feasible p d hd l, ?_, ?_⟩
  · rw [prefix_n]; exact Finset.subset_univ _
  · rw [hdiff, numLate_eq p d ag l hl]
  · rw [hdiff, numLate_eq p d ag l hl]

lemma idx_lt_of_lt (L : List (Fin n)) (hL : L.Pairwise (· < ·)) (x y : Fin n) (hx : x ∈ L)
    (hy : y ∈ L) (hxy : x < y) : L.idxOf x < L.idxOf y := by
  rw [List.pairwise_iff_getElem] at hL
  by_contra hcon
  have hle := not_lt.1 hcon
  have hx' := List.idxOf_lt_length_iff.2 hx
  have hy' := List.idxOf_lt_length_iff.2 hy
  rcases Nat.lt_or_eq_of_le hle with h | h
  · have := hL _ _ hy' hx' h
    rw [List.getElem_idxOf, List.getElem_idxOf] at this
    exact absurd (lt_trans hxy this) (lt_irrefl _)
  · have := (List.idxOf_inj hx).1 h.symm
    exact absurd this (ne_of_lt hxy)

lemma sched_of_ps {h k : ℕ} {E : Finset (Fin n)} (hE : IsPartialSchedule p d ag n h k E) :
    ∃ l : List (Fin n), IsSchedule Finset.univ l ∧ numLate p d ag .A l ≤ h ∧
      numLate p d ag .B l ≤ k := by
  classical
  obtain ⟨_, hEF, hA, hB⟩ := hE
  set l₁ := (List.finRange n).filter (fun j => decide (j ∈ E)) with hl₁
  set l₂ := (List.finRange n).filter (fun j => decide (j ∉ E)) with hl₂
  have hm₁ : ∀ j, j ∈ l₁ ↔ j ∈ E := by intro j; simp [hl₁]
  have hm₂ : ∀ j, j ∈ l₂ ↔ j ∉ E := by intro j; simp [hl₂]
  have hpw : l₁.Pairwise (· < ·) := (List.pairwise_lt_finRange n).filter _
  have hnd₁ : l₁.Nodup := hpw.imp ne_of_lt
  have hnd₂ : l₂.Nodup := ((List.pairwise_lt_finRange n).filter _).imp ne_of_lt
  have hsched : IsSchedule Finset.univ (l₁ ++ l₂) := by
    refine ⟨List.nodup_append.2 ⟨hnd₁, hnd₂, ?_⟩, ?_⟩
    · intro a ha b hb hab
      subst hab
      exact (hm₂ a).1 hb ((hm₁ a).1 ha)
    · intro x
      simp only [List.mem_append, Finset.mem_univ, iff_true]
      by_cases hx : x ∈ E
      · exact Or.inl ((hm₁ x).2 hx)
      · exact Or.inr ((hm₂ x).2 hx)
  have KL : ∀ j ∈ E, ∀ y, (l₁ ++ l₂).idxOf y ≤ (l₁ ++ l₂).idxOf j → y ∈ E ∧ y ≤ j := by
    intro j hj y hy
    have hj1 : j ∈ l₁ := (hm₁ j).2 hj
    have e1 : (l₁ ++ l₂).idxOf j = l₁.idxOf j := List.idxOf_append_of_mem hj1
    by_cases hy1 : y ∈ l₁
    · rw [List.idxOf_append_of_mem hy1, e1] at hy
      refine ⟨(hm₁ y).1 hy1, ?_⟩
      by_contra hcon
      have hlt : j < y := not_le.1 hcon
      have := idx_lt_of_lt l₁ hpw j y hj1 hy1 hlt
      omega
    · exfalso
      rw [List.idxOf_append_of_notMem hy1, e1] at hy
      have := List.idxOf_lt_length_iff.2 hj1
      omega
  have hnl : ∀ j ∈ E, ¬ (d j < cN p (l₁ ++ l₂) j) := by
    intro j hj
    rw [not_lt]
    calc cN p (l₁ ++ l₂) j ≤ ∑ y ∈ E.filter (fun i => i ≤ j), p y := by
          unfold cN
          refine Finset.sum_le_sum_of_subset (fun y hy => ?_)
          have := KL j hj y (Finset.mem_filter.1 hy).2
          exact Finset.mem_filter.2 this
      _ ≤ d j := hEF j hj
  have hsub : ∀ X : Agent, ((Finset.univ.filter (fun j => d j < cN p (l₁ ++ l₂) j)).filter
      (fun j => ag j = X)).card ≤ ((prefixJobs n n \ E).filter (fun j => ag j = X)).card := by
    intro X
    refine Finset.card_le_card (Finset.filter_subset_filter _ (fun j hj => ?_))
    rw [Finset.mem_filter] at hj
    rw [Finset.mem_sdiff, prefix_n]
    exact ⟨Finset.mem_univ _, fun hjE => hnl j hjE hj.2⟩
  refine ⟨l₁ ++ l₂, hsched, ?_, ?_⟩
  · rw [numLate_eq p d ag _ hsched]; exact (hsub .A).trans hA
  · rw [numLate_eq p d ag _ hsched]; exact (hsub .B).trans hB

end lib2

open LL in
theorem solution {n : ℕ} (p d : Fin n → ℕ) (ag : Fin n → Agent) (Q : ℕ) (hd : Monotone d)
    (hfeas : ∃ l : List (Fin n), IsFeasible p d ag Q l) :
    ∃ hex : ∃ h : ℕ, C p d ag n h Q < ⊤,
      (∃ l : List (Fin n), IsFeasible p d ag Q l ∧ numLate p d ag .A l = Nat.find hex) ∧
      ∀ l : List (Fin n), IsFeasible p d ag Q l → Nat.find hex ≤ numLate p d ag .A l := by
  -- key: a feasible sequence gives a finite table entry
  have key : ∀ l : List (Fin n), IsFeasible p d ag Q l →
      C p d ag n (numLate p d ag .A l) Q < ⊤ := by
    intro l hl
    obtain ⟨hs, hB⟩ := hl
    have hps := ps_of_sched p d ag hd l hs
    have hps' : IsPartialSchedule p d ag n (numLate p d ag .A l) Q
        (Finset.univ.filter (fun j => cN p l j ≤ d j)) := by
      obtain ⟨h1, h2, h3, h4⟩ := hps
      exact ⟨h1, h2, h3, h4.trans hB⟩
    obtain ⟨hle, _⟩ := C_spec p d ag n le_rfl (numLate p d ag .A l) Q
    exact lt_of_le_of_lt (hle _ hps') (WithTop.coe_lt_top _)
  obtain ⟨l0, hl0⟩ := hfeas
  have hex : ∃ h : ℕ, C p d ag n h Q < ⊤ := ⟨_, key l0 hl0⟩
  refine ⟨hex, ?_, ?_⟩
  · have hfind : C p d ag n (Nat.find hex) Q < ⊤ := Nat.find_spec hex
    obtain ⟨hle, hatt⟩ := C_spec p d ag n le_rfl (Nat.find hex) Q
    rcases hatt with h0 | ⟨E, hE, _⟩
    · rw [h0] at hfind; exact absurd hfind (lt_irrefl _)
    · obtain ⟨l, hl, hA, hB⟩ := sched_of_ps p d ag hE
      refine ⟨l, ⟨hl, hB⟩, le_antisymm hA ?_⟩
      exact Nat.find_min' hex (key l ⟨hl, hB⟩)
  · intro l hl
    exact Nat.find_min' hex (key l hl)
