-- Prove2me | solution 1 for TwoAgentSched.LateLate.lemma_7_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:39:12.507747+00:00
-- url     : https://prove2.me/submissions/3c68f596-0f79-49ec-a40f-83b19a44e7ce

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

section lib3
variable {n : ℕ} (p d : Fin n → ℕ) (ag : Fin n → Agent)

lemma early_pos (l0 : List (Fin n)) (sE rest : List (Fin n)) (hsE : sE.Nodup)
    (hmem : ∀ y ∈ sE, cN p l0 y ≤ d y) (hpw : sE.Pairwise (fun a b => d a ≤ d b)) (k : ℕ)
    (hk : k < sE.length) :
    completionAt (fun j => (p j : ℝ)) (sE ++ rest) k ≤ (d sE[k] : ℝ) := by
  unfold completionAt
  rw [List.take_append_of_le_length (by omega)]
  have hnd : (sE.take (k + 1)).Nodup := hsE.sublist (List.take_sublist _ _)
  rw [← List.sum_toFinset _ hnd]
  have hklen : (sE.take (k + 1)).length = k + 1 := by simp; omega
  have hkmem : sE[k] ∈ sE.take (k + 1) := by
    rw [List.mem_iff_getElem]
    exact ⟨k, by omega, by simp⟩
  have := jackson p d l0 (sE.take (k + 1)).toFinset ⟨sE[k], List.mem_toFinset.2 hkmem⟩ (d sE[k])
    (fun y hy => hmem y (List.mem_of_mem_take (List.mem_toFinset.1 hy)))
    (by
      intro y hy
      have hy' := List.mem_toFinset.1 hy
      rw [List.mem_iff_getElem] at hy'
      obtain ⟨i, hi, rfl⟩ := hy'
      rw [List.getElem_take]
      have hik : i ≤ k := by omega
      rcases Nat.lt_or_eq_of_le hik with h | h
      · exact List.pairwise_iff_getElem.1 hpw i k (by omega) hk h
      · subst h; exact le_refl _)
  exact_mod_cast this

end lib3

open LL in
theorem solution {n : ℕ} (p d : Fin n → ℕ) (ag : Fin n → Agent) (Q : ℕ)
    (hfeas : ∃ l : List (Fin n), IsFeasible p d ag Q l) :
    ∃ l : List (Fin n), IsOptimal p d ag Q l ∧
      ∃ m ≤ l.length,
        (∀ (k : ℕ) (hk : k < l.length),
          (k < m ↔ MooreLateJobs.Shared.completionAt (fun j => (p j : ℝ)) l k ≤ (d l[k] : ℝ))) ∧
        (l.take m).Pairwise (fun a b => d a ≤ d b) := by
  classical
  -- an optimal schedule with the fewest late jobs
  have hex1 : ∃ h : ℕ, ∃ l, IsFeasible p d ag Q l ∧ numLate p d ag .A l = h := by
    obtain ⟨l, hl⟩ := hfeas; exact ⟨_, l, hl, rfl⟩
  obtain ⟨l1, hl1, hl1A⟩ := Nat.find_spec hex1
  have hopt1 : IsOptimal p d ag Q l1 := by
    refine ⟨hl1, fun l' hl' => ?_⟩
    rw [hl1A]; exact Nat.find_min' hex1 ⟨l', hl', rfl⟩
  have hex2 : ∃ c : ℕ, ∃ l, IsOptimal p d ag Q l ∧
      (MooreLateJobs.NumLate.lateSet (fun j => (p j : ℝ)) (fun j => (d j : ℝ)) l).card = c :=
    ⟨_, l1, hopt1, rfl⟩
  obtain ⟨l0, hopt0, hc0⟩ := Nat.find_spec hex2
  have hmin : ∀ l, IsOptimal p d ag Q l →
      Nat.find hex2 ≤ (MooreLateJobs.NumLate.lateSet (fun j => (p j : ℝ)) (fun j => (d j : ℝ)) l).card :=
    fun l hl => Nat.find_min' hex2 ⟨l, hl, rfl⟩
  have hs0 : IsSchedule Finset.univ l0 := hopt0.1.1
  set E : Finset (Fin n) := Finset.univ.filter (fun j => cN p l0 j ≤ d j) with hE
  set R : Finset (Fin n) := Finset.univ.filter (fun j => d j < cN p l0 j) with hR
  have hRlate : MooreLateJobs.NumLate.lateSet (fun j => (p j : ℝ)) (fun j => (d j : ℝ)) l0 = R :=
    lateSet_eq p d l0 hs0
  set le : Fin n → Fin n → Bool := fun a b => decide (d a ≤ d b) with hle
  set sE : List (Fin n) := E.toList.mergeSort le with hsE
  set sR : List (Fin n) := R.toList with hsR
  have hpermE : sE.Perm E.toList := List.mergeSort_perm _ _
  have hndE : sE.Nodup := hpermE.nodup_iff.2 (Finset.nodup_toList E)
  have hmE : ∀ y, y ∈ sE ↔ y ∈ E := fun y => by rw [hpermE.mem_iff, Finset.mem_toList]
  have hmR : ∀ y, y ∈ sR ↔ y ∈ R := fun y => by rw [hsR, Finset.mem_toList]
  have hndR : sR.Nodup := Finset.nodup_toList R
  have hpw : sE.Pairwise (fun a b => d a ≤ d b) := by
    have := List.pairwise_mergeSort (le := le) (l := E.toList)
      (by intro a b c h1 h2; simp only [hle, decide_eq_true_eq] at h1 h2 ⊢; exact h1.trans h2)
      (by intro a b; simp only [hle, Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _)
    exact this.imp (by intro a b h; simpa [hle] using h)
  have hEmem : ∀ y ∈ sE, cN p l0 y ≤ d y := fun y hy => (Finset.mem_filter.1 ((hmE y).1 hy)).2
  have hsched : IsSchedule Finset.univ (sE ++ sR) := by
    refine ⟨List.nodup_append.2 ⟨hndE, hndR, ?_⟩, ?_⟩
    · intro a ha b hb hab
      subst hab
      have h1 := Finset.mem_filter.1 ((hmE a).1 ha)
      have h2 := Finset.mem_filter.1 ((hmR a).1 hb)
      exact absurd h1.2 (not_le.2 h2.2)
    · intro x
      simp only [List.mem_append, Finset.mem_univ, iff_true]
      by_cases hx : cN p l0 x ≤ d x
      · exact Or.inl ((hmE x).2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩))
      · exact Or.inr ((hmR x).2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, not_le.1 hx⟩))
  set l := sE ++ sR with hl
  have hearly : ∀ (k : ℕ) (hk : k < sE.length),
      completionAt (fun j => (p j : ℝ)) l k ≤ (d sE[k] : ℝ) :=
    fun k hk => early_pos p d l0 sE sR hndE hEmem hpw k hk
  -- late set of l is contained in R
  have hsub : MooreLateJobs.NumLate.lateSet (fun j => (p j : ℝ)) (fun j => (d j : ℝ)) l ⊆ R := by
    intro j hj
    unfold MooreLateJobs.NumLate.lateSet at hj
    rw [Finset.mem_filter] at hj
    by_contra hjR
    have hjE : j ∈ E := by
      have : cN p l0 j ≤ d j := by
        by_contra hcon
        exact hjR (Finset.mem_filter.2 ⟨Finset.mem_univ _, not_le.1 hcon⟩)
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, this⟩
    have hjs : j ∈ sE := (hmE j).2 hjE
    have hidx : l.idxOf j = sE.idxOf j := List.idxOf_append_of_mem hjs
    have hlt : sE.idxOf j < sE.length := List.idxOf_lt_length_iff.2 hjs
    have h1 := hearly (sE.idxOf j) hlt
    rw [List.getElem_idxOf] at h1
    have h2 : completionTime (fun j => (p j : ℝ)) l j ≤ (d j : ℝ) := by
      unfold completionTime
      rw [hidx]; exact h1
    exact absurd hj.2 (not_lt.2 h2)
  have hfeas_l : IsFeasible p d ag Q l := by
    refine ⟨hsched, ?_⟩
    have : numLate p d ag .B l ≤ numLate p d ag .B l0 := by
      unfold numLate
      rw [hRlate]
      exact Finset.card_le_card (Finset.filter_subset_filter _ hsub)
    exact this.trans hopt0.1.2
  have hopt_l : IsOptimal p d ag Q l := by
    refine ⟨hfeas_l, fun l' hl' => ?_⟩
    have : numLate p d ag .A l ≤ numLate p d ag .A l0 := by
      unfold numLate
      rw [hRlate]
      exact Finset.card_le_card (Finset.filter_subset_filter _ hsub)
    exact this.trans (hopt0.2 l' hl')
  have hceq : MooreLateJobs.NumLate.lateSet (fun j => (p j : ℝ)) (fun j => (d j : ℝ)) l = R := by
    apply Finset.eq_of_subset_of_card_le hsub
    calc R.card = (MooreLateJobs.NumLate.lateSet (fun j => (p j : ℝ)) (fun j => (d j : ℝ)) l0).card := by
          rw [hRlate]
      _ = Nat.find hex2 := hc0
      _ ≤ _ := hmin l hopt_l
  refine ⟨l, hopt_l, sE.length, by simp [hl], ?_, ?_⟩
  · intro k hk
    by_cases hkm : k < sE.length
    · refine ⟨fun _ => ?_, fun _ => hkm⟩
      have := hearly k hkm
      have e : l[k] = sE[k] := by
        simp only [hl]; exact List.getElem_append_left hkm
      rw [e]; exact this
    · refine ⟨fun h => absurd h hkm, fun hearly' => ?_⟩
      exfalso
      have hkR : l[k] ∈ R := by
        have hk2 : k - sE.length < sR.length := by simp [hl] at hk; omega
        have e : l[k] = sR[k - sE.length] := by
          simp only [hl]; exact List.getElem_append_right (by omega)
        rw [e]; exact (hmR _).1 (List.getElem_mem _)
      rw [← hceq] at hkR
      unfold MooreLateJobs.NumLate.lateSet at hkR
      rw [Finset.mem_filter] at hkR
      have hnd : l.Nodup := hsched.1
      have : l.idxOf l[k] = k := hnd.idxOf_getElem k hk
      have h3 := hkR.2
      unfold completionTime at h3
      rw [this] at h3
      exact absurd hearly' (not_le.2 h3)
  · have : l.take sE.length = sE := by
      simp only [hl]; exact List.take_left
    rw [this]; exact hpw
