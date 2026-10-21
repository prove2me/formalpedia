-- Prove2me | solution 1 for TwoAgentSched.LateLate.lemma_7_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:32:53.450145+00:00
-- url     : https://prove2.me/submissions/202a82b7-c202-4096-9bfb-4211f7a1b673

import Mathlib
import Definitions.Def_TwoAgentSched_LateLate_DPTable

set_option autoImplicit false
open TwoAgentSched.LateLate

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

open LL in
theorem solution {n : ℕ} (p d : Fin n → ℕ) (ag : Fin n → Agent) (hd : Monotone d)
    (i h k : ℕ) (hi : i ≤ n) :
    (∀ c : ℕ, C p d ag i h k = (c : WithTop ℕ) →
      (∃ E : Finset (Fin n), IsPartialSchedule p d ag i h k E ∧ ∑ j ∈ E, p j = c) ∧
      ∀ E : Finset (Fin n), IsPartialSchedule p d ag i h k E → c ≤ ∑ j ∈ E, p j) ∧
    (C p d ag i h k = ⊤ → ∀ E : Finset (Fin n), ¬ IsPartialSchedule p d ag i h k E) := by
  obtain ⟨hle, hatt⟩ := C_spec p d ag i hi h k
  refine ⟨fun c hc => ⟨?_, fun E hE => ?_⟩, fun htop E hE => ?_⟩
  · rcases hatt with h0 | ⟨E, hE, he⟩
    · rw [h0] at hc; exact absurd hc (by simp)
    · refine ⟨E, hE, ?_⟩
      rw [hc] at he; exact_mod_cast he.symm
  · have := hle E hE
    rw [hc] at this; exact_mod_cast this
  · have := hle E hE
    rw [htop] at this
    exact absurd this (by simp)
