-- Prove2me | solution 1 for TwoAgentSched.TotalTotal.spt_normalization
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T19:30:21.288516+00:00
-- url     : https://prove2.me/submissions/99c1bb73-7077-4db8-973e-34e5787d603c

import Definitions.Def_TwoAgentSched_TotalTotal_DP

open MooreLateJobs.Shared

namespace TwoAgentSched.TotalTotal.PrefixProof

/- The following completion-time facts are adapted from the previously checked
   `Sol_TwoAgentSched_ParetoTotal_theorem_11_6.lean`, generic section. -/

lemma completionAt_append_left {ι : Type*} (p : ι → ℝ) (l₁ l₂ : List ι) (m : ℕ)
    (hm : m < l₁.length) :
    completionAt p (l₁ ++ l₂) m = completionAt p l₁ m := by
  unfold completionAt
  rw [List.take_append_of_le_length (by omega)]

lemma completionTime_append_mem {ι : Type*} [DecidableEq ι] (p : ι → ℝ)
    (l₁ l₂ : List ι) (x : ι) (hx : x ∈ l₁) :
    completionTime p (l₁ ++ l₂) x = completionTime p l₁ x := by
  unfold completionTime
  rw [List.idxOf_append_of_mem hx]
  exact completionAt_append_left p l₁ l₂ _ (List.idxOf_lt_length_iff.mpr hx)

lemma completionTime_append_last {ι : Type*} [DecidableEq ι] (p : ι → ℝ)
    (l : List ι) (z : ι) (hz : z ∉ l) :
    completionTime p (l ++ [z]) z = ((l ++ [z]).map p).sum := by
  unfold completionTime completionAt
  have hidx : (l ++ [z]).idxOf z = l.length := by
    rw [List.idxOf_append_of_notMem hz]
    simp
  rw [hidx]
  rw [List.take_of_length_le (by simp)]

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

/-- Completion sum of exactly the first `i` A-jobs in the supplied sequence. -/
noncomputable def prefixSumCA (I : Instance) (i : ℕ)
    (l : List (Fin I.nA ⊕ Fin I.nB)) : ℝ :=
  ∑ h : Fin I.nA, if h.val < i then I.C l (Sum.inl h) else 0

/-- Completion sum of exactly the first `j` B-jobs in the supplied sequence. -/
noncomputable def prefixSumCB (I : Instance) (j : ℕ)
    (l : List (Fin I.nA ⊕ Fin I.nB)) : ℝ :=
  ∑ k : Fin I.nB, if k.val < j then I.C l (Sum.inr k) else 0

lemma prefixSumCA_append (I : Instance) (i : ℕ) (l₁ l₂ : List (Fin I.nA ⊕ Fin I.nB))
    (hmem : ∀ h : Fin I.nA, h.val < i → Sum.inl h ∈ l₁) :
    prefixSumCA I i (l₁ ++ l₂) = prefixSumCA I i l₁ := by
  unfold prefixSumCA
  apply Finset.sum_congr rfl
  intro h _
  by_cases hh : h.val < i
  · simp only [hh, if_true, Instance.C]
    exact completionTime_append_mem I.p l₁ l₂ (Sum.inl h) (hmem h hh)
  · simp [hh]

lemma prefixSumCB_append (I : Instance) (j : ℕ) (l₁ l₂ : List (Fin I.nA ⊕ Fin I.nB))
    (hmem : ∀ k : Fin I.nB, k.val < j → Sum.inr k ∈ l₁) :
    prefixSumCB I j (l₁ ++ l₂) = prefixSumCB I j l₁ := by
  unfold prefixSumCB
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k.val < j
  · simp only [hk, if_true, Instance.C]
    exact completionTime_append_mem I.p l₁ l₂ (Sum.inr k) (hmem k hk)
  · simp [hk]

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

lemma prefixSumCA_succ (I : Instance) (i : ℕ) (hi : i < I.nA)
    (l : List (Fin I.nA ⊕ Fin I.nB)) :
    prefixSumCA I (i + 1) l = prefixSumCA I i l + I.C l (Sum.inl (⟨i, hi⟩ : Fin I.nA)) := by
  classical
  unfold prefixSumCA
  calc
    (∑ h : Fin I.nA, if h.val < i + 1 then I.C l (Sum.inl h) else 0) =
        ∑ h : Fin I.nA, ((if h.val < i then I.C l (Sum.inl h) else 0) +
          if h = ⟨i, hi⟩ then I.C l (Sum.inl h) else 0) := by
      apply Finset.sum_congr rfl
      intro h _
      by_cases hlt : h.val < i
      · have hne : h ≠ ⟨i, hi⟩ := by
          intro heq
          have hv : h.val = i := congrArg Fin.val heq
          omega
        simp [hlt, show h.val < i + 1 by omega, hne]
      · by_cases heq : h = ⟨i, hi⟩
        · subst h
          simp
        · have hnot : ¬ h.val < i + 1 := by
            intro hle
            have hv : h.val = i := by omega
            exact heq (Fin.ext hv)
          simp [hlt, heq, hnot]
    _ = (∑ h : Fin I.nA, if h.val < i then I.C l (Sum.inl h) else 0) +
        I.C l (Sum.inl (⟨i, hi⟩ : Fin I.nA)) := by
      simp [Finset.sum_add_distrib]

lemma prefixSumCA_append_next (I : Instance) (i : ℕ) (hi : i < I.nA)
    (l : List (Fin I.nA ⊕ Fin I.nB))
    (hprev : ∀ h : Fin I.nA, h.val < i → Sum.inl h ∈ l)
    (hnew : Sum.inl (⟨i, hi⟩ : Fin I.nA) ∉ l) :
    prefixSumCA I (i + 1) (l ++ [Sum.inl (⟨i, hi⟩ : Fin I.nA)]) =
      prefixSumCA I i l + ((l ++ [Sum.inl (⟨i, hi⟩ : Fin I.nA)]).map I.p).sum := by
  rw [prefixSumCA_succ I i hi]
  rw [prefixSumCA_append I i l [Sum.inl (⟨i, hi⟩ : Fin I.nA)] hprev]
  unfold Instance.C
  rw [completionTime_append_last I.p l (Sum.inl (⟨i, hi⟩ : Fin I.nA)) hnew]

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

lemma prefixSumCB_succ (I : Instance) (i : ℕ) (hi : i < I.nB)
    (l : List (Fin I.nA ⊕ Fin I.nB)) :
    prefixSumCB I (i + 1) l = prefixSumCB I i l + I.C l (Sum.inr (⟨i, hi⟩ : Fin I.nB)) := by
  classical
  unfold prefixSumCB
  calc
    (∑ h : Fin I.nB, if h.val < i + 1 then I.C l (Sum.inr h) else 0) =
        ∑ h : Fin I.nB, ((if h.val < i then I.C l (Sum.inr h) else 0) +
          if h = ⟨i, hi⟩ then I.C l (Sum.inr h) else 0) := by
      apply Finset.sum_congr rfl
      intro h _
      by_cases hlt : h.val < i
      · have hne : h ≠ ⟨i, hi⟩ := by
          intro heq
          have hv : h.val = i := congrArg Fin.val heq
          omega
        simp [hlt, show h.val < i + 1 by omega, hne]
      · by_cases heq : h = ⟨i, hi⟩
        · subst h
          simp
        · have hnot : ¬ h.val < i + 1 := by
            intro hle
            have hv : h.val = i := by omega
            exact heq (Fin.ext hv)
          simp [hlt, heq, hnot]
    _ = (∑ h : Fin I.nB, if h.val < i then I.C l (Sum.inr h) else 0) +
        I.C l (Sum.inr (⟨i, hi⟩ : Fin I.nB)) := by
      simp [Finset.sum_add_distrib]

lemma prefixSumCB_append_next (I : Instance) (i : ℕ) (hi : i < I.nB)
    (l : List (Fin I.nA ⊕ Fin I.nB))
    (hprev : ∀ h : Fin I.nB, h.val < i → Sum.inr h ∈ l)
    (hnew : Sum.inr (⟨i, hi⟩ : Fin I.nB) ∉ l) :
    prefixSumCB I (i + 1) (l ++ [Sum.inr (⟨i, hi⟩ : Fin I.nB)]) =
      prefixSumCB I i l + ((l ++ [Sum.inr (⟨i, hi⟩ : Fin I.nB)]).map I.p).sum := by
  rw [prefixSumCB_succ I i hi]
  rw [prefixSumCB_append I i l [Sum.inr (⟨i, hi⟩ : Fin I.nB)] hprev]
  unfold Instance.C
  rw [completionTime_append_last I.p l (Sum.inr (⟨i, hi⟩ : Fin I.nB)) hnew]

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

/-- The job set for the first `i` A-jobs and first `j` B-jobs. -/
noncomputable def prefixJobs (I : Instance) (i j : ℕ) : Finset (Fin I.nA ⊕ Fin I.nB) := by
  classical
  exact Finset.univ.filter fun x => match x with
    | Sum.inl h => h.val < i
    | Sum.inr k => k.val < j

/-- Total processing time of a duplicate-free enumeration of the prefix jobs. -/
lemma prefixJobs_total (I : Instance) (i j : ℕ) (l : List (Fin I.nA ⊕ Fin I.nB))
    (hnd : l.Nodup) (hmem : ∀ x, x ∈ l ↔ x ∈ prefixJobs I i j) :
    (l.map I.p).sum = (I.bigPij i j : ℝ) := by
  classical
  have hset : l.toFinset = prefixJobs I i j := by
    ext x
    simpa only [List.mem_toFinset] using hmem x
  rw [← List.sum_toFinset I.p hnd, hset]
  simp [prefixJobs, Finset.sum_filter, Fintype.sum_sum_type, Instance.p, Instance.bigPij]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro x _ <;> split_ifs <;> rfl

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

/-- Appending the next A-job adds exactly `P(i+1,j)` to the A-prefix objective. -/
lemma prefixSumCA_append_next_bigP (I : Instance) (i j : ℕ) (hi : i < I.nA)
    (l : List (Fin I.nA ⊕ Fin I.nB))
    (hprev : ∀ h : Fin I.nA, h.val < i → Sum.inl h ∈ l)
    (hnew : Sum.inl (⟨i, hi⟩ : Fin I.nA) ∉ l)
    (hnd : (l ++ [Sum.inl (⟨i, hi⟩ : Fin I.nA)]).Nodup)
    (hmem : ∀ x, x ∈ l ++ [Sum.inl (⟨i, hi⟩ : Fin I.nA)] ↔
      x ∈ prefixJobs I (i + 1) j) :
    prefixSumCA I (i + 1) (l ++ [Sum.inl (⟨i, hi⟩ : Fin I.nA)]) =
      prefixSumCA I i l + (I.bigPij (i + 1) j : ℝ) := by
  rw [prefixSumCA_append_next I i hi l hprev hnew]
  rw [prefixJobs_total I (i + 1) j _ hnd hmem]

/-- Appending the next B-job adds exactly `P(i,j+1)` to the B-prefix objective. -/
lemma prefixSumCB_append_next_bigP (I : Instance) (i j : ℕ) (hj : j < I.nB)
    (l : List (Fin I.nA ⊕ Fin I.nB))
    (hprev : ∀ k : Fin I.nB, k.val < j → Sum.inr k ∈ l)
    (hnew : Sum.inr (⟨j, hj⟩ : Fin I.nB) ∉ l)
    (hnd : (l ++ [Sum.inr (⟨j, hj⟩ : Fin I.nB)]).Nodup)
    (hmem : ∀ x, x ∈ l ++ [Sum.inr (⟨j, hj⟩ : Fin I.nB)] ↔
      x ∈ prefixJobs I i (j + 1)) :
    prefixSumCB I (j + 1) (l ++ [Sum.inr (⟨j, hj⟩ : Fin I.nB)]) =
      prefixSumCB I j l + (I.bigPij i (j + 1) : ℝ) := by
  rw [prefixSumCB_append_next I j hj l hprev hnew]
  rw [prefixJobs_total I i (j + 1) _ hnd hmem]

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

lemma sum_fin_prefix_succ {n : ℕ} (f : Fin n → ℕ) (i : ℕ) (hi : i < n) :
    (∑ h : Fin n, if h.val < i + 1 then f h else 0) =
      (∑ h : Fin n, if h.val < i then f h else 0) + f ⟨i, hi⟩ := by
  classical
  calc
    (∑ h : Fin n, if h.val < i + 1 then f h else 0) =
        ∑ h : Fin n, ((if h.val < i then f h else 0) +
          if h = ⟨i, hi⟩ then f h else 0) := by
      apply Finset.sum_congr rfl
      intro h _
      by_cases hlt : h.val < i
      · have hne : h ≠ ⟨i, hi⟩ := by
          intro heq
          have hv : h.val = i := congrArg Fin.val heq
          omega
        simp [hlt, show h.val < i + 1 by omega, hne]
      · by_cases heq : h = ⟨i, hi⟩
        · subst h
          simp
        · have hnot : ¬ h.val < i + 1 := by
            intro hle
            have hv : h.val = i := by omega
            exact heq (Fin.ext hv)
          simp [hlt, heq, hnot]
    _ = (∑ h : Fin n, if h.val < i then f h else 0) + f ⟨i, hi⟩ := by
      simp [Finset.sum_add_distrib]

/-- The source's A-last cost equals the total processing time of the extended prefix. -/
lemma bigPij_A_succ (I : Instance) (i j : ℕ) (hi : i < I.nA) :
    I.bigPij i j + I.pAt (i + 1) = I.bigPij (i + 1) j := by
  have hsum := sum_fin_prefix_succ I.pA i hi
  unfold Instance.bigPij Instance.pAt
  have hbound : 1 ≤ i + 1 ∧ i + 1 ≤ I.nA := by omega
  simp only [hbound, true_and, ↓reduceDIte, Nat.add_sub_cancel_right]
  omega

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

lemma prefixJobs_A_succ (I : Instance) (i j : ℕ) (hi : i < I.nA) :
    prefixJobs I (i + 1) j = insert (Sum.inl (⟨i, hi⟩ : Fin I.nA)) (prefixJobs I i j) := by
  classical
  ext x
  cases x with
  | inl a =>
    simp only [prefixJobs, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Sum.inl.injEq, Fin.ext_iff]
    omega
  | inr b => simp [prefixJobs]

lemma prefixJobs_B_succ (I : Instance) (i j : ℕ) (hj : j < I.nB) :
    prefixJobs I i (j + 1) = insert (Sum.inr (⟨j, hj⟩ : Fin I.nB)) (prefixJobs I i j) := by
  classical
  ext x
  cases x with
  | inl a => simp [prefixJobs]
  | inr b =>
    simp only [prefixJobs, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Sum.inr.injEq, Fin.ext_iff]
    omega

lemma prefixJobs_A_append (I : Instance) (i j : ℕ) (hi : i < I.nA)
    (l : List (Fin I.nA ⊕ Fin I.nB))
    (hl : ∀ x, x ∈ l ↔ x ∈ prefixJobs I i j) :
    ∀ x, x ∈ l ++ [Sum.inl (⟨i, hi⟩ : Fin I.nA)] ↔ x ∈ prefixJobs I (i + 1) j := by
  intro x
  rw [prefixJobs_A_succ I i j hi]
  simp only [List.mem_append, List.mem_singleton, Finset.mem_insert, hl]
  tauto

lemma prefixJobs_B_append (I : Instance) (i j : ℕ) (hj : j < I.nB)
    (l : List (Fin I.nA ⊕ Fin I.nB))
    (hl : ∀ x, x ∈ l ↔ x ∈ prefixJobs I i j) :
    ∀ x, x ∈ l ++ [Sum.inr (⟨j, hj⟩ : Fin I.nB)] ↔ x ∈ prefixJobs I i (j + 1) := by
  intro x
  rw [prefixJobs_B_succ I i j hj]
  simp only [List.mem_append, List.mem_singleton, Finset.mem_insert, hl]
  tauto

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

/-- Each agent's jobs appear in increasing index order; cross-agent order is free. -/
def prefixOrder {nA nB : ℕ} (x y : Fin nA ⊕ Fin nB) : Prop :=
  match x, y with
  | Sum.inl a, Sum.inl b => a.val < b.val
  | Sum.inr a, Sum.inr b => a.val < b.val
  | _, _ => True

/-- A sorted A-ending interleaving must end in the largest A-prefix job. -/
lemma last_A_eq_prefix (I : Instance) (i j : ℕ) (hi : i < I.nA)
    (l : List (Fin I.nA ⊕ Fin I.nB)) (a : Fin I.nA)
    (hpair : (l ++ [Sum.inl a]).Pairwise prefixOrder)
    (hmem : ∀ x, x ∈ l ++ [Sum.inl a] ↔ x ∈ prefixJobs I (i + 1) j) :
    a = ⟨i, hi⟩ := by
  classical
  by_contra hne
  have hk : Sum.inl (⟨i, hi⟩ : Fin I.nA) ∈ l ++ [Sum.inl a] :=
    (hmem _).mpr (by simp [prefixJobs])
  have hkl : Sum.inl (⟨i, hi⟩ : Fin I.nA) ∈ l := by
    rcases List.mem_append.mp hk with hk | hk
    · exact hk
    · simp only [List.mem_singleton, Sum.inl.injEq] at hk
      exact False.elim (hne hk.symm)
  have hrel := (List.pairwise_append.mp hpair).2.2 _ hkl (Sum.inl a) (by simp)
  have hlt : i < a.val := hrel
  have ha : Sum.inl a ∈ prefixJobs I (i + 1) j := (hmem _).mp (by simp)
  have habound : a.val < i + 1 := by simpa [prefixJobs] using ha
  omega

/-- A sorted B-ending interleaving must end in the largest B-prefix job. -/
lemma last_B_eq_prefix (I : Instance) (i j : ℕ) (hj : j < I.nB)
    (l : List (Fin I.nA ⊕ Fin I.nB)) (b : Fin I.nB)
    (hpair : (l ++ [Sum.inr b]).Pairwise prefixOrder)
    (hmem : ∀ x, x ∈ l ++ [Sum.inr b] ↔ x ∈ prefixJobs I i (j + 1)) :
    b = ⟨j, hj⟩ := by
  classical
  by_contra hne
  have hk : Sum.inr (⟨j, hj⟩ : Fin I.nB) ∈ l ++ [Sum.inr b] :=
    (hmem _).mpr (by simp [prefixJobs])
  have hkl : Sum.inr (⟨j, hj⟩ : Fin I.nB) ∈ l := by
    rcases List.mem_append.mp hk with hk | hk
    · exact hk
    · simp only [List.mem_singleton, Sum.inr.injEq] at hk
      exact False.elim (hne hk.symm)
  have hrel := (List.pairwise_append.mp hpair).2.2 _ hkl (Sum.inr b) (by simp)
  have hlt : j < b.val := hrel
  have hb : Sum.inr b ∈ prefixJobs I i (j + 1) := (hmem _).mp (by simp)
  have hbbound : b.val < j + 1 := by simpa [prefixJobs] using hb
  omega

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

/-- A sequence of exactly the two prefixes, in each agent's index order. -/
def IsPrefixSequence (I : Instance) (i j : ℕ) (l : List (Fin I.nA ⊕ Fin I.nB)) : Prop :=
  l.Nodup ∧ (∀ x, x ∈ l ↔ x ∈ prefixJobs I i j) ∧ l.Pairwise prefixOrder

lemma prefixSequence_append_A (I : Instance) (i j : ℕ) (hi : i < I.nA)
    (l : List (Fin I.nA ⊕ Fin I.nB)) (h : IsPrefixSequence I i j l) :
    IsPrefixSequence I (i + 1) j (l ++ [Sum.inl (⟨i, hi⟩ : Fin I.nA)]) := by
  classical
  obtain ⟨hnd, hmem, hpair⟩ := h
  have hnew : Sum.inl (⟨i, hi⟩ : Fin I.nA) ∉ l := by
    intro hx
    have hx' := (hmem _).mp hx
    simp [prefixJobs] at hx'
  refine ⟨?_, prefixJobs_A_append I i j hi l hmem, ?_⟩
  · apply List.nodup_append.mpr
    refine ⟨hnd, by simp, ?_⟩
    intro x hx y hy
    have hy' : y = Sum.inl (⟨i, hi⟩ : Fin I.nA) := by simpa using hy
    subst y
    intro heq
    apply hnew
    simpa [heq] using hx
  · apply List.pairwise_append.mpr
    refine ⟨hpair, by simp, ?_⟩
    intro x hx y hy
    have hy' : y = Sum.inl (⟨i, hi⟩ : Fin I.nA) := by simpa using hy
    subst y
    cases x with
    | inl a =>
      have ha := (hmem _).mp hx
      simpa [prefixJobs, prefixOrder] using ha
    | inr b => trivial

lemma prefixSequence_append_B (I : Instance) (i j : ℕ) (hj : j < I.nB)
    (l : List (Fin I.nA ⊕ Fin I.nB)) (h : IsPrefixSequence I i j l) :
    IsPrefixSequence I i (j + 1) (l ++ [Sum.inr (⟨j, hj⟩ : Fin I.nB)]) := by
  classical
  obtain ⟨hnd, hmem, hpair⟩ := h
  have hnew : Sum.inr (⟨j, hj⟩ : Fin I.nB) ∉ l := by
    intro hx
    have hx' := (hmem _).mp hx
    simp [prefixJobs] at hx'
  refine ⟨?_, prefixJobs_B_append I i j hj l hmem, ?_⟩
  · apply List.nodup_append.mpr
    refine ⟨hnd, by simp, ?_⟩
    intro x hx y hy
    have hy' : y = Sum.inr (⟨j, hj⟩ : Fin I.nB) := by simpa using hy
    subst y
    intro heq
    apply hnew
    simpa [heq] using hx
  · apply List.pairwise_append.mpr
    refine ⟨hpair, by simp, ?_⟩
    intro x hx y hy
    have hy' : y = Sum.inr (⟨j, hj⟩ : Fin I.nB) := by simpa using hy
    subst y
    cases x with
    | inl a => trivial
    | inr b =>
      have hb := (hmem _).mp hx
      simpa [prefixJobs, prefixOrder] using hb

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

@[simp] lemma prefixJobs_full (I : Instance) : prefixJobs I I.nA I.nB = Finset.univ := by
  classical
  ext x
  cases x with
  | inl a => simp [prefixJobs]
  | inr b => simp [prefixJobs]

@[simp] lemma prefixSumCA_full (I : Instance) (l : List (Fin I.nA ⊕ Fin I.nB)) :
    prefixSumCA I I.nA l = I.sumCA l := by
  simp [prefixSumCA, Instance.sumCA]

@[simp] lemma prefixSumCB_full (I : Instance) (l : List (Fin I.nA ⊕ Fin I.nB)) :
    prefixSumCB I I.nB l = I.sumCB l := by
  simp [prefixSumCB, Instance.sumCB]

lemma prefixSequence_full_schedule (I : Instance) (l : List (Fin I.nA ⊕ Fin I.nB))
    (h : IsPrefixSequence I I.nA I.nB l) : IsSchedule Finset.univ l := by
  obtain ⟨hnd, hmem, _⟩ := h
  refine ⟨hnd, ?_⟩
  intro x
  simpa only [prefixJobs_full] using hmem x

end TwoAgentSched.TotalTotal.PrefixProof


namespace TwoAgentSched.TotalTotal.PrefixProof

/-- The jobs of the first agent, in their order of occurrence. -/
def projectionA {α β : Type*} (l : List (α ⊕ β)) : List α :=
  l.filterMap (fun x => match x with | Sum.inl a => some a | Sum.inr _ => none)

/-- The jobs of the second agent, in their order of occurrence. -/
def projectionB {α β : Type*} (l : List (α ⊕ β)) : List β :=
  l.filterMap (fun x => match x with | Sum.inl _ => none | Sum.inr b => some b)

/-- Swapping A-jobs does not alter the B-subsequence. -/
lemma exchange_A_preserves_B_order {α β : Type*} (before middle after : List (α ⊕ β))
    (a b : α) :
    projectionB (before ++ Sum.inl b :: (middle ++ Sum.inl a :: after)) =
      projectionB (before ++ Sum.inl a :: (middle ++ Sum.inl b :: after)) := by
  simp [projectionB, List.filterMap_append]

/-- Swapping B-jobs does not alter the A-subsequence. -/
lemma exchange_B_preserves_A_order {α β : Type*} (before middle after : List (α ⊕ β))
    (a b : β) :
    projectionA (before ++ Sum.inr b :: (middle ++ Sum.inr a :: after)) =
      projectionA (before ++ Sum.inr a :: (middle ++ Sum.inr b :: after)) := by
  simp [projectionA, List.filterMap_append]

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

/-- The A-subsequence undergoes exactly the corresponding exchange. -/
lemma exchange_A_projection {α β : Type*} (before middle after : List (α ⊕ β))
    (a b : α) :
    projectionA (before ++ Sum.inl b :: (middle ++ Sum.inl a :: after)) =
      projectionA before ++ b :: (projectionA middle ++ a :: projectionA after) := by
  simp [projectionA, List.filterMap_append]

/-- The B-subsequence undergoes exactly the corresponding exchange. -/
lemma exchange_B_projection {α β : Type*} (before middle after : List (α ⊕ β))
    (a b : β) :
    projectionB (before ++ Sum.inr b :: (middle ++ Sum.inr a :: after)) =
      projectionB before ++ b :: (projectionB middle ++ a :: projectionB after) := by
  simp [projectionB, List.filterMap_append]

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

/-- Sorting both projected job lists yields the interleaving order used by the DP. -/
lemma pairwise_of_projections {nA nB : ℕ} (l : List (Fin nA ⊕ Fin nB))
    (ha : (projectionA l).Pairwise (fun a b => a.val < b.val))
    (hb : (projectionB l).Pairwise (fun a b => a.val < b.val)) :
    l.Pairwise prefixOrder := by
  unfold projectionA at ha
  unfold projectionB at hb
  rw [List.pairwise_filterMap] at ha hb
  apply (ha.and hb).imp
  intro x y hxy
  cases x with
  | inl a =>
    cases y with
    | inl b => exact hxy.1 a rfl b rfl
    | inr b => trivial
  | inr a =>
    cases y with
    | inl b => trivial
    | inr b => exact hxy.2 a rfl b rfl

/-- A full schedule with sorted agent projections is a full ordered-prefix sequence. -/
lemma fullPrefix_of_projected_order (I : Instance) (l : List (Fin I.nA ⊕ Fin I.nB))
    (hsch : IsSchedule Finset.univ l)
    (ha : (projectionA l).Pairwise (fun a b => a.val < b.val))
    (hb : (projectionB l).Pairwise (fun a b => a.val < b.val)) :
    IsPrefixSequence I I.nA I.nB l := by
  refine ⟨hsch.1, ?_, pairwise_of_projections l ha hb⟩
  intro x
  simpa only [prefixJobs_full] using hsch.2 x

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

def orderOnlyA {nA nB : ℕ} (x y : Fin nA ⊕ Fin nB) : Prop :=
  match x, y with
  | Sum.inl a, Sum.inl b => a.val < b.val
  | _, _ => True

def orderOnlyB {nA nB : ℕ} (x y : Fin nA ⊕ Fin nB) : Prop :=
  match x, y with
  | Sum.inr a, Sum.inr b => a.val < b.val
  | _, _ => True

lemma projectionA_pairwise_of_order {nA nB : ℕ} (l : List (Fin nA ⊕ Fin nB))
    (h : l.Pairwise orderOnlyA) :
    (projectionA l).Pairwise (fun a b => a.val < b.val) := by
  unfold projectionA
  rw [List.pairwise_filterMap]
  apply h.imp
  intro x y hxy a ha b hb
  cases x <;> cases y <;> simp_all [orderOnlyA]

lemma projectionB_pairwise_of_order {nA nB : ℕ} (l : List (Fin nA ⊕ Fin nB))
    (h : l.Pairwise orderOnlyB) :
    (projectionB l).Pairwise (fun a b => a.val < b.val) := by
  unfold projectionB
  rw [List.pairwise_filterMap]
  apply h.imp
  intro x y hxy a ha b hb
  cases x <;> cases y <;> simp_all [orderOnlyB]

end TwoAgentSched.TotalTotal.PrefixProof


namespace TwoAgentSched.TotalTotal.PrefixProof

/-- A failure of a pairwise list property exposes two violating entries in order. -/
lemma not_pairwise_split {α : Type*} (R : α → α → Prop) (l : List α)
    (h : ¬ l.Pairwise R) :
    ∃ before a middle b after, l = before ++ a :: (middle ++ b :: after) ∧ ¬ R a b := by
  classical
  induction l with
  | nil => simp at h
  | cons z zs ih =>
    by_cases ht : zs.Pairwise R
    · have hz : ¬ ∀ y ∈ zs, R z y := by
        intro hall
        exact h (List.pairwise_cons.mpr ⟨hall, ht⟩)
      push_neg at hz
      obtain ⟨y, hy, hzy⟩ := hz
      obtain ⟨middle, after, rfl⟩ := List.append_of_mem hy
      exact ⟨[], z, middle, y, after, rfl, hzy⟩
    · obtain ⟨before, a, middle, b, after, heq, hbad⟩ := ih ht
      exact ⟨z :: before, a, middle, b, after, by simp [heq], hbad⟩

end TwoAgentSched.TotalTotal.PrefixProof


namespace TwoAgentSched.TotalTotal.PrefixProof

/-- A duplicate-free list supplies the disjointness conditions for a nonadjacent exchange. -/
lemma exchange_nodup_absences {α : Type*} (before middle after : List α) (a b : α)
    (hnd : (before ++ a :: (middle ++ b :: after)).Nodup) :
    a ≠ b ∧ a ∉ before ∧ b ∉ before ∧ a ∉ middle ∧ b ∉ middle := by
  obtain ⟨_, hrest, hdisj⟩ := List.nodup_append.mp hnd
  obtain ⟨haTail, htail⟩ := List.nodup_cons.mp hrest
  have ha_before : a ∉ before := by
    intro ha
    exact hdisj a ha a (by simp) rfl
  have hb_before : b ∉ before := by
    intro hb
    exact hdisj b hb b (by simp) rfl
  have ha_middle : a ∉ middle := by
    intro ha
    exact haTail (List.mem_append_left _ ha)
  have hb_middle : b ∉ middle := by
    intro hb
    exact (List.nodup_append.mp htail).2.2 b hb b (by simp) rfl
  have hab : a ≠ b := by
    intro hab
    subst b
    apply haTail
    simp
  exact ⟨hab, ha_before, hb_before, ha_middle, hb_middle⟩

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

/-- If A's projection is not sorted, two A-jobs form a strict index inversion in the full list. -/
lemma inversion_A {nA nB : ℕ} (l : List (Fin nA ⊕ Fin nB)) (hnd : l.Nodup)
    (hbad : ¬ (projectionA l).Pairwise (fun a b => a.val < b.val)) :
    ∃ (before middle after : List (Fin nA ⊕ Fin nB)) (a b : Fin nA),
      l = before ++ Sum.inl a :: (middle ++ Sum.inl b :: after) ∧ b.val < a.val := by
  classical
  have hn : ¬ l.Pairwise orderOnlyA := by
    intro h
    exact hbad (projectionA_pairwise_of_order l h)
  obtain ⟨before, x, middle, y, after, heq, hxy⟩ := not_pairwise_split orderOnlyA l hn
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      have hnd' : (before ++ Sum.inl a :: (middle ++ Sum.inl b :: after)).Nodup := by
        rw [← heq]
        exact hnd
      have hab' := (exchange_nodup_absences before middle after (Sum.inl a) (Sum.inl b) hnd').1
      have hab : a ≠ b := by
        intro he
        apply hab'
        simpa [he]
      have hne : a.val ≠ b.val := by
        intro he
        exact hab (Fin.ext he)
      have hnot : ¬ a.val < b.val := by simpa [orderOnlyA] using hxy
      have hlt : b.val < a.val := by omega
      exact ⟨before, middle, after, a, b, heq, hlt⟩
    | inr b => simp [orderOnlyA] at hxy
  | inr a => cases y <;> simp [orderOnlyA] at hxy

/-- If B's projection is not sorted, two B-jobs form a strict index inversion in the full list. -/
lemma inversion_B {nA nB : ℕ} (l : List (Fin nA ⊕ Fin nB)) (hnd : l.Nodup)
    (hbad : ¬ (projectionB l).Pairwise (fun a b => a.val < b.val)) :
    ∃ (before middle after : List (Fin nA ⊕ Fin nB)) (a b : Fin nB),
      l = before ++ Sum.inr a :: (middle ++ Sum.inr b :: after) ∧ b.val < a.val := by
  classical
  have hn : ¬ l.Pairwise orderOnlyB := by
    intro h
    exact hbad (projectionB_pairwise_of_order l h)
  obtain ⟨before, x, middle, y, after, heq, hxy⟩ := not_pairwise_split orderOnlyB l hn
  cases x with
  | inl a => cases y <;> simp [orderOnlyB] at hxy
  | inr a =>
    cases y with
    | inl b => simp [orderOnlyB] at hxy
    | inr b =>
      have hnd' : (before ++ Sum.inr a :: (middle ++ Sum.inr b :: after)).Nodup := by
        rw [← heq]
        exact hnd
      have hab' := (exchange_nodup_absences before middle after (Sum.inr a) (Sum.inr b) hnd').1
      have hab : a ≠ b := by
        intro he
        apply hab'
        simpa [he]
      have hne : a.val ≠ b.val := by
        intro he
        exact hab (Fin.ext he)
      have hnot : ¬ a.val < b.val := by simpa [orderOnlyB] using hxy
      have hlt : b.val < a.val := by omega
      exact ⟨before, middle, after, a, b, heq, hlt⟩

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

/- The following generic list facts adapt the previously checked helpers
   `ttm55_ct_append_right` and `ttm55_ct_cons_ne` from the two-agent project. -/
lemma completionTime_append_not_mem {ι : Type*} [DecidableEq ι] (p : ι → ℝ)
    (l₁ l₂ : List ι) (x : ι) (hx : x ∉ l₁) :
    completionTime p (l₁ ++ l₂) x = (l₁.map p).sum + completionTime p l₂ x := by
  unfold completionTime completionAt
  rw [List.idxOf_append_of_notMem hx, List.take_append]
  have e1 : l₁.take (l₁.length + l₂.idxOf x + 1) = l₁ := List.take_of_length_le (by omega)
  have e2 : l₁.length + l₂.idxOf x + 1 - l₁.length = l₂.idxOf x + 1 := by omega
  rw [e1, e2]
  simp

lemma completionTime_cons_ne {ι : Type*} [DecidableEq ι] (p : ι → ℝ)
    (y : ι) (rest : List ι) (x : ι) (hx : x ≠ y) :
    completionTime p (y :: rest) x = p y + completionTime p rest x := by
  unfold completionTime completionAt
  rw [List.idxOf_cons_ne _ (Ne.symm hx)]
  simp [List.take_succ_cons]

/-- Every job between the exchanged jobs finishes earlier by exactly the processing-time difference. -/
lemma exchange_middle_completion {ι : Type*} [DecidableEq ι] (p : ι → ℝ)
    (before middle after : List ι) (a b x : ι)
    (hx_before : x ∉ before) (hx_middle : x ∈ middle) (hxa : x ≠ a) (hxb : x ≠ b) :
    completionTime p (before ++ b :: (middle ++ a :: after)) x =
      completionTime p (before ++ a :: (middle ++ b :: after)) x - (p a - p b) := by
  rw [completionTime_append_not_mem p before _ x hx_before,
    completionTime_append_not_mem p before _ x hx_before,
    completionTime_cons_ne p b _ x hxb, completionTime_cons_ne p a _ x hxa,
    completionTime_append_mem p middle _ x hx_middle,
    completionTime_append_mem p middle _ x hx_middle]
  ring

/-- Jobs after the exchanged pair have unchanged completion time. -/
lemma exchange_after_completion {ι : Type*} [DecidableEq ι] (p : ι → ℝ)
    (before middle after : List ι) (a b x : ι)
    (hx_before : x ∉ before) (hx_middle : x ∉ middle) (hxa : x ≠ a) (hxb : x ≠ b) :
    completionTime p (before ++ b :: (middle ++ a :: after)) x =
      completionTime p (before ++ a :: (middle ++ b :: after)) x := by
  rw [completionTime_append_not_mem p before _ x hx_before,
    completionTime_append_not_mem p before _ x hx_before,
    completionTime_cons_ne p b _ x hxb, completionTime_cons_ne p a _ x hxa,
    completionTime_append_not_mem p middle _ x hx_middle,
    completionTime_append_not_mem p middle _ x hx_middle,
    completionTime_cons_ne p a _ x hxa, completionTime_cons_ne p b _ x hxb]
  ring

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

lemma completionTime_cons_self {ι : Type*} [DecidableEq ι] (p : ι → ℝ)
    (y : ι) (rest : List ι) : completionTime p (y :: rest) y = p y := by
  unfold completionTime completionAt
  simp

/-- Exchanging two jobs changes their combined completion time by the length difference. -/
lemma exchange_pair_sum {ι : Type*} [DecidableEq ι] (p : ι → ℝ)
    (before middle after : List ι) (a b : ι) (hab : a ≠ b)
    (ha_before : a ∉ before) (hb_before : b ∉ before)
    (ha_middle : a ∉ middle) (hb_middle : b ∉ middle) :
    completionTime p (before ++ b :: (middle ++ a :: after)) a +
        completionTime p (before ++ b :: (middle ++ a :: after)) b =
      completionTime p (before ++ a :: (middle ++ b :: after)) a +
        completionTime p (before ++ a :: (middle ++ b :: after)) b - (p a - p b) := by
  have ha_old : completionTime p (before ++ a :: (middle ++ b :: after)) a =
      (before.map p).sum + p a := by
    rw [completionTime_append_not_mem p before _ a ha_before, completionTime_cons_self]
  have hb_new : completionTime p (before ++ b :: (middle ++ a :: after)) b =
      (before.map p).sum + p b := by
    rw [completionTime_append_not_mem p before _ b hb_before, completionTime_cons_self]
  have hb_old : completionTime p (before ++ a :: (middle ++ b :: after)) b =
      (before.map p).sum + p a + (middle.map p).sum + p b := by
    rw [completionTime_append_not_mem p before _ b hb_before,
      completionTime_cons_ne p a _ b (Ne.symm hab),
      completionTime_append_not_mem p middle _ b hb_middle, completionTime_cons_self]
    ring
  have ha_new : completionTime p (before ++ b :: (middle ++ a :: after)) a =
      (before.map p).sum + p b + (middle.map p).sum + p a := by
    rw [completionTime_append_not_mem p before _ a ha_before,
      completionTime_cons_ne p b _ a hab,
      completionTime_append_not_mem p middle _ a ha_middle, completionTime_cons_self]
    ring
  rw [ha_new, hb_new, ha_old, hb_old]
  ring

lemma exchange_pair_sum_le {ι : Type*} [DecidableEq ι] (p : ι → ℝ)
    (before middle after : List ι) (a b : ι) (hab : a ≠ b)
    (ha_before : a ∉ before) (hb_before : b ∉ before)
    (ha_middle : a ∉ middle) (hb_middle : b ∉ middle) (hle : p b ≤ p a) :
    completionTime p (before ++ b :: (middle ++ a :: after)) a +
        completionTime p (before ++ b :: (middle ++ a :: after)) b ≤
      completionTime p (before ++ a :: (middle ++ b :: after)) a +
        completionTime p (before ++ a :: (middle ++ b :: after)) b := by
  rw [exchange_pair_sum p before middle after a b hab ha_before hb_before ha_middle hb_middle]
  linarith

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

/-- Moving the shorter of two exchanged jobs earlier cannot delay any third job. -/
lemma exchange_other_completion_le {ι : Type*} [DecidableEq ι] (p : ι → ℝ)
    (before middle after : List ι) (a b x : ι) (hxa : x ≠ a) (hxb : x ≠ b)
    (hle : p b ≤ p a) :
    completionTime p (before ++ b :: (middle ++ a :: after)) x ≤
      completionTime p (before ++ a :: (middle ++ b :: after)) x := by
  by_cases hbefore : x ∈ before
  · have hn := completionTime_append_mem p before (b :: (middle ++ a :: after)) x hbefore
    have ho := completionTime_append_mem p before (a :: (middle ++ b :: after)) x hbefore
    exact le_of_eq (hn.trans ho.symm)
  · by_cases hmiddle : x ∈ middle
    · rw [exchange_middle_completion p before middle after a b x hbefore hmiddle hxa hxb]
      linarith
    · exact le_of_eq (exchange_after_completion p before middle after a b x hbefore hmiddle hxa hxb)

end TwoAgentSched.TotalTotal.PrefixProof


namespace TwoAgentSched.TotalTotal.PrefixProof

/-- A sum comparison may combine two exceptional coordinates before comparing the rest. -/
lemma sum_le_of_two_exceptions {α : Type*} [Fintype α] [DecidableEq α]
    (f g : α → ℝ) (a b : α) (hab : a ≠ b)
    (hpair : f a + f b ≤ g a + g b)
    (hother : ∀ x, x ≠ a → x ≠ b → f x ≤ g x) :
    (∑ x, f x) ≤ ∑ x, g x := by
  classical
  let s : Finset α := Finset.univ.erase a
  have hb : b ∈ s := by simp [s, Ne.symm hab]
  have hf₁ := Finset.add_sum_erase Finset.univ f (Finset.mem_univ a)
  have hf₂ := Finset.add_sum_erase s f hb
  have hg₁ := Finset.add_sum_erase Finset.univ g (Finset.mem_univ a)
  have hg₂ := Finset.add_sum_erase s g hb
  have hs : (∑ x ∈ s.erase b, f x) ≤ ∑ x ∈ s.erase b, g x := by
    apply Finset.sum_le_sum
    intro x hx
    have hxb : x ≠ b := (Finset.mem_erase.mp hx).1
    have hxa : x ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
    exact hother x hxa hxb
  linarith

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

/-- Exchanging two A-jobs to put the shorter first weakly improves both agents' sums. -/
lemma exchange_A_objectives (I : Instance) (before middle after : List (Fin I.nA ⊕ Fin I.nB))
    (a b : Fin I.nA) (hab : a ≠ b) (hle : I.pA b ≤ I.pA a)
    (ha_before : Sum.inl a ∉ before) (hb_before : Sum.inl b ∉ before)
    (ha_middle : Sum.inl a ∉ middle) (hb_middle : Sum.inl b ∉ middle) :
    I.sumCA (before ++ Sum.inl b :: (middle ++ Sum.inl a :: after)) ≤
        I.sumCA (before ++ Sum.inl a :: (middle ++ Sum.inl b :: after)) ∧
      I.sumCB (before ++ Sum.inl b :: (middle ++ Sum.inl a :: after)) ≤
        I.sumCB (before ++ Sum.inl a :: (middle ++ Sum.inl b :: after)) := by
  have hab' : (Sum.inl a : Fin I.nA ⊕ Fin I.nB) ≠ Sum.inl b := by simpa using hab
  have hp : I.p (Sum.inl b) ≤ I.p (Sum.inl a) := by
    change (I.pA b : ℝ) ≤ (I.pA a : ℝ)
    exact_mod_cast hle
  constructor
  · unfold Instance.sumCA Instance.C
    apply sum_le_of_two_exceptions _ _ a b hab
    · exact exchange_pair_sum_le I.p before middle after (Sum.inl a) (Sum.inl b)
        hab' ha_before hb_before ha_middle hb_middle hp
    · intro x hxa hxb
      apply exchange_other_completion_le
      · simpa using hxa
      · simpa using hxb
      · exact hp
  · unfold Instance.sumCB Instance.C
    apply Finset.sum_le_sum
    intro x _
    apply exchange_other_completion_le
    · simp
    · simp
    · exact hp

/-- Exchanging two B-jobs to put the shorter first weakly improves both agents' sums. -/
lemma exchange_B_objectives (I : Instance) (before middle after : List (Fin I.nA ⊕ Fin I.nB))
    (a b : Fin I.nB) (hab : a ≠ b) (hle : I.pB b ≤ I.pB a)
    (ha_before : Sum.inr a ∉ before) (hb_before : Sum.inr b ∉ before)
    (ha_middle : Sum.inr a ∉ middle) (hb_middle : Sum.inr b ∉ middle) :
    I.sumCA (before ++ Sum.inr b :: (middle ++ Sum.inr a :: after)) ≤
        I.sumCA (before ++ Sum.inr a :: (middle ++ Sum.inr b :: after)) ∧
      I.sumCB (before ++ Sum.inr b :: (middle ++ Sum.inr a :: after)) ≤
        I.sumCB (before ++ Sum.inr a :: (middle ++ Sum.inr b :: after)) := by
  have hab' : (Sum.inr a : Fin I.nA ⊕ Fin I.nB) ≠ Sum.inr b := by simpa using hab
  have hp : I.p (Sum.inr b) ≤ I.p (Sum.inr a) := by
    change (I.pB b : ℝ) ≤ (I.pB a : ℝ)
    exact_mod_cast hle
  constructor
  · unfold Instance.sumCA Instance.C
    apply Finset.sum_le_sum
    intro x _
    apply exchange_other_completion_le
    · simp
    · simp
    · exact hp
  · unfold Instance.sumCB Instance.C
    apply sum_le_of_two_exceptions _ _ a b hab
    · exact exchange_pair_sum_le I.p before middle after (Sum.inr a) (Sum.inr b)
        hab' ha_before hb_before ha_middle hb_middle hp
    · intro x hxa hxb
      apply exchange_other_completion_le
      · simpa using hxa
      · simpa using hxb
      · exact hp

end TwoAgentSched.TotalTotal.PrefixProof


open MooreLateJobs.Shared

namespace TwoAgentSched.TotalTotal.PrefixProof

/-- A nonadjacent exchange preserves exactly the same list of jobs up to permutation. -/
lemma exchange_perm {ι : Type*} (before middle after : List ι) (a b : ι) :
    (before ++ b :: (middle ++ a :: after)).Perm (before ++ a :: (middle ++ b :: after)) := by
  have h : (a :: (middle ++ [b])).Perm (b :: (middle ++ [a])) := by
    exact ((List.Perm.cons a (List.perm_append_singleton b middle)).trans
      (List.Perm.swap b a middle)).trans (List.Perm.cons b (List.perm_append_singleton a middle).symm)
  have h' := (h.append_right after).append_left before
  simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using h'.symm

/-- A nonadjacent exchange of a schedule is a schedule of the same job set. -/
lemma exchange_preserves_schedule {ι : Type*} [DecidableEq ι] (J : Finset ι)
    (before middle after : List ι) (a b : ι)
    (h : IsSchedule J (before ++ a :: (middle ++ b :: after))) :
    IsSchedule J (before ++ b :: (middle ++ a :: after)) := by
  have hp := exchange_perm before middle after a b
  refine ⟨hp.nodup_iff.mpr h.1, ?_⟩
  intro x
  exact hp.mem_iff.trans (h.2 x)

end TwoAgentSched.TotalTotal.PrefixProof


namespace TwoAgentSched.TotalTotal.PrefixProof

/-- Moving a smaller element forward by a nonadjacent swap decreases shortlex order. -/
lemma exchange_shortlex {α : Type*} (R : α → α → Prop)
    (before middle after : List α) (a b : α) (hba : R b a) :
    List.Shortlex R (before ++ b :: (middle ++ a :: after))
      (before ++ a :: (middle ++ b :: after)) := by
  apply List.Shortlex.of_lex
  · simp only [List.length_append, List.length_cons]
  · exact List.Lex.append_left R (List.Lex.rel hba) before

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

/-- Sort A's projection, preserve B's projection, and weakly improve both objectives. -/
lemma normalize_A (I : Instance) (hA : Monotone I.pA) :
    ∀ l : List (Fin I.nA ⊕ Fin I.nB), IsSchedule Finset.univ l →
      ∃ σ : List (Fin I.nA ⊕ Fin I.nB), IsSchedule Finset.univ σ ∧
        (projectionA σ).Pairwise (fun a b => a.val < b.val) ∧ projectionB σ = projectionB l ∧
        I.sumCA σ ≤ I.sumCA l ∧ I.sumCB σ ≤ I.sumCB l := by
  classical
  let R : Fin I.nA → Fin I.nA → Prop := fun a b => a.val < b.val
  have hwf : WellFounded (fun (l₁ l₂ : List (Fin I.nA ⊕ Fin I.nB)) =>
      List.Shortlex R (projectionA l₁) (projectionA l₂)) :=
    InvImage.wf (fun l : List (Fin I.nA ⊕ Fin I.nB) => projectionA l)
      (List.Shortlex.wf (InvImage.wf (fun x : Fin I.nA => x.val) Nat.lt_wfRel.wf))
  intro l
  induction l using hwf.induction with
  | h l ih =>
    intro hsch
    by_cases hsorted : (projectionA l).Pairwise (fun a b => a.val < b.val)
    · exact ⟨l, hsch, hsorted, rfl, le_rfl, le_rfl⟩
    · obtain ⟨before, middle, after, a, b, heq, hlt⟩ := inversion_A l hsch.1 hsorted
      have hnd : (before ++ Sum.inl a :: (middle ++ Sum.inl b :: after)).Nodup := by
        rw [← heq]
        exact hsch.1
      obtain ⟨hab', ha_before, hb_before, ha_middle, hb_middle⟩ :=
        exchange_nodup_absences before middle after (Sum.inl a) (Sum.inl b) hnd
      have hab : a ≠ b := by
        intro he
        apply hab'
        simpa [he]
      have hle : I.pA b ≤ I.pA a := hA (by exact hlt.le)
      let σ := before ++ Sum.inl b :: (middle ++ Sum.inl a :: after)
      have hschOld : IsSchedule Finset.univ (before ++ Sum.inl a :: (middle ++ Sum.inl b :: after)) := by
        rw [← heq]
        exact hsch
      have hσ : IsSchedule Finset.univ σ := by
        exact exchange_preserves_schedule Finset.univ before middle after (Sum.inl a) (Sum.inl b) hschOld
      have hdesc : List.Shortlex R (projectionA σ) (projectionA l) := by
        dsimp [σ]
        rw [heq, exchange_A_projection before middle after a b,
          exchange_A_projection before middle after b a]
        exact exchange_shortlex R (projectionA before) (projectionA middle) (projectionA after) a b hlt
      have hproj : projectionB σ = projectionB l := by
        dsimp [σ]
        rw [heq]
        exact exchange_A_preserves_B_order before middle after a b
      have hobj := exchange_A_objectives I before middle after a b hab hle
        ha_before hb_before ha_middle hb_middle
      obtain ⟨τ, hτ, hτsorted, hτproj, hτA, hτB⟩ := ih σ hdesc hσ
      refine ⟨τ, hτ, hτsorted, hτproj.trans hproj, ?_, ?_⟩
      · exact le_trans hτA (by simpa only [σ, heq] using hobj.1)
      · exact le_trans hτB (by simpa only [σ, heq] using hobj.2)

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

/-- Sort B's projection, preserve A's projection, and weakly improve both objectives. -/
lemma normalize_B (I : Instance) (hB : Monotone I.pB) :
    ∀ l : List (Fin I.nA ⊕ Fin I.nB), IsSchedule Finset.univ l →
      ∃ σ : List (Fin I.nA ⊕ Fin I.nB), IsSchedule Finset.univ σ ∧
        (projectionB σ).Pairwise (fun a b => a.val < b.val) ∧ projectionA σ = projectionA l ∧
        I.sumCA σ ≤ I.sumCA l ∧ I.sumCB σ ≤ I.sumCB l := by
  classical
  let R : Fin I.nB → Fin I.nB → Prop := fun a b => a.val < b.val
  have hwf : WellFounded (fun (l₁ l₂ : List (Fin I.nA ⊕ Fin I.nB)) =>
      List.Shortlex R (projectionB l₁) (projectionB l₂)) :=
    InvImage.wf (fun l : List (Fin I.nA ⊕ Fin I.nB) => projectionB l)
      (List.Shortlex.wf (InvImage.wf (fun x : Fin I.nB => x.val) Nat.lt_wfRel.wf))
  intro l
  induction l using hwf.induction with
  | h l ih =>
    intro hsch
    by_cases hsorted : (projectionB l).Pairwise (fun a b => a.val < b.val)
    · exact ⟨l, hsch, hsorted, rfl, le_rfl, le_rfl⟩
    · obtain ⟨before, middle, after, a, b, heq, hlt⟩ := inversion_B l hsch.1 hsorted
      have hnd : (before ++ Sum.inr a :: (middle ++ Sum.inr b :: after)).Nodup := by
        rw [← heq]
        exact hsch.1
      obtain ⟨hab', ha_before, hb_before, ha_middle, hb_middle⟩ :=
        exchange_nodup_absences before middle after (Sum.inr a) (Sum.inr b) hnd
      have hab : a ≠ b := by
        intro he
        apply hab'
        simpa [he]
      have hle : I.pB b ≤ I.pB a := hB (by exact hlt.le)
      let σ := before ++ Sum.inr b :: (middle ++ Sum.inr a :: after)
      have hschOld : IsSchedule Finset.univ (before ++ Sum.inr a :: (middle ++ Sum.inr b :: after)) := by
        rw [← heq]
        exact hsch
      have hσ : IsSchedule Finset.univ σ := by
        exact exchange_preserves_schedule Finset.univ before middle after (Sum.inr a) (Sum.inr b) hschOld
      have hdesc : List.Shortlex R (projectionB σ) (projectionB l) := by
        dsimp [σ]
        rw [heq, exchange_B_projection before middle after a b,
          exchange_B_projection before middle after b a]
        exact exchange_shortlex R (projectionB before) (projectionB middle) (projectionB after) a b hlt
      have hproj : projectionA σ = projectionA l := by
        dsimp [σ]
        rw [heq]
        exact exchange_B_preserves_A_order before middle after a b
      have hobj := exchange_B_objectives I before middle after a b hab hle
        ha_before hb_before ha_middle hb_middle
      obtain ⟨τ, hτ, hτsorted, hτproj, hτA, hτB⟩ := ih σ hdesc hσ
      refine ⟨τ, hτ, hτsorted, hτproj.trans hproj, ?_, ?_⟩
      · exact le_trans hτA (by simpa only [σ, heq] using hobj.1)
      · exact le_trans hτB (by simpa only [σ, heq] using hobj.2)

end TwoAgentSched.TotalTotal.PrefixProof

open TwoAgentSched.TotalTotal TwoAgentSched.TotalTotal.PrefixProof MooreLateJobs.Shared

theorem solution (I : Instance) (hA : Monotone I.pA) (hB : Monotone I.pB) :
    ∀ l : List (Fin I.nA ⊕ Fin I.nB), IsSchedule Finset.univ l →
      ∃ σ : List (Fin I.nA ⊕ Fin I.nB), IsSchedule Finset.univ σ ∧
        σ.Pairwise (fun x y => match x, y with
          | Sum.inl a, Sum.inl b => a.val < b.val
          | Sum.inr a, Sum.inr b => a.val < b.val
          | _, _ => True) ∧
        I.sumCA σ ≤ I.sumCA l ∧ I.sumCB σ ≤ I.sumCB l := by
  intro l hl
  obtain ⟨σ, hσ, hAsorted, _, hσA, hσB⟩ := normalize_A I hA l hl
  obtain ⟨τ, hτ, hBsorted, hτproj, hτA, hτB⟩ := normalize_B I hB σ hσ
  have hAsortedτ : (projectionA τ).Pairwise (fun a b => a.val < b.val) := by
    rw [hτproj]
    exact hAsorted
  have hfull := fullPrefix_of_projected_order I τ hτ hAsortedτ hBsorted
  refine ⟨τ, hτ, ?_, le_trans hτA hσA, le_trans hτB hσB⟩
  apply hfull.2.2.imp
  intro x y hxy
  cases x <;> cases y <;> simpa [prefixOrder] using hxy
