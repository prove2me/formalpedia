-- Prove2me | solution 1 for TwoAgentSched.TotalTotal.theorem_9_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T19:13:34.255474+00:00
-- url     : https://prove2.me/submissions/01047818-516b-4690-ba68-bc0e177a7ce1

import Definitions.Def_TwoAgentSched_TotalTotal_DP
import Theorems.Thm_TwoAgentSched_TotalTotal_spt_normalization

namespace TwoAgentSched.TotalTotal

lemma dpF_zero_zero (I : Instance) (q : ℤ) :
    I.dpF 0 0 q = if q < 0 then ⊤ else 0 := by
  rw [Instance.dpF]
  simp

end TwoAgentSched.TotalTotal

namespace TwoAgentSched.TotalTotal

lemma dpF_a_only (I : Instance) (q : ℤ) (hq : 0 ≤ q) (i : ℕ) :
    I.dpF i 0 q =
      ((∑ k ∈ Finset.range i, (I.bigPij k 0 + I.pAt (k + 1)) : ℕ) : ℕ∞) := by
  induction i with
  | zero =>
      rw [Instance.dpF]
      simp [hq]
  | succ i ih =>
      rw [Instance.dpF]
      simp [hq, ih, Finset.sum_range_succ]

end TwoAgentSched.TotalTotal

namespace TwoAgentSched.TotalTotal

lemma dpF_b_only (I : Instance) (j : ℕ) (q : ℤ) :
    I.dpF 0 j q =
      if q < ((∑ k ∈ Finset.range j, I.bigPij 0 (k + 1) : ℕ) : ℤ) then ⊤ else 0 := by
  induction j generalizing q with
  | zero =>
      rw [Instance.dpF]
      simp
  | succ j ih =>
      rw [Instance.dpF]
      simp only [Nat.zero_lt_succ, Nat.succ_ne_zero, and_false, if_false,
        lt_self_iff_false, Nat.succ_sub_one, min_eq_right le_top]
      rw [Finset.sum_range_succ]
      simp only [Nat.cast_add]
      have hsum : 0 ≤ ((∑ k ∈ Finset.range j, I.bigPij 0 (k + 1) : ℕ) : ℤ) := by positivity
      by_cases hq : q < 0
      · simp only [hq, if_pos]
        split_ifs <;> simp_all <;> omega
      · simp only [hq, if_false]
        rw [ih]
        split_ifs <;> simp_all <;> omega

end TwoAgentSched.TotalTotal

namespace TwoAgentSched.TotalTotal

lemma dpF_negative (I : Instance) (i j : ℕ) (q : ℤ) (hq : q < 0) :
    I.dpF i j q = ⊤ := by
  rw [Instance.dpF]
  simp [hq]

lemma dpF_both (I : Instance) (i j : ℕ) (q : ℤ) (hq : 0 ≤ q) :
    I.dpF (i + 1) (j + 1) q =
      min (I.dpF i (j + 1) q + ((I.bigPij i (j + 1) + I.pAt (i + 1) : ℕ) : ℕ∞))
        (I.dpF (i + 1) j (q - (I.bigPij (i + 1) (j + 1) : ℤ))) := by
  rw [Instance.dpF]
  simp [hq]

end TwoAgentSched.TotalTotal

namespace TwoAgentSched.TotalTotal

lemma dpF_budget_mono_aux (I : Instance) (n : ℕ) :
    ∀ i j, i + j = n → ∀ q r : ℤ, q ≤ r → I.dpF i j r ≤ I.dpF i j q := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro i j hij q r hqr
    by_cases hqneg : q < 0
    · rw [dpF_negative I i j q hqneg]
      exact le_top
    · have hq : 0 ≤ q := by omega
      have hr : 0 ≤ r := by omega
      cases i with
      | zero =>
        rw [dpF_b_only I j r, dpF_b_only I j q]
        split_ifs <;> simp_all <;> omega
      | succ i =>
        cases j with
        | zero =>
          rw [dpF_a_only I r hr (i + 1), dpF_a_only I q hq (i + 1)]
        | succ j =>
          rw [dpF_both I i j r hr, dpF_both I i j q hq]
          apply min_le_min
          · simpa only [add_comm] using
              add_le_add_right (ih (i + (j + 1)) (by omega) i (j + 1) rfl q r hqr)
                ((I.bigPij i (j + 1) + I.pAt (i + 1) : ℕ) : ℕ∞)
          · exact ih ((i + 1) + j) (by omega) (i + 1) j rfl _ _ (by omega)

lemma dpF_budget_mono (I : Instance) (i j : ℕ) (q r : ℤ) (h : q ≤ r) :
    I.dpF i j r ≤ I.dpF i j q :=
  dpF_budget_mono_aux I (i + j) i j rfl q r h

end TwoAgentSched.TotalTotal

namespace TwoAgentSched.TotalTotal

/-- A finite mixed-prefix optimum is attained by one of the two recurrence branches. -/
lemma dpF_both_attains_branch (I : Instance) (i j : ℕ) (q : ℤ) (hq : 0 ≤ q) (m : ℕ)
    (h : I.dpF (i + 1) (j + 1) q = (m : ℕ∞)) :
    (∃ a : ℕ, I.dpF i (j + 1) q = (a : ℕ∞) ∧
      m = a + (I.bigPij i (j + 1) + I.pAt (i + 1)) ∧
      (m : ℕ∞) ≤ I.dpF (i + 1) j (q - (I.bigPij (i + 1) (j + 1) : ℤ))) ∨
    (I.dpF (i + 1) j (q - (I.bigPij (i + 1) (j + 1) : ℤ)) = (m : ℕ∞) ∧
      (m : ℕ∞) ≤ I.dpF i (j + 1) q +
        ((I.bigPij i (j + 1) + I.pAt (i + 1) : ℕ) : ℕ∞)) := by
  rw [dpF_both I i j q hq] at h
  by_cases hle : I.dpF i (j + 1) q +
      ((I.bigPij i (j + 1) + I.pAt (i + 1) : ℕ) : ℕ∞) ≤
      I.dpF (i + 1) j (q - (I.bigPij (i + 1) (j + 1) : ℤ))
  · rw [min_eq_left hle] at h
    have hne : I.dpF i (j + 1) q ≠ ⊤ := by
      intro ht
      rw [ht] at h
      simp at h
    obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hne
    left
    refine ⟨a, ha.symm, ?_, ?_⟩
    · apply ENat.natCast_inj.mp
      simpa only [← ha, Nat.cast_add] using h.symm
    · simpa only [h] using hle
  · have hge : I.dpF (i + 1) j (q - (I.bigPij (i + 1) (j + 1) : ℤ)) ≤
        I.dpF i (j + 1) q +
          ((I.bigPij i (j + 1) + I.pAt (i + 1) : ℕ) : ℕ∞) := le_of_not_ge hle
    rw [min_eq_right hge] at h
    exact Or.inr ⟨h, by simpa only [h] using hge⟩

end TwoAgentSched.TotalTotal

namespace TwoAgentSched.TotalTotal

/-- A mixed prefix is infeasible in the recurrence precisely when both branches are. -/
lemma dpF_both_eq_top_iff (I : Instance) (i j : ℕ) (q : ℤ) (hq : 0 ≤ q) :
    I.dpF (i + 1) (j + 1) q = ⊤ ↔
      I.dpF i (j + 1) q = ⊤ ∧
      I.dpF (i + 1) j (q - (I.bigPij (i + 1) (j + 1) : ℤ)) = ⊤ := by
  rw [dpF_both I i j q hq]
  change (I.dpF i (j + 1) q +
      ((I.bigPij i (j + 1) + I.pAt (i + 1) : ℕ) : ℕ∞)) ⊓
      I.dpF (i + 1) j (q - (I.bigPij (i + 1) (j + 1) : ℤ)) = ⊤ ↔ _
  simp only [inf_eq_top_iff, ENat.add_eq_top, ENat.natCast_ne_top, or_false]

end TwoAgentSched.TotalTotal


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

/-- The A-last branch: A's objective gains `P(i+1,j)`, B's is unchanged. -/
lemma prefixSequence_A_update (I : Instance) (i j : ℕ) (hi : i < I.nA)
    (l : List (Fin I.nA ⊕ Fin I.nB)) (h : IsPrefixSequence I i j l) :
    prefixSumCA I (i + 1) (l ++ [Sum.inl (⟨i, hi⟩ : Fin I.nA)]) =
        prefixSumCA I i l + (I.bigPij (i + 1) j : ℝ) ∧
      prefixSumCB I j (l ++ [Sum.inl (⟨i, hi⟩ : Fin I.nA)]) = prefixSumCB I j l := by
  classical
  have hm := h.2.1
  have hprev : ∀ a : Fin I.nA, a.val < i → Sum.inl a ∈ l := by
    intro a ha
    apply (hm _).mpr
    simp [prefixJobs, ha]
  have hnew : Sum.inl (⟨i, hi⟩ : Fin I.nA) ∉ l := by
    intro hx
    have := (hm _).mp hx
    simp [prefixJobs] at this
  have hs := prefixSequence_append_A I i j hi l h
  refine ⟨prefixSumCA_append_next_bigP I i j hi l hprev hnew hs.1 hs.2.1, ?_⟩
  apply prefixSumCB_append
  intro b hb
  apply (hm _).mpr
  simp [prefixJobs, hb]

/-- The B-last branch: B's objective gains `P(i,j+1)`, A's is unchanged. -/
lemma prefixSequence_B_update (I : Instance) (i j : ℕ) (hj : j < I.nB)
    (l : List (Fin I.nA ⊕ Fin I.nB)) (h : IsPrefixSequence I i j l) :
    prefixSumCA I i (l ++ [Sum.inr (⟨j, hj⟩ : Fin I.nB)]) = prefixSumCA I i l ∧
      prefixSumCB I (j + 1) (l ++ [Sum.inr (⟨j, hj⟩ : Fin I.nB)]) =
        prefixSumCB I j l + (I.bigPij i (j + 1) : ℝ) := by
  classical
  have hm := h.2.1
  have hprev : ∀ b : Fin I.nB, b.val < j → Sum.inr b ∈ l := by
    intro b hb
    apply (hm _).mpr
    simp [prefixJobs, hb]
  have hnew : Sum.inr (⟨j, hj⟩ : Fin I.nB) ∉ l := by
    intro hx
    have := (hm _).mp hx
    simp [prefixJobs] at this
  have hs := prefixSequence_append_B I i j hj l h
  refine ⟨?_, prefixSumCB_append_next_bigP I i j hj l hprev hnew hs.1 hs.2.1⟩
  apply prefixSumCA_append
  intro a ha
  apply (hm _).mpr
  simp [prefixJobs, ha]

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

/-- Construct the A-last branch without changing the B-budget. -/
lemma feasible_append_A (I : Instance) (i j : ℕ) (hi : i < I.nA) (q : ℤ)
    (l : List (Fin I.nA ⊕ Fin I.nB)) (hs : IsPrefixSequence I i j l)
    (hb : prefixSumCB I j l ≤ (q : ℝ)) :
    IsPrefixSequence I (i + 1) j (l ++ [Sum.inl (⟨i, hi⟩ : Fin I.nA)]) ∧
    prefixSumCB I j (l ++ [Sum.inl (⟨i, hi⟩ : Fin I.nA)]) ≤ (q : ℝ) ∧
    prefixSumCA I (i + 1) (l ++ [Sum.inl (⟨i, hi⟩ : Fin I.nA)]) =
      prefixSumCA I i l + (I.bigPij (i + 1) j : ℝ) := by
  have hext := prefixSequence_append_A I i j hi l hs
  have hcost := prefixSequence_A_update I i j hi l hs
  exact ⟨hext, by simpa only [hcost.2] using hb, hcost.1⟩

/-- Construct the B-last branch, charging the new completion time to its budget. -/
lemma feasible_append_B (I : Instance) (i j : ℕ) (hj : j < I.nB) (q : ℤ)
    (l : List (Fin I.nA ⊕ Fin I.nB)) (hs : IsPrefixSequence I i j l)
    (hb : prefixSumCB I j l ≤ ((q - (I.bigPij i (j + 1) : ℤ) : ℤ) : ℝ)) :
    IsPrefixSequence I i (j + 1) (l ++ [Sum.inr (⟨j, hj⟩ : Fin I.nB)]) ∧
    prefixSumCB I (j + 1) (l ++ [Sum.inr (⟨j, hj⟩ : Fin I.nB)]) ≤ (q : ℝ) ∧
    prefixSumCA I i (l ++ [Sum.inr (⟨j, hj⟩ : Fin I.nB)]) = prefixSumCA I i l := by
  have hext := prefixSequence_append_B I i j hj l hs
  have hcost := prefixSequence_B_update I i j hj l hs
  refine ⟨hext, ?_, hcost.1⟩
  rw [hcost.2]
  push_cast at hb
  linarith

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

lemma prefixSequence_pop_A (I : Instance) (i j : ℕ) (hi : i < I.nA)
    (l : List (Fin I.nA ⊕ Fin I.nB))
    (h : IsPrefixSequence I (i + 1) j (l ++ [Sum.inl (⟨i, hi⟩ : Fin I.nA)])) :
    IsPrefixSequence I i j l := by
  classical
  obtain ⟨hnd, hmem, hpair⟩ := h
  have hnew : Sum.inl (⟨i, hi⟩ : Fin I.nA) ∉ l := by
    intro hx
    exact (List.nodup_append.mp hnd).2.2 _ hx _ (by simp) rfl
  refine ⟨(List.nodup_append.mp hnd).1, ?_, (List.pairwise_append.mp hpair).1⟩
  intro x
  by_cases hx : x = Sum.inl (⟨i, hi⟩ : Fin I.nA)
  · subst x
    simp [hnew, prefixJobs]
  · have hm := hmem x
    rw [prefixJobs_A_succ I i j hi] at hm
    simp only [List.mem_append, List.mem_singleton, Finset.mem_insert, hx, or_false, false_or] at hm
    exact hm

lemma prefixSequence_pop_B (I : Instance) (i j : ℕ) (hj : j < I.nB)
    (l : List (Fin I.nA ⊕ Fin I.nB))
    (h : IsPrefixSequence I i (j + 1) (l ++ [Sum.inr (⟨j, hj⟩ : Fin I.nB)])) :
    IsPrefixSequence I i j l := by
  classical
  obtain ⟨hnd, hmem, hpair⟩ := h
  have hnew : Sum.inr (⟨j, hj⟩ : Fin I.nB) ∉ l := by
    intro hx
    exact (List.nodup_append.mp hnd).2.2 _ hx _ (by simp) rfl
  refine ⟨(List.nodup_append.mp hnd).1, ?_, (List.pairwise_append.mp hpair).1⟩
  intro x
  by_cases hx : x = Sum.inr (⟨j, hj⟩ : Fin I.nB)
  · subst x
    simp [hnew, prefixJobs]
  · have hm := hmem x
    rw [prefixJobs_B_succ I i j hj] at hm
    simp only [List.mem_append, List.mem_singleton, Finset.mem_insert, hx, or_false, false_or] at hm
    exact hm

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

/-- Removing a final A-job preserves B-feasibility and exposes the A-cost update. -/
lemma feasible_pop_A (I : Instance) (i j : ℕ) (hi : i < I.nA) (q : ℤ)
    (l : List (Fin I.nA ⊕ Fin I.nB))
    (hs : IsPrefixSequence I (i + 1) j (l ++ [Sum.inl (⟨i, hi⟩ : Fin I.nA)]))
    (hb : prefixSumCB I j (l ++ [Sum.inl (⟨i, hi⟩ : Fin I.nA)]) ≤ (q : ℝ)) :
    IsPrefixSequence I i j l ∧ prefixSumCB I j l ≤ (q : ℝ) ∧
      prefixSumCA I (i + 1) (l ++ [Sum.inl (⟨i, hi⟩ : Fin I.nA)]) =
        prefixSumCA I i l + (I.bigPij (i + 1) j : ℝ) := by
  have hpre := prefixSequence_pop_A I i j hi l hs
  have hcost := prefixSequence_A_update I i j hi l hpre
  exact ⟨hpre, by simpa only [hcost.2] using hb, hcost.1⟩

/-- Removing a final B-job refunds its completion time to the predecessor budget. -/
lemma feasible_pop_B (I : Instance) (i j : ℕ) (hj : j < I.nB) (q : ℤ)
    (l : List (Fin I.nA ⊕ Fin I.nB))
    (hs : IsPrefixSequence I i (j + 1) (l ++ [Sum.inr (⟨j, hj⟩ : Fin I.nB)]))
    (hb : prefixSumCB I (j + 1) (l ++ [Sum.inr (⟨j, hj⟩ : Fin I.nB)]) ≤ (q : ℝ)) :
    IsPrefixSequence I i j l ∧
      prefixSumCB I j l ≤ ((q - (I.bigPij i (j + 1) : ℤ) : ℤ) : ℝ) ∧
      prefixSumCA I i (l ++ [Sum.inr (⟨j, hj⟩ : Fin I.nB)]) = prefixSumCA I i l := by
  have hpre := prefixSequence_pop_B I i j hj l hs
  have hcost := prefixSequence_B_update I i j hj l hpre
  refine ⟨hpre, ?_, hcost.1⟩
  rw [hcost.2] at hb
  push_cast
  linarith

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

/-- A nonempty mixed ordered prefix ends with one of the two next prefix jobs. -/
lemma prefixSequence_split_both (I : Instance) (i j : ℕ) (hi : i < I.nA) (hj : j < I.nB)
    (l : List (Fin I.nA ⊕ Fin I.nB)) (h : IsPrefixSequence I (i + 1) (j + 1) l) :
    ∃ pre : List (Fin I.nA ⊕ Fin I.nB),
      (l = pre ++ [Sum.inl (⟨i, hi⟩ : Fin I.nA)] ∧ IsPrefixSequence I i (j + 1) pre) ∨
      (l = pre ++ [Sum.inr (⟨j, hj⟩ : Fin I.nB)] ∧ IsPrefixSequence I (i + 1) j pre) := by
  classical
  rcases List.eq_nil_or_concat' l with hnil | ⟨pre, z, hl⟩
  · have ha : Sum.inl (⟨i, hi⟩ : Fin I.nA) ∈ l :=
      (h.2.1 _).mpr (by simp [prefixJobs])
    simp [hnil] at ha
  · rw [hl] at h
    cases z with
    | inl a =>
      have ha := last_A_eq_prefix I i (j + 1) hi pre a h.2.2 h.2.1
      subst a
      exact ⟨pre, Or.inl ⟨hl, prefixSequence_pop_A I i (j + 1) hi pre h⟩⟩
    | inr b =>
      have hb := last_B_eq_prefix I (i + 1) j hj pre b h.2.2 h.2.1
      subst b
      exact ⟨pre, Or.inr ⟨hl, prefixSequence_pop_B I (i + 1) j hj pre h⟩⟩

/-- A nonempty ordered prefix containing no B-jobs ends in its last A-job. -/
lemma prefixSequence_split_A (I : Instance) (i : ℕ) (hi : i < I.nA)
    (l : List (Fin I.nA ⊕ Fin I.nB)) (h : IsPrefixSequence I (i + 1) 0 l) :
    ∃ pre, l = pre ++ [Sum.inl (⟨i, hi⟩ : Fin I.nA)] ∧ IsPrefixSequence I i 0 pre := by
  classical
  rcases List.eq_nil_or_concat' l with hnil | ⟨pre, z, hl⟩
  · have ha : Sum.inl (⟨i, hi⟩ : Fin I.nA) ∈ l :=
      (h.2.1 _).mpr (by simp [prefixJobs])
    simp [hnil] at ha
  · rw [hl] at h
    cases z with
    | inl a =>
      have ha := last_A_eq_prefix I i 0 hi pre a h.2.2 h.2.1
      subst a
      exact ⟨pre, hl, prefixSequence_pop_A I i 0 hi pre h⟩
    | inr b =>
      have hb : Sum.inr b ∈ prefixJobs I (i + 1) 0 := (h.2.1 _).mp (by simp)
      simp [prefixJobs] at hb

/-- A nonempty ordered prefix containing no A-jobs ends in its last B-job. -/
lemma prefixSequence_split_B (I : Instance) (j : ℕ) (hj : j < I.nB)
    (l : List (Fin I.nA ⊕ Fin I.nB)) (h : IsPrefixSequence I 0 (j + 1) l) :
    ∃ pre, l = pre ++ [Sum.inr (⟨j, hj⟩ : Fin I.nB)] ∧ IsPrefixSequence I 0 j pre := by
  classical
  rcases List.eq_nil_or_concat' l with hnil | ⟨pre, z, hl⟩
  · have hb : Sum.inr (⟨j, hj⟩ : Fin I.nB) ∈ l :=
      (h.2.1 _).mpr (by simp [prefixJobs])
    simp [hnil] at hb
  · rw [hl] at h
    cases z with
    | inl a =>
      have ha : Sum.inl a ∈ prefixJobs I 0 (j + 1) := (h.2.1 _).mp (by simp)
      simp [prefixJobs] at ha
    | inr b =>
      have hb := last_B_eq_prefix I 0 j hj pre b h.2.2 h.2.1
      subst b
      exact ⟨pre, hl, prefixSequence_pop_B I 0 j hj pre h⟩

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

/-- Target-shaped correctness specification restricted to ordered prefix sequences. -/
def OrderedDPSpec (I : Instance) (i j : ℕ) (q : ℤ) : Prop :=
  (I.dpF i j q = ⊤ ↔
      ¬ ∃ l : List (Fin I.nA ⊕ Fin I.nB),
        IsPrefixSequence I i j l ∧ prefixSumCB I j l ≤ (q : ℝ)) ∧
    ∀ m : ℕ, I.dpF i j q = (m : ℕ∞) →
      (∃ l : List (Fin I.nA ⊕ Fin I.nB),
        IsPrefixSequence I i j l ∧ prefixSumCB I j l ≤ (q : ℝ) ∧
          prefixSumCA I i l = (m : ℝ)) ∧
      ∀ l : List (Fin I.nA ⊕ Fin I.nB),
        IsPrefixSequence I i j l → prefixSumCB I j l ≤ (q : ℝ) →
          (m : ℝ) ≤ prefixSumCA I i l

/-- Under the two predecessor specifications, the mixed-prefix infinity criterion is correct. -/
lemma orderedDP_mixed_top (I : Instance) (i j : ℕ) (hi : i < I.nA) (hj : j < I.nB)
    (q : ℤ) (hq : 0 ≤ q)
    (ha : OrderedDPSpec I i (j + 1) q)
    (hb : OrderedDPSpec I (i + 1) j (q - (I.bigPij (i + 1) (j + 1) : ℤ))) :
    I.dpF (i + 1) (j + 1) q = ⊤ ↔
      ¬ ∃ l : List (Fin I.nA ⊕ Fin I.nB),
        IsPrefixSequence I (i + 1) (j + 1) l ∧ prefixSumCB I (j + 1) l ≤ (q : ℝ) := by
  rw [dpF_both_eq_top_iff I i j q hq]
  constructor
  · rintro ⟨hta, htb⟩ ⟨l, hs, hbudget⟩
    obtain ⟨pre, hlast | hlast⟩ := prefixSequence_split_both I i j hi hj l hs
    · obtain ⟨hl, _⟩ := hlast
      rw [hl] at hs hbudget
      have hp := feasible_pop_A I i (j + 1) hi q pre hs hbudget
      exact (ha.1.mp hta) ⟨pre, hp.1, hp.2.1⟩
    · obtain ⟨hl, _⟩ := hlast
      rw [hl] at hs hbudget
      have hp := feasible_pop_B I (i + 1) j hj q pre hs hbudget
      exact (hb.1.mp htb) ⟨pre, hp.1, hp.2.1⟩
  · intro hnone
    constructor
    · by_contra hne
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
      obtain ⟨pre, hs, hbudget, _⟩ := (ha.2 m hm.symm).1
      have hext := feasible_append_A I i (j + 1) hi q pre hs hbudget
      exact hnone ⟨_, hext.1, hext.2.1⟩
    · by_contra hne
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
      obtain ⟨pre, hs, hbudget, _⟩ := (hb.2 m hm.symm).1
      have hext := feasible_append_B I (i + 1) j hj q pre hs hbudget
      exact hnone ⟨_, hext.1, hext.2.1⟩

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

lemma orderedDP_finite_of_feasible (I : Instance) (i j : ℕ) (q : ℤ)
    (h : OrderedDPSpec I i j q) (l : List (Fin I.nA ⊕ Fin I.nB))
    (hs : IsPrefixSequence I i j l) (hb : prefixSumCB I j l ≤ (q : ℝ)) :
    ∃ m : ℕ, I.dpF i j q = (m : ℕ∞) := by
  have hne : I.dpF i j q ≠ ⊤ := by
    intro ht
    exact (h.1.mp ht) ⟨l, hs, hb⟩
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
  exact ⟨m, hm.symm⟩

/-- A finite mixed-prefix DP value is attained when both predecessors satisfy the specification. -/
lemma orderedDP_mixed_attained (I : Instance) (i j : ℕ) (hi : i < I.nA) (hj : j < I.nB)
    (q : ℤ) (hq : 0 ≤ q)
    (ha : OrderedDPSpec I i (j + 1) q)
    (hb : OrderedDPSpec I (i + 1) j (q - (I.bigPij (i + 1) (j + 1) : ℤ)))
    (m : ℕ) (hm : I.dpF (i + 1) (j + 1) q = (m : ℕ∞)) :
    ∃ l : List (Fin I.nA ⊕ Fin I.nB),
      IsPrefixSequence I (i + 1) (j + 1) l ∧ prefixSumCB I (j + 1) l ≤ (q : ℝ) ∧
        prefixSumCA I (i + 1) l = (m : ℝ) := by
  rcases dpF_both_attains_branch I i j q hq m hm with hA | hB
  · obtain ⟨a, haeq, hval, _⟩ := hA
    obtain ⟨pre, hs, hbudget, hcost⟩ := (ha.2 a haeq).1
    have hext := feasible_append_A I i (j + 1) hi q pre hs hbudget
    refine ⟨_, hext.1, hext.2.1, ?_⟩
    rw [hext.2.2, hcost, ← bigPij_A_succ I i (j + 1) hi, hval]
    simp
  · obtain ⟨hbeq, _⟩ := hB
    obtain ⟨pre, hs, hbudget, hcost⟩ := (hb.2 m hbeq).1
    have hext := feasible_append_B I (i + 1) j hj q pre hs hbudget
    refine ⟨_, hext.1, hext.2.1, ?_⟩
    rw [hext.2.2, hcost]

/-- Every feasible mixed-prefix sequence has A-cost at least a finite DP value. -/
lemma orderedDP_mixed_lower (I : Instance) (i j : ℕ) (hi : i < I.nA) (hj : j < I.nB)
    (q : ℤ) (hq : 0 ≤ q)
    (ha : OrderedDPSpec I i (j + 1) q)
    (hb : OrderedDPSpec I (i + 1) j (q - (I.bigPij (i + 1) (j + 1) : ℤ)))
    (m : ℕ) (hm : I.dpF (i + 1) (j + 1) q = (m : ℕ∞))
    (l : List (Fin I.nA ⊕ Fin I.nB)) (hs : IsPrefixSequence I (i + 1) (j + 1) l)
    (hbudget : prefixSumCB I (j + 1) l ≤ (q : ℝ)) :
    (m : ℝ) ≤ prefixSumCA I (i + 1) l := by
  have hmA : (m : ℕ∞) ≤ I.dpF i (j + 1) q +
      ((I.bigPij i (j + 1) + I.pAt (i + 1) : ℕ) : ℕ∞) := by
    rw [← hm, dpF_both I i j q hq]
    exact min_le_left _ _
  have hmB : (m : ℕ∞) ≤
      I.dpF (i + 1) j (q - (I.bigPij (i + 1) (j + 1) : ℤ)) := by
    rw [← hm, dpF_both I i j q hq]
    exact min_le_right _ _
  obtain ⟨pre, hlast | hlast⟩ := prefixSequence_split_both I i j hi hj l hs
  · obtain ⟨hl, _⟩ := hlast
    rw [hl] at hs hbudget ⊢
    have hp := feasible_pop_A I i (j + 1) hi q pre hs hbudget
    obtain ⟨a, haeq⟩ := orderedDP_finite_of_feasible I i (j + 1) q ha pre hp.1 hp.2.1
    have hbound := (ha.2 a haeq).2 pre hp.1 hp.2.1
    have hmNat : m ≤ a + (I.bigPij i (j + 1) + I.pAt (i + 1)) := by
      have hcast : (m : ℕ∞) ≤
          ((a + (I.bigPij i (j + 1) + I.pAt (i + 1)) : ℕ) : ℕ∞) := by
        simpa only [haeq, Nat.cast_add] using hmA
      exact_mod_cast hcast
    have hmReal : (m : ℝ) ≤ (a : ℝ) + (I.bigPij (i + 1) (j + 1) : ℝ) := by
      rw [← bigPij_A_succ I i (j + 1) hi]
      exact_mod_cast hmNat
    linarith [hp.2.2]
  · obtain ⟨hl, _⟩ := hlast
    rw [hl] at hs hbudget ⊢
    have hp := feasible_pop_B I (i + 1) j hj q pre hs hbudget
    obtain ⟨b, hbeq⟩ := orderedDP_finite_of_feasible I (i + 1) j _ hb pre hp.1 hp.2.1
    have hbound := (hb.2 b hbeq).2 pre hp.1 hp.2.1
    have hmBNat : m ≤ b := by
      have hcast : (m : ℕ∞) ≤ (b : ℕ∞) := by simpa only [hbeq] using hmB
      exact_mod_cast hcast
    have hmBReal : (m : ℝ) ≤ (b : ℝ) := by exact_mod_cast hmBNat
    linarith [hp.2.2]

/-- Full mixed-prefix step for the target-shaped ordered DP specification. -/
lemma orderedDP_mixed_step (I : Instance) (i j : ℕ) (hi : i < I.nA) (hj : j < I.nB)
    (q : ℤ) (hq : 0 ≤ q)
    (ha : OrderedDPSpec I i (j + 1) q)
    (hb : OrderedDPSpec I (i + 1) j (q - (I.bigPij (i + 1) (j + 1) : ℤ))) :
    OrderedDPSpec I (i + 1) (j + 1) q := by
  refine ⟨orderedDP_mixed_top I i j hi hj q hq ha hb, ?_⟩
  intro m hm
  exact ⟨orderedDP_mixed_attained I i j hi hj q hq ha hb m hm,
    orderedDP_mixed_lower I i j hi hj q hq ha hb m hm⟩

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

/-- Every ordered A-only prefix has exactly the cost computed by the A-only recurrence. -/
lemma prefixSequence_A_only_cost (I : Instance) :
    ∀ i, i ≤ I.nA → ∀ l : List (Fin I.nA ⊕ Fin I.nB), IsPrefixSequence I i 0 l →
      prefixSumCA I i l =
        ((∑ k ∈ Finset.range i, (I.bigPij k 0 + I.pAt (k + 1)) : ℕ) : ℝ) := by
  intro i
  induction i with
  | zero =>
    intro _ l _
    simp [prefixSumCA]
  | succ i ih =>
    intro hi l hl
    have hi' : i < I.nA := by omega
    obtain ⟨pre, rfl, hp⟩ := prefixSequence_split_A I i hi' l hl
    rw [(prefixSequence_A_update I i 0 hi' pre hp).1]
    rw [ih (by omega) pre hp]
    rw [Finset.sum_range_succ]
    rw [bigPij_A_succ I i 0 hi']
    simp

end TwoAgentSched.TotalTotal.PrefixProof



namespace TwoAgentSched.TotalTotal.PrefixProof

@[simp] lemma prefixJobs_zero (I : Instance) : prefixJobs I 0 0 = ∅ := by
  classical
  ext x
  cases x with
  | inl a => simp [prefixJobs]
  | inr b => simp [prefixJobs]

lemma prefixSequence_zero (I : Instance) : IsPrefixSequence I 0 0 [] := by
  refine ⟨by simp, ?_, by simp⟩
  intro x
  simp

lemma prefixSequence_zero_eq_nil (I : Instance) (l : List (Fin I.nA ⊕ Fin I.nB))
    (h : IsPrefixSequence I 0 0 l) : l = [] := by
  cases l with
  | nil => rfl
  | cons x xs =>
    have hx : x ∈ x :: xs := by simp
    have hp := (h.2.1 x).mp hx
    simp at hp

@[simp] lemma prefixSumCA_zero (I : Instance) (l : List (Fin I.nA ⊕ Fin I.nB)) :
    prefixSumCA I 0 l = 0 := by
  simp [prefixSumCA]

@[simp] lemma prefixSumCB_zero (I : Instance) (l : List (Fin I.nA ⊕ Fin I.nB)) :
    prefixSumCB I 0 l = 0 := by
  simp [prefixSumCB]

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

/-- Every pair of in-range prefixes has an ordered sequence. -/
lemma prefixSequence_exists (I : Instance) :
    ∀ i j, i ≤ I.nA → j ≤ I.nB →
      ∃ l : List (Fin I.nA ⊕ Fin I.nB), IsPrefixSequence I i j l := by
  intro i
  induction i with
  | zero =>
    intro j _
    induction j with
    | zero =>
      intro _
      exact ⟨[], prefixSequence_zero I⟩
    | succ j ih =>
      intro hj
      obtain ⟨l, hl⟩ := ih (by omega)
      have hj' : j < I.nB := by omega
      exact ⟨l ++ [Sum.inr (⟨j, hj'⟩ : Fin I.nB)], prefixSequence_append_B I 0 j hj' l hl⟩
  | succ i ih =>
    intro j hi hj
    obtain ⟨l, hl⟩ := ih j (by omega) hj
    have hi' : i < I.nA := by omega
    exact ⟨l ++ [Sum.inl (⟨i, hi'⟩ : Fin I.nA)], prefixSequence_append_A I i j hi' l hl⟩

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

lemma completionTime_nonneg (I : Instance) (l : List (Fin I.nA ⊕ Fin I.nB))
    (x : Fin I.nA ⊕ Fin I.nB) : 0 ≤ I.C l x := by
  unfold Instance.C completionTime completionAt
  apply List.sum_nonneg
  intro y hy
  obtain ⟨z, _, rfl⟩ := List.mem_map.mp hy
  cases z with
  | inl a => simp [Instance.p]
  | inr b => simp [Instance.p]

lemma prefixSumCA_nonneg (I : Instance) (i : ℕ) (l : List (Fin I.nA ⊕ Fin I.nB)) :
    0 ≤ prefixSumCA I i l := by
  unfold prefixSumCA
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact completionTime_nonneg I l _
  · exact le_rfl

lemma prefixSumCB_nonneg (I : Instance) (j : ℕ) (l : List (Fin I.nA ⊕ Fin I.nB)) :
    0 ≤ prefixSumCB I j l := by
  unfold prefixSumCB
  apply Finset.sum_nonneg
  intro b _
  split_ifs
  · exact completionTime_nonneg I l _
  · exact le_rfl

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

/-- On an A-only prefix, DP infinity is equivalent to absence of a feasible ordered schedule. -/
lemma dpF_A_only_eq_top_iff_infeasible (I : Instance) (i : ℕ) (hi : i ≤ I.nA) (q : ℤ) :
    I.dpF i 0 q = ⊤ ↔
      ¬ ∃ l : List (Fin I.nA ⊕ Fin I.nB),
        IsPrefixSequence I i 0 l ∧ prefixSumCB I 0 l ≤ (q : ℝ) := by
  by_cases hq : q < 0
  · have hqR : (q : ℝ) < 0 := by exact_mod_cast hq
    have hnone : ¬ ∃ l : List (Fin I.nA ⊕ Fin I.nB),
        IsPrefixSequence I i 0 l ∧ prefixSumCB I 0 l ≤ (q : ℝ) := by
      rintro ⟨l, _, hl⟩
      have hn := prefixSumCB_nonneg I 0 l
      linarith
    exact ⟨fun _ => hnone, fun _ => dpF_negative I i 0 q hq⟩
  · have hq' : 0 ≤ q := by omega
    have hqR : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq'
    obtain ⟨l, hl⟩ := prefixSequence_exists I i 0 hi (Nat.zero_le _)
    have hex : ∃ l : List (Fin I.nA ⊕ Fin I.nB),
        IsPrefixSequence I i 0 l ∧ prefixSumCB I 0 l ≤ (q : ℝ) := by
      exact ⟨l, hl, by simpa only [prefixSumCB_zero] using hqR⟩
    have hfin : I.dpF i 0 q ≠ ⊤ := by
      rw [dpF_a_only I q hq' i]
      exact ENat.natCast_ne_top _
    exact ⟨fun htop => (hfin htop).elim, fun hnone => (hnone hex).elim⟩

/-- An A-only finite DP value is attained and is optimal over ordered prefix schedules. -/
lemma dpF_A_only_finite_optimum (I : Instance) (i : ℕ) (hi : i ≤ I.nA) (q : ℤ) (m : ℕ)
    (h : I.dpF i 0 q = (m : ℕ∞)) :
    (∃ l : List (Fin I.nA ⊕ Fin I.nB),
      IsPrefixSequence I i 0 l ∧ prefixSumCB I 0 l ≤ (q : ℝ) ∧
        prefixSumCA I i l = (m : ℝ)) ∧
    ∀ l : List (Fin I.nA ⊕ Fin I.nB),
      IsPrefixSequence I i 0 l → prefixSumCB I 0 l ≤ (q : ℝ) →
        (m : ℝ) ≤ prefixSumCA I i l := by
  have hq : 0 ≤ q := by
    by_contra hn
    have hn' : q < 0 := by omega
    rw [dpF_negative I i 0 q hn'] at h
    simp at h
  have hcost : m = ∑ k ∈ Finset.range i, (I.bigPij k 0 + I.pAt (k + 1)) := by
    have heq : ((∑ k ∈ Finset.range i, (I.bigPij k 0 + I.pAt (k + 1)) : ℕ) : ℕ∞) = m := by
      simpa only [dpF_a_only I q hq i] using h
    exact (ENat.natCast_inj.mp heq).symm
  subst m
  have hqR : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  obtain ⟨l, hl⟩ := prefixSequence_exists I i 0 hi (Nat.zero_le _)
  constructor
  · exact ⟨l, hl, by simpa only [prefixSumCB_zero] using hqR,
      prefixSequence_A_only_cost I i hi l hl⟩
  · intro l hl _
    exact le_of_eq (prefixSequence_A_only_cost I i hi l hl).symm

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

/-- Every ordered B-only prefix has the cumulative B-completion cost of the recurrence. -/
lemma prefixSequence_B_only_cost (I : Instance) :
    ∀ j, j ≤ I.nB → ∀ l : List (Fin I.nA ⊕ Fin I.nB), IsPrefixSequence I 0 j l →
      prefixSumCB I j l = ((∑ k ∈ Finset.range j, I.bigPij 0 (k + 1) : ℕ) : ℝ) := by
  intro j
  induction j with
  | zero =>
    intro _ l _
    simp [prefixSumCB]
  | succ j ih =>
    intro hj l hl
    have hj' : j < I.nB := by omega
    obtain ⟨pre, rfl, hp⟩ := prefixSequence_split_B I j hj' l hl
    rw [(prefixSequence_B_update I 0 j hj' pre hp).2]
    rw [ih (by omega) pre hp]
    rw [Finset.sum_range_succ]
    simp

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

/-- On a B-only prefix, DP infinity is equivalent to absence of a feasible ordered schedule. -/
lemma dpF_B_only_eq_top_iff_infeasible (I : Instance) (j : ℕ) (hj : j ≤ I.nB) (q : ℤ) :
    I.dpF 0 j q = ⊤ ↔
      ¬ ∃ l : List (Fin I.nA ⊕ Fin I.nB),
        IsPrefixSequence I 0 j l ∧ prefixSumCB I j l ≤ (q : ℝ) := by
  let c : ℕ := ∑ k ∈ Finset.range j, I.bigPij 0 (k + 1)
  have hfeas : (∃ l : List (Fin I.nA ⊕ Fin I.nB),
      IsPrefixSequence I 0 j l ∧ prefixSumCB I j l ≤ (q : ℝ)) ↔ (c : ℤ) ≤ q := by
    constructor
    · rintro ⟨l, hl, hb⟩
      rw [prefixSequence_B_only_cost I j hj l hl] at hb
      exact_mod_cast hb
    · intro hq
      obtain ⟨l, hl⟩ := prefixSequence_exists I 0 j (Nat.zero_le _) hj
      refine ⟨l, hl, ?_⟩
      rw [prefixSequence_B_only_cost I j hj l hl]
      exact_mod_cast hq
  rw [hfeas, dpF_b_only]
  change (if q < (c : ℤ) then (⊤ : ℕ∞) else 0) = ⊤ ↔ ¬ (c : ℤ) ≤ q
  by_cases hc : q < (c : ℤ)
  · simp [hc, not_le.mpr hc]
  · simp [hc, le_of_not_gt hc]

/-- A finite B-only DP value is attained and is optimal over ordered prefix schedules. -/
lemma dpF_B_only_finite_optimum (I : Instance) (j : ℕ) (hj : j ≤ I.nB) (q : ℤ) (m : ℕ)
    (h : I.dpF 0 j q = (m : ℕ∞)) :
    (∃ l : List (Fin I.nA ⊕ Fin I.nB),
      IsPrefixSequence I 0 j l ∧ prefixSumCB I j l ≤ (q : ℝ) ∧
        prefixSumCA I 0 l = (m : ℝ)) ∧
    ∀ l : List (Fin I.nA ⊕ Fin I.nB),
      IsPrefixSequence I 0 j l → prefixSumCB I j l ≤ (q : ℝ) →
        (m : ℝ) ≤ prefixSumCA I 0 l := by
  let c : ℕ := ∑ k ∈ Finset.range j, I.bigPij 0 (k + 1)
  have hq : (c : ℤ) ≤ q := by
    by_contra hn
    have hn' : q < (c : ℤ) := by omega
    rw [dpF_b_only] at h
    change (if q < (c : ℤ) then (⊤ : ℕ∞) else 0) = (m : ℕ∞) at h
    simp [hn'] at h
  have hm : m = 0 := by
    have hzero : (0 : ℕ∞) = (m : ℕ∞) := by
      rw [dpF_b_only] at h
      change (if q < (c : ℤ) then (⊤ : ℕ∞) else 0) = (m : ℕ∞) at h
      simpa only [not_lt.mpr hq, if_false] using h
    exact_mod_cast hzero.symm
  subst m
  obtain ⟨l, hl⟩ := prefixSequence_exists I 0 j (Nat.zero_le _) hj
  constructor
  · refine ⟨l, hl, ?_, by simp⟩
    rw [prefixSequence_B_only_cost I j hj l hl]
    exact_mod_cast hq
  · intro l _ _
    simp

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

/-- The DP is correct for every ordered pair of in-range prefixes and integer budget. -/
lemma orderedDP_all_aux (I : Instance) (n : ℕ) :
    ∀ i j, i + j = n → i ≤ I.nA → j ≤ I.nB → ∀ q : ℤ, OrderedDPSpec I i j q := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro i j hij hi hj q
    by_cases hqneg : q < 0
    · have hqR : (q : ℝ) < 0 := by exact_mod_cast hqneg
      refine ⟨?_, ?_⟩
      · constructor
        · intro _
          rintro ⟨l, _, hl⟩
          have hn := prefixSumCB_nonneg I j l
          linarith
        · intro _
          exact dpF_negative I i j q hqneg
      · intro m hm
        rw [dpF_negative I i j q hqneg] at hm
        simp at hm
    · have hq : 0 ≤ q := by omega
      cases i with
      | zero =>
        exact ⟨dpF_B_only_eq_top_iff_infeasible I j hj q,
          dpF_B_only_finite_optimum I j hj q⟩
      | succ i =>
        cases j with
        | zero =>
          exact ⟨dpF_A_only_eq_top_iff_infeasible I (i + 1) hi q,
            dpF_A_only_finite_optimum I (i + 1) hi q⟩
        | succ j =>
          have hi' : i < I.nA := by omega
          have hj' : j < I.nB := by omega
          exact orderedDP_mixed_step I i j hi' hj' q hq
            (ih (i + (j + 1)) (by omega) i (j + 1) rfl (by omega) (by omega) q)
            (ih ((i + 1) + j) (by omega) (i + 1) j rfl (by omega) (by omega)
              (q - (I.bigPij (i + 1) (j + 1) : ℤ)))

lemma orderedDP_all (I : Instance) (i j : ℕ) (hi : i ≤ I.nA) (hj : j ≤ I.nB) (q : ℤ) :
    OrderedDPSpec I i j q :=
  orderedDP_all_aux I (i + j) i j rfl hi hj q

end TwoAgentSched.TotalTotal.PrefixProof

namespace TwoAgentSched.TotalTotal.PrefixProof

/-- Every schedule admits an agentwise index-ordered schedule that weakly improves both sums. -/
def SPTNormalization (I : Instance) : Prop :=
  ∀ l : List (Fin I.nA ⊕ Fin I.nB), IsSchedule Finset.univ l →
    ∃ σ : List (Fin I.nA ⊕ Fin I.nB),
      IsPrefixSequence I I.nA I.nB σ ∧ I.sumCA σ ≤ I.sumCA l ∧ I.sumCB σ ≤ I.sumCB l

/-- The full source statement follows from ordered-prefix correctness and SPT normalization. -/
lemma theorem_9_3_of_normalization (I : Instance) (hnorm : SPTNormalization I) (Q : ℕ) :
    (I.dpF I.nA I.nB Q = ⊤ ↔
      ¬ ∃ l, IsSchedule Finset.univ l ∧ I.sumCB l ≤ (Q : ℝ)) ∧
    ∀ m : ℕ, I.dpF I.nA I.nB Q = (m : ℕ∞) →
      (∃ l, IsSchedule Finset.univ l ∧ I.sumCB l ≤ (Q : ℝ) ∧ I.sumCA l = (m : ℝ)) ∧
      ∀ l, IsSchedule Finset.univ l → I.sumCB l ≤ (Q : ℝ) → (m : ℝ) ≤ I.sumCA l := by
  have hs := orderedDP_all I I.nA I.nB le_rfl le_rfl (Q : ℤ)
  constructor
  · constructor
    · intro htop
      rintro ⟨l, hl, hb⟩
      obtain ⟨σ, hσ, _, hB⟩ := hnorm l hl
      apply hs.1.mp htop
      refine ⟨σ, hσ, ?_⟩
      simpa using le_trans hB hb
    · intro hnone
      apply hs.1.mpr
      rintro ⟨σ, hσ, hb⟩
      apply hnone
      refine ⟨σ, prefixSequence_full_schedule I σ hσ, ?_⟩
      simpa using hb
  · intro m hm
    obtain ⟨⟨σ, hσ, hb, hc⟩, hbound⟩ := hs.2 m hm
    constructor
    · refine ⟨σ, prefixSequence_full_schedule I σ hσ, ?_, ?_⟩
      · simpa using hb
      · simpa using hc
    · intro l hl hb
      obtain ⟨σ, hσ, hA, hB⟩ := hnorm l hl
      have hb' : prefixSumCB I I.nB σ ≤ ((Q : ℤ) : ℝ) := by
        simpa using le_trans hB hb
      have hm' : (m : ℝ) ≤ I.sumCA σ := by
        simpa using hbound σ hσ hb'
      exact le_trans hm' hA

end TwoAgentSched.TotalTotal.PrefixProof



open TwoAgentSched.TotalTotal TwoAgentSched.TotalTotal.PrefixProof MooreLateJobs.Shared

theorem solution (I : Instance) (hA : Monotone I.pA) (hB : Monotone I.pB) (Q : ℕ) :
    (I.dpF I.nA I.nB Q = ⊤ ↔
      ¬ ∃ l, IsSchedule Finset.univ l ∧ I.sumCB l ≤ (Q : ℝ)) ∧
    ∀ m : ℕ, I.dpF I.nA I.nB Q = (m : ℕ∞) →
      (∃ l, IsSchedule Finset.univ l ∧ I.sumCB l ≤ (Q : ℝ) ∧ I.sumCA l = (m : ℝ)) ∧
      ∀ l, IsSchedule Finset.univ l → I.sumCB l ≤ (Q : ℝ) → (m : ℝ) ≤ I.sumCA l := by
  apply theorem_9_3_of_normalization I ?_ Q
  intro l hl
  obtain ⟨σ, hσ, hpair, hAσ, hBσ⟩ := spt_normalization I hA hB l hl
  refine ⟨σ, ⟨hσ.1, ?_, ?_⟩, hAσ, hBσ⟩
  · intro x
    simpa only [prefixJobs_full] using hσ.2 x
  · apply hpair.imp
    intro x y hxy
    cases x <;> cases y <;> simpa [prefixOrder] using hxy
