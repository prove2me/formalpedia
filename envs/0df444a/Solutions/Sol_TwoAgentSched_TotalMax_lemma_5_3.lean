-- Prove2me | solution 1 for TwoAgentSched.TotalMax.lemma_5_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:59:12.403279+00:00
-- url     : https://prove2.me/submissions/d6c7fd77-3839-4489-9f79-f18564ecbcf7

import Mathlib
import Definitions.Def_TwoAgentSched_TotalMax_Model

set_option autoImplicit false
open TwoAgentSched.TotalMax TwoAgentSched.MaxMax MooreLateJobs.Shared

section generic
variable {ι : Type*} [DecidableEq ι] (p : ι → ℝ)

lemma ttm_ca_append_left (l₁ l₂ : List ι) (m : ℕ) (hm : m < l₁.length) :
    completionAt p (l₁ ++ l₂) m = completionAt p l₁ m := by
  unfold completionAt
  rw [List.take_append_of_le_length (by omega)]

lemma ttm_ct_append_left (l₁ l₂ : List ι) (x : ι) (hx : x ∈ l₁) :
    completionTime p (l₁ ++ l₂) x = completionTime p l₁ x := by
  unfold completionTime
  rw [List.idxOf_append_of_mem hx]
  exact ttm_ca_append_left p l₁ l₂ _ (List.idxOf_lt_length_iff.mpr hx)

lemma ttm_ct_last (l : List ι) (z : ι) (hz : z ∉ l) :
    completionTime p (l ++ [z]) z = ((l ++ [z]).map p).sum := by
  unfold completionTime completionAt
  have h1 : (l ++ [z]).idxOf z = l.length := by
    rw [List.idxOf_append_of_notMem hz]; simp
  rw [h1]
  have h2 : (l ++ [z]).take (l.length + 1) = l ++ [z] := List.take_of_length_le (by simp)
  rw [h2]

lemma ttm_ct_erase_le (hp : ∀ j, 0 ≤ p j) (l : List ι) (hnd : l.Nodup) (z x : ι)
    (hz : z ∈ l) (hx : x ∈ l) (hxz : x ≠ z) :
    completionTime p (l.erase z) x ≤ completionTime p l x := by
  obtain ⟨a, b, rfl⟩ := List.append_of_mem hz
  have hza : z ∉ a := fun h => (List.nodup_append.1 hnd).2.2 z h z (by simp) rfl
  have herase : (a ++ z :: b).erase z = a ++ b := by
    rw [List.erase_append_right _ hza]; simp
  rw [herase]
  have hx' : x ∈ a ∨ x ∈ b := by
    rcases List.mem_append.1 hx with h | h
    · exact Or.inl h
    · rcases List.mem_cons.1 h with h | h
      · exact absurd h hxz
      · exact Or.inr h
  rcases hx' with hxa | hxb
  · rw [ttm_ct_append_left p a b x hxa, ttm_ct_append_left p a (z :: b) x hxa]
  · have hxa : x ∉ a := fun h => (List.nodup_append.1 hnd).2.2 x h x (by simp [hxb]) rfl
    unfold completionTime completionAt
    rw [List.idxOf_append_of_notMem hxa, List.idxOf_append_of_notMem hxa,
      List.idxOf_cons_ne _ (Ne.symm hxz)]
    rw [List.take_append, List.take_append]
    have e1 : a.take (a.length + List.idxOf x b + 1) = a := List.take_of_length_le (by omega)
    have e2 : a.take (a.length + (List.idxOf x b).succ + 1) = a :=
      List.take_of_length_le (by omega)
    rw [e1, e2]
    have e3 : a.length + List.idxOf x b + 1 - a.length = List.idxOf x b + 1 := by omega
    have e4 : a.length + (List.idxOf x b).succ + 1 - a.length = List.idxOf x b + 1 + 1 := by omega
    rw [e3, e4]
    simp only [List.take_succ_cons, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    linarith [hp z]

end generic

local instance (priority := high) ttmBEq {nA nB : ℕ} : BEq (Job nA nB) := instBEqOfDecidableEq

namespace TTM53
variable {nA nB : ℕ} (p : Job nA nB → ℝ)

lemma sum_all (l : List (Job nA nB)) (hl : IsSchedule Finset.univ l) :
    (l.map p).sum = ∑ h : Fin nA, p (Sum.inl h) + ∑ k : Fin nB, p (Sum.inr k) := by
  rw [← Fintype.sum_sum_type (fun j : Job nA nB => p j)]
  have hnd : l.Nodup := hl.1
  have : l.toFinset = Finset.univ := by
    ext x; simp [(hl.2 x).2 (Finset.mem_univ x)]
  rw [← List.sum_toFinset p hnd, this]

/-- moving a job to the end -/
lemma move_last (l : List (Job nA nB)) (hl : IsSchedule Finset.univ l) (z : Job nA nB) :
    IsSchedule Finset.univ (l.erase z ++ [z]) := by
  have hz : z ∈ l := (hl.2 z).2 (Finset.mem_univ z)
  have hperm : l.Perm (l.erase z ++ [z]) :=
    (List.perm_cons_erase hz).trans (List.perm_append_singleton z _).symm
  exact ⟨hperm.nodup_iff.1 hl.1, fun x => by
    rw [← hperm.mem_iff]; exact hl.2 x⟩

lemma ct_le (hp : ∀ j, 0 ≤ p j) (l : List (Job nA nB)) (hl : IsSchedule Finset.univ l)
    (kbar : Fin nB) (x : Job nA nB) (hx : x ≠ Sum.inr kbar) :
    completionTime p (l.erase (Sum.inr kbar) ++ [Sum.inr kbar]) x ≤ completionTime p l x := by
  have hz : (Sum.inr kbar : Job nA nB) ∈ l := (hl.2 _).2 (Finset.mem_univ _)
  have hxm : x ∈ l.erase (Sum.inr kbar) := by
    rw [hl.1.mem_erase_iff]; exact ⟨hx, (hl.2 _).2 (Finset.mem_univ _)⟩
  rw [ttm_ct_append_left p _ _ _ hxm]
  exact ttm_ct_erase_le p hp l hl.1 _ _ hz ((hl.2 _).2 (Finset.mem_univ _)) hx

lemma total_le (hp : ∀ j, 0 ≤ p j) (l : List (Job nA nB)) (hl : IsSchedule Finset.univ l)
    (kbar : Fin nB) :
    totalCompletionA p (l.erase (Sum.inr kbar) ++ [Sum.inr kbar]) ≤ totalCompletionA p l := by
  unfold totalCompletionA
  exact Finset.sum_le_sum (fun h _ => ct_le p hp l hl kbar _ (by simp))

lemma feas_move (hp : ∀ j, 0 ≤ p j) (fB : Fin nB → ℝ → ℝ) (hfB : ∀ k, Monotone (fB k)) (Q : ℝ)
    (l : List (Job nA nB)) (hl : IsFeasible p fB Q l) (kbar : Fin nB)
    (hkbar : fB kbar (∑ h : Fin nA, p (Sum.inl h) + ∑ k : Fin nB, p (Sum.inr k)) ≤ Q) :
    IsFeasible p fB Q (l.erase (Sum.inr kbar) ++ [Sum.inr kbar]) := by
  obtain ⟨hs, hB⟩ := hl
  have hs' := move_last l hs (Sum.inr kbar)
  refine ⟨hs', fun k => ?_⟩
  by_cases hk : k = kbar
  · subst hk
    have hnot : (Sum.inr k : Job nA nB) ∉ l.erase (Sum.inr k) := fun h =>
      (List.Nodup.not_mem_erase hs.1) h
    rw [ttm_ct_last p _ _ hnot, sum_all p _ hs']
    exact hkbar
  · exact (hfB k (ct_le p hp l hs kbar _ (by simpa using hk))).trans (hB k)

lemma total_lt (hp : ∀ j, 0 < p j) (L : List (Job nA nB)) (h0 : Fin nA)
    (hl : IsSchedule Finset.univ (L ++ [Sum.inl h0])) (kbar : Fin nB) :
    totalCompletionA p ((L ++ [Sum.inl h0]).erase (Sum.inr kbar) ++ [Sum.inr kbar]) <
      totalCompletionA p (L ++ [Sum.inl h0]) := by
  have hp0 : ∀ j, 0 ≤ p j := fun j => (hp j).le
  have hznd := hl.1
  have hzL : (Sum.inr kbar : Job nA nB) ∈ L := by
    have : (Sum.inr kbar : Job nA nB) ∈ L ++ [Sum.inl h0] := (hl.2 _).2 (Finset.mem_univ _)
    rcases List.mem_append.1 this with h | h
    · exact h
    · simp at h
  have hh0L : (Sum.inl h0 : Job nA nB) ∉ L := fun h =>
    (List.nodup_append.1 hznd).2.2 _ h _ (by simp) rfl
  have hndL : L.Nodup := (List.nodup_append.1 hznd).1
  unfold totalCompletionA
  apply Finset.sum_lt_sum
  · intro h _; exact ct_le p hp0 _ hl kbar _ (by simp)
  · refine ⟨h0, Finset.mem_univ _, ?_⟩
    have herase : (L ++ [Sum.inl h0]).erase (Sum.inr kbar) = L.erase (Sum.inr kbar) ++ [Sum.inl h0] :=
      List.erase_append_left _ hzL
    have hmem : (Sum.inl h0 : Job nA nB) ∈ L.erase (Sum.inr kbar) ++ [Sum.inl h0] := by simp
    have hnot : (Sum.inl h0 : Job nA nB) ∉ L.erase (Sum.inr kbar) := fun h =>
      hh0L (List.mem_of_mem_erase h)
    rw [herase, ttm_ct_append_left p _ _ _ hmem, ttm_ct_last p _ _ hnot,
      ttm_ct_last p _ _ hh0L]
    have hperm := (List.perm_cons_erase hzL).map p
    have hsum := hperm.sum_eq
    simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons, List.map_nil,
      List.sum_nil] at hsum ⊢
    have := hp (Sum.inr kbar)
    linarith

end TTM53

open TTM53 in
theorem solution {nA nB : ℕ} (p : Job nA nB → ℝ) (hp : ∀ j, 0 < p j)
    (fB : Fin nB → ℝ → ℝ) (hfB : ∀ k, Monotone (fB k)) (Q : ℝ)
    (hfeas : IsFeasibleInstance p fB Q) (kbar : Fin nB)
    (hkbar : fB kbar (∑ h : Fin nA, p (Sum.inl h) + ∑ k : Fin nB, p (Sum.inr k)) ≤ Q) :
    (∃ l : List (Job nA nB), IsOptimal p fB Q l ∧ l.getLast? = some (Sum.inr kbar)) ∧
      ∀ l : List (Job nA nB), IsOptimal p fB Q l →
        ∀ h : Fin nA, l.getLast? ≠ some (Sum.inl h) := by
  have hp0 : ∀ j, 0 ≤ p j := fun j => (hp j).le
  -- an optimal schedule exists
  have hexopt : ∃ l, IsOptimal p fB Q l := by
    classical
    obtain ⟨l1, hl1⟩ := hfeas
    have hfin : {l : List (Job nA nB) | IsFeasible p fB Q l}.Finite := by
      refine (List.finite_length_le (Job nA nB) (Fintype.card (Job nA nB))).subset ?_
      intro l hl
      exact hl.1.1.length_le_card
    obtain ⟨l0, hl0, hmin⟩ := Set.exists_min_image _ (fun l => totalCompletionA p l) hfin ⟨l1, hl1⟩
    exact ⟨l0, hl0, fun l' hl' => hmin l' hl'⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨l0, hl0⟩ := hexopt
    refine ⟨l0.erase (Sum.inr kbar) ++ [Sum.inr kbar],
      ⟨feas_move p hp0 fB hfB Q l0 hl0.1 kbar hkbar, fun l' hl' => ?_⟩, by simp⟩
    exact (total_le p hp0 l0 hl0.1.1 kbar).trans (hl0.2 l' hl')
  · intro l hl h hlast
    obtain ⟨L, rfl⟩ := List.getLast?_eq_some_iff.1 hlast
    have hlt := total_lt p hp L h hl.1.1 kbar
    have hfeas' := feas_move p hp0 fB hfB Q _ hl.1 kbar hkbar
    have := hl.2 _ hfeas'
    linarith
