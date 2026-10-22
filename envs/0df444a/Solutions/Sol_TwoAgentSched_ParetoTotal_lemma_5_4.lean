-- Prove2me | solution 1 for TwoAgentSched.ParetoTotal.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:05:42.700201+00:00
-- url     : https://prove2.me/submissions/9481a936-2734-4bb0-a416-a57a05dbc34d

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

lemma ttm_ct_append_right (l₁ l₂ : List ι) (x : ι) (hx : x ∉ l₁) :
    completionTime p (l₁ ++ l₂) x = (l₁.map p).sum + completionTime p l₂ x := by
  unfold completionTime completionAt
  rw [List.idxOf_append_of_notMem hx, List.take_append]
  have e1 : l₁.take (l₁.length + l₂.idxOf x + 1) = l₁ := List.take_of_length_le (by omega)
  have e3 : l₁.length + l₂.idxOf x + 1 - l₁.length = l₂.idxOf x + 1 := by omega
  rw [e1, e3]
  simp

lemma ttm_ct_cons_ne (y : ι) (R : List ι) (x : ι) (hx : x ≠ y) :
    completionTime p (y :: R) x = p y + completionTime p R x := by
  unfold completionTime completionAt
  rw [List.idxOf_cons_ne _ (Ne.symm hx)]
  simp [List.take_succ_cons]

lemma ttm_ct_cons_self (y : ι) (R : List ι) :
    completionTime p (y :: R) y = p y := by
  unfold completionTime completionAt
  simp

end generic

local instance (priority := high) ttmBEq {nA nB : ℕ} : BEq (Job nA nB) := instBEqOfDecidableEq

namespace TTM54
variable {nA nB : ℕ} (p : Job nA nB → ℝ)

lemma sum_all (l : List (Job nA nB)) (hl : IsSchedule Finset.univ l) :
    (l.map p).sum = ∑ h : Fin nA, p (Sum.inl h) + ∑ k : Fin nB, p (Sum.inr k) := by
  rw [← Fintype.sum_sum_type (fun j : Job nA nB => p j)]
  have hnd : l.Nodup := hl.1
  have : l.toFinset = Finset.univ := by
    ext x; simp [(hl.2 x).2 (Finset.mem_univ x)]
  rw [← List.sum_toFinset p hnd, this]

end TTM54

namespace TTM54
variable {nA nB : ℕ} (p : Job nA nB → ℝ)

lemma swap_better (hp : ∀ j, 0 < p j) (fB : Fin nB → ℝ → ℝ) (hfB : ∀ k, Monotone (fB k)) (Q : ℝ)
    (L : List (Job nA nB)) (h h' : Fin nA) (hlt : p (Sum.inl h) < p (Sum.inl h'))
    (hl : IsFeasible p fB Q (L ++ [Sum.inl h])) :
    ∃ l', IsFeasible p fB Q l' ∧
      totalCompletionA p l' < totalCompletionA p (L ++ [Sum.inl h]) := by
  obtain ⟨hs, hB⟩ := hl
  set a : Job nA nB := Sum.inl h' with ha
  set b : Job nA nB := Sum.inl h with hb
  have hab : a ≠ b := by
    intro e
    have : h' = h := by simpa [ha, hb] using e
    exact absurd hlt (by rw [ha, hb, this]; exact lt_irrefl _)
  have haL : a ∈ L := by
    have : a ∈ L ++ [b] := (hs.2 a).2 (Finset.mem_univ _)
    rcases List.mem_append.1 this with h1 | h1
    · exact h1
    · exact absurd (List.mem_singleton.1 h1) hab
  obtain ⟨L1, L2, rfl⟩ := List.append_of_mem haL
  have hnd := hs.1
  simp only [List.append_assoc, List.cons_append] at hnd
  obtain ⟨hn1, hn2, hdisj⟩ := List.nodup_append.1 hnd
  obtain ⟨ha_notin, hnd2⟩ := List.nodup_cons.1 hn2
  obtain ⟨hn3, hn4, hdisj2⟩ := List.nodup_append.1 hnd2
  have haL1 : a ∉ L1 := fun hx => hdisj a hx a (by simp) rfl
  have hbL1 : b ∉ L1 := fun hx => hdisj b hx b (by simp) rfl
  have haL2 : a ∉ L2 := fun hx => ha_notin (List.mem_append_left _ hx)
  have hbL2 : b ∉ L2 := fun hx => hdisj2 b hx b (by simp) rfl
  have hL12 : ∀ x ∈ L2, x ∉ L1 := fun x hx hx1 => hdisj x hx1 x (by simp [hx]) rfl
  set l' : List (Job nA nB) := L1 ++ (b :: (L2 ++ [a])) with hl'
  set l : List (Job nA nB) := (L1 ++ a :: L2) ++ [b] with hl
  have hl_eq : l = L1 ++ (a :: (L2 ++ [b])) := by simp [hl]
  have hperm : l.Perm l' := by
    rw [hl_eq]
    refine List.Perm.append_left L1 ?_
    exact ((List.Perm.cons a (List.perm_append_singleton b L2)).trans
      (List.Perm.swap b a L2)).trans (List.Perm.cons b (List.perm_append_singleton a L2).symm)
  have hs' : IsSchedule Finset.univ l' :=
    ⟨hperm.nodup_iff.1 hs.1, fun x => by rw [← hperm.mem_iff]; exact hs.2 x⟩
  have hl_sched : IsSchedule Finset.univ l := hs
  set S1 := (L1.map p).sum with hS1
  have hτ : (l.map p).sum = (l'.map p).sum := (hperm.map p).sum_eq
  -- completion times
  have c1 : ∀ x ∈ L1, completionTime p l' x = completionTime p l x := by
    intro x hx
    rw [hl_eq, hl', ttm_ct_append_left p _ _ x hx, ttm_ct_append_left p _ _ x hx]
  have c2 : ∀ x ∈ L2, completionTime p l' x = completionTime p l x - (p a - p b) := by
    intro x hx
    have hxa : x ≠ a := fun e => haL2 (e ▸ hx)
    have hxb : x ≠ b := fun e => hbL2 (e ▸ hx)
    rw [hl_eq, hl', ttm_ct_append_right p _ _ x (hL12 x hx), ttm_ct_append_right p _ _ x (hL12 x hx),
      ttm_ct_cons_ne p _ _ x hxa, ttm_ct_cons_ne p _ _ x hxb,
      ttm_ct_append_left p _ _ x hx, ttm_ct_append_left p _ _ x hx]
    ring
  have c3a : completionTime p l a = S1 + p a := by
    rw [hl_eq, ttm_ct_append_right p _ _ a haL1, ttm_ct_cons_self]
  have c3b : completionTime p l' b = S1 + p b := by
    rw [hl', ttm_ct_append_right p _ _ b hbL1, ttm_ct_cons_self]
  have hbnot : b ∉ (L1 ++ a :: L2) := by
    intro hx
    rcases List.mem_append.1 hx with h1 | h1
    · exact hbL1 h1
    · rcases List.mem_cons.1 h1 with h2 | h2
      · exact hab h2.symm
      · exact hbL2 h2
  have hanot : a ∉ (L1 ++ b :: L2) := by
    intro hx
    rcases List.mem_append.1 hx with h1 | h1
    · exact haL1 h1
    · rcases List.mem_cons.1 h1 with h2 | h2
      · exact hab h2
      · exact haL2 h2
  have c4b : completionTime p l b = (l.map p).sum := by
    rw [hl]; exact ttm_ct_last p _ b hbnot
  have c4a : completionTime p l' a = (l'.map p).sum := by
    have : l' = (L1 ++ b :: L2) ++ [a] := by simp [hl']
    rw [this]; exact ttm_ct_last p _ a hanot
  -- every job other than a, b is in L1 or L2
  have hcls : ∀ x : Job nA nB, x ≠ a → x ≠ b → x ∈ L1 ∨ x ∈ L2 := by
    intro x hxa hxb
    have : x ∈ l := (hs.2 x).2 (Finset.mem_univ _)
    rw [hl] at this
    simp only [List.mem_append, List.mem_cons, List.mem_singleton] at this
    tauto
  refine ⟨l', ⟨hs', fun k => ?_⟩, ?_⟩
  · have hxa : (Sum.inr k : Job nA nB) ≠ a := by simp [ha]
    have hxb : (Sum.inr k : Job nA nB) ≠ b := by simp [hb]
    have hB' := hB k
    rcases hcls _ hxa hxb with h1 | h1
    · rw [c1 _ h1]; exact hB'
    · rw [c2 _ h1]
      refine le_trans (hfB k ?_) hB'
      have := hlt
      linarith
  · unfold totalCompletionA
    have hG1 : ∀ h'' : Fin nA, h'' ≠ h → h'' ≠ h' →
        completionTime p l' (Sum.inl h'') - completionTime p l (Sum.inl h'') ≤ 0 := by
      intro h'' h1 h2
      have hxa : (Sum.inl h'' : Job nA nB) ≠ a := by simp [ha, h2]
      have hxb : (Sum.inl h'' : Job nA nB) ≠ b := by simp [hb, h1]
      rcases hcls _ hxa hxb with h3 | h3
      · rw [c1 _ h3]; simp
      · rw [c2 _ h3]; linarith
    have hpair : ∑ x ∈ ({h, h'} : Finset (Fin nA)),
        -(completionTime p l' (Sum.inl x) - completionTime p l (Sum.inl x)) = p a - p b := by
      have hne : h ≠ h' := fun e => hab (by rw [ha, hb, e])
      rw [Finset.sum_pair hne]
      have e1 : completionTime p l' (Sum.inl h') = (l'.map p).sum := c4a
      have e2 : completionTime p l (Sum.inl h) = (l.map p).sum := c4b
      have e3 : completionTime p l (Sum.inl h') = S1 + p a := c3a
      have e4 : completionTime p l' (Sum.inl h) = S1 + p b := c3b
      rw [e1, e2, e3, e4, ← hτ]
      ring
    have hsub : ({h, h'} : Finset (Fin nA)) ⊆ Finset.univ := Finset.subset_univ _
    have hle := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun x => -(completionTime p l' (Sum.inl x) - completionTime p l (Sum.inl x))) hsub
      (by
        intro x _ hx
        have h1 : x ≠ h := fun e => hx (by simp [e])
        have h2 : x ≠ h' := fun e => hx (by simp [e])
        have := hG1 x h1 h2
        linarith)
    rw [hpair] at hle
    rw [Finset.sum_neg_distrib, Finset.sum_sub_distrib] at hle
    have hpos : 0 < p a - p b := by rw [ha, hb]; linarith
    linarith

end TTM54

open TTM54 in
theorem solution {nA nB : ℕ} (hA : 0 < nA) (p : Job nA nB → ℝ) (hp : ∀ j, 0 < p j)
    (fB : Fin nB → ℝ → ℝ) (hfB : ∀ k, Monotone (fB k)) (Q : ℝ)
    (hfeas : IsFeasibleInstance p fB Q)
    (hall : ∀ k : Fin nB,
      Q < fB k (∑ h : Fin nA, p (Sum.inl h) + ∑ k : Fin nB, p (Sum.inr k))) :
    ∀ l : List (Job nA nB), IsOptimal p fB Q l →
      ∃ h : Fin nA, l.getLast? = some (Sum.inl h) ∧
        ∀ h' : Fin nA, p (Sum.inl h') ≤ p (Sum.inl h) := by
  intro l hl
  have hne : l ≠ [] := by
    intro h0
    have := (hl.1.1.2 (Sum.inl ⟨0, hA⟩)).2 (Finset.mem_univ _)
    rw [h0] at this; simp at this
  obtain ⟨L, x, hLx⟩ := (List.eq_nil_or_concat l).resolve_left hne
  rw [List.concat_eq_append] at hLx
  subst hLx
  rcases x with h | k
  · refine ⟨h, by simp, fun h' => ?_⟩
    by_contra hcon
    have hlt : p (Sum.inl h) < p (Sum.inl h') := not_le.1 hcon
    obtain ⟨l', hl'f, hl'lt⟩ := swap_better p hp fB hfB Q L h h' hlt hl.1
    have := hl.2 l' hl'f
    linarith
  · exfalso
    have hnot : (Sum.inr k : Job nA nB) ∉ L := fun hx =>
      (List.nodup_append.1 hl.1.1.1).2.2 _ hx _ (by simp) rfl
    have := hl.1.2 k
    rw [ttm_ct_last p L _ hnot, sum_all p _ hl.1.1] at this
    exact absurd this (not_le.2 (hall k))
