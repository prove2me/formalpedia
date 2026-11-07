-- Prove2me | solution 1 for RevenueOrdered.Stackelberg.greedy_card_mono_inter_subset
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T00:43:11.170203+00:00
-- url     : https://prove2.me/submissions/10381601-32a3-4b70-9ab2-4416c2e8ab6d

import Mathlib
import Definitions.Def_RevenueOrdered_Stackelberg_Greedy

open Classical

namespace StackG0Aux

open RevenueOrdered.Stackelberg

variable {β : Type*}

/-- One step of the greedy scan. -/
noncomputable def gstep (P : Finset β → Prop) (F : Finset β) (I : Finset β) (e : β) : Finset β :=
  if e ∈ F ∧ P (insert e I) then insert e I else I

theorem greedy_eq_foldl (P : Finset β → Prop) (l : List β) (F : Finset β) :
    greedy P l F = l.foldl (gstep P F) ∅ := rfl

theorem foldl_mono (P : Finset β → Prop) (F : Finset β) (l : List β) (I : Finset β) :
    I ⊆ l.foldl (gstep P F) I := by
  induction l generalizing I with
  | nil => exact le_rfl
  | cons a l ih =>
    simp only [List.foldl_cons]
    refine le_trans ?_ (ih _)
    unfold gstep
    split_ifs
    · exact Finset.subset_insert _ _
    · exact le_rfl

theorem foldl_subset (P : Finset β → Prop) (F : Finset β) (l : List β) (I : Finset β) :
    l.foldl (gstep P F) I ⊆ I ∪ (F.filter (fun x => x ∈ l)) := by
  induction l generalizing I with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons]
    refine (ih _).trans ?_
    intro x hx
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx
    · unfold gstep at hx
      split_ifs at hx with h
      · rcases Finset.mem_insert.mp hx with rfl | hx
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨h.1, List.mem_cons_self⟩)
        · exact Finset.mem_union_left _ hx
      · exact Finset.mem_union_left _ hx
    · rw [Finset.mem_filter] at hx
      exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hx.1, List.mem_cons_of_mem _ hx.2⟩)

theorem greedy_subset (P : Finset β → Prop) (l : List β) (F : Finset β) :
    greedy P l F ⊆ F.filter (fun x => x ∈ l) := by
  have := foldl_subset P F l ∅
  rw [greedy_eq_foldl]
  simpa using this

theorem greedy_append (P : Finset β → Prop) (l₁ l₂ : List β) (F : Finset β) :
    greedy P (l₁ ++ l₂) F = l₂.foldl (gstep P F) (greedy P l₁ F) := by
  rw [greedy_eq_foldl, greedy_eq_foldl, List.foldl_append]

theorem greedy_concat (P : Finset β → Prop) (l : List β) (e : β) (F : Finset β) :
    greedy P (l ++ [e]) F = gstep P F (greedy P l F) e := by
  rw [greedy_append]; rfl

/-- Membership characterization: in a duplicate-free scan `l₁ ++ e :: l₂`, `e` is picked iff it
is in `F` and can be added to the set built from `l₁`. -/
theorem mem_greedy_iff (P : Finset β → Prop) (l₁ l₂ : List β) (e : β) (F : Finset β)
    (hnd : (l₁ ++ e :: l₂).Nodup) :
    e ∈ greedy P (l₁ ++ e :: l₂) F ↔ e ∈ F ∧ P (insert e (greedy P l₁ F)) := by
  rw [greedy_append]
  simp only [List.foldl_cons]
  constructor
  · intro h
    by_contra hc
    have hs : gstep P F (greedy P l₁ F) e = greedy P l₁ F := by
      unfold gstep; rw [if_neg hc]
    rw [hs] at h
    have h2 := foldl_subset P F l₂ (greedy P l₁ F) h
    rw [Finset.mem_union] at h2
    rcases h2 with h2 | h2
    · have := (Finset.mem_filter.mp (greedy_subset P l₁ F h2)).2
      rw [List.nodup_append] at hnd
      exact hnd.2.2 e this e List.mem_cons_self rfl
    · have := (Finset.mem_filter.mp h2).2
      rw [List.nodup_append] at hnd
      exact (List.nodup_cons.mp hnd.2.1).1 this
  · intro h
    apply foldl_mono
    unfold gstep
    rw [if_pos h]
    exact Finset.mem_insert_self _ _

variable {α : Type*}

/-- Basis invariant: the greedy output on `F` along `l` is a basis of the elements of `F`
scanned by `l`. -/
theorem greedyM_isBasis (M : Matroid α) (l : List α) (F : Finset α) (hF : (F : Set α) ⊆ M.E) :
    M.IsBasis (greedyM M l F : Set α) ((F.filter (fun x => x ∈ l) : Finset α) : Set α) := by
  induction l using List.reverseRecOn with
  | nil =>
    simp only [greedyM, greedy, List.foldl_nil, Finset.coe_empty]
    have : (F.filter (fun x => x ∈ ([] : List α))) = ∅ := by simp
    rw [this, Finset.coe_empty]
    exact M.empty_indep.isBasis_self
  | append_singleton l e ih =>
    unfold greedyM at ih ⊢
    rw [greedy_concat]
    set G := greedy (fun X => M.Indep (X : Set α)) l F
    have hfil : F.filter (fun x => x ∈ l ++ [e]) =
        if e ∈ F then insert e (F.filter (fun x => x ∈ l)) else F.filter (fun x => x ∈ l) := by
      ext x
      split_ifs with he
      · simp only [Finset.mem_filter, List.mem_append, List.mem_singleton, Finset.mem_insert]
        constructor
        · rintro ⟨hx, hx' | rfl⟩
          · exact Or.inr ⟨hx, hx'⟩
          · exact Or.inl rfl
        · rintro (rfl | ⟨hx, hx'⟩)
          · exact ⟨he, Or.inr rfl⟩
          · exact ⟨hx, Or.inl hx'⟩
      · simp only [Finset.mem_filter, List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨hx, hx' | rfl⟩
          · exact ⟨hx, hx'⟩
          · exact absurd hx he
        · rintro ⟨hx, hx'⟩
          exact ⟨hx, Or.inl hx'⟩
    rw [hfil]
    unfold gstep
    by_cases h : e ∈ F ∧ M.Indep ((insert e G : Finset α) : Set α)
    · rw [if_pos h, if_pos h.1, Finset.coe_insert, Finset.coe_insert]
      rw [Finset.coe_insert] at h
      exact ih.insert_isBasis_insert h.2
    · rw [if_neg h]
      split_ifs with he
      · rw [Finset.coe_insert]
        refine ih.indep.isBasis_of_forall_insert
          (ih.subset.trans (Set.subset_insert _ _)) ?_
        rintro x ⟨hx, hxG⟩
        rcases (Set.mem_insert_iff.mp hx) with rfl | hx
        · refine ⟨?_, ?_⟩
          · intro hi
            exact h ⟨he, by rw [Finset.coe_insert]; exact hi⟩
          · exact Set.insert_subset (hF he) ih.indep.subset_ground
        · exact ih.insert_dep ⟨hx, hxG⟩
      · exact ih

theorem greedyM_isBasis_of_subset (M : Matroid α) (E : Finset α) (hE : (E : Set α) = M.E)
    (L : List α) (hL : IsLinearOrderOf L E) (F : Finset α) (hFE : F ⊆ E) :
    M.IsBasis (greedyM M L F : Set α) (F : Set α) := by
  have h := greedyM_isBasis M L F (by rw [← hE]; exact_mod_cast hFE)
  have : F.filter (fun x => x ∈ L) = F := by
    apply Finset.filter_true_of_mem
    intro x hx
    have := hFE hx
    rw [← hL.2, List.mem_toFinset] at this
    exact this
  rwa [this] at h

end StackG0Aux

open RevenueOrdered.Stackelberg StackG0Aux in
theorem solution {α : Type*} (M : Matroid α) (E : Finset α)
    (hE : (E : Set α) = M.E) (L : List α) (hL : IsLinearOrderOf L E)
    (F F' : Finset α) (hFF' : F ⊆ F') (hF'E : F' ⊆ E) :
    (greedyM M L F).card ≤ (greedyM M L F').card ∧
      F ∩ greedyM M L F' ⊆ greedyM M L F := by
  have hB := greedyM_isBasis_of_subset M E hE L hL F (hFF'.trans hF'E)
  have hB' := greedyM_isBasis_of_subset M E hE L hL F' hF'E
  constructor
  · have h1 : ((greedyM M L F : Finset α) : Set α).encard ≤
        ((greedyM M L F' : Finset α) : Set α).encard := by
      rw [← hB'.eRk_eq_encard]
      exact hB.indep.encard_le_eRk_of_subset (hB.subset.trans (by exact_mod_cast hFF'))
    rw [Set.encard_coe_eq_coe_finsetCard, Set.encard_coe_eq_coe_finsetCard] at h1
    exact_mod_cast h1
  · intro e he
    rw [Finset.mem_inter] at he
    obtain ⟨heF, heG'⟩ := he
    have heL : e ∈ L := by
      have := hF'E (hFF' heF)
      rw [← hL.2, List.mem_toFinset] at this
      exact this
    obtain ⟨l₁, l₂, hsplit⟩ := List.append_of_mem heL
    have hnd : (l₁ ++ e :: l₂).Nodup := hsplit ▸ hL.1
    unfold greedyM at heG' ⊢
    rw [hsplit] at heG' ⊢
    rw [mem_greedy_iff _ l₁ l₂ e F' hnd] at heG'
    rw [mem_greedy_iff _ l₁ l₂ e F hnd]
    refine ⟨heF, ?_⟩
    have hEl1 : ∀ X : Finset α, X ⊆ E → (X : Set α) ⊆ M.E := fun X hX => by
      rw [← hE]; exact_mod_cast hX
    have hJ' := greedyM_isBasis M l₁ F' (hEl1 F' hF'E)
    have hJ := greedyM_isBasis M l₁ F (hEl1 F (hFF'.trans hF'E))
    unfold greedyM at hJ hJ'
    set J := greedy (fun X => M.Indep (X : Set α)) l₁ F
    set J' := greedy (fun X => M.Indep (X : Set α)) l₁ F'
    have heJ' : e ∉ (J' : Set α) := by
      intro h
      have := (Finset.mem_filter.mp (greedy_subset _ l₁ F' h)).2
      rw [List.nodup_append] at hnd
      exact hnd.2.2 e this e List.mem_cons_self rfl
    have hncl : e ∉ M.closure (J' : Set α) := by
      have h2 := heG'.2
      rw [Finset.coe_insert, hJ'.indep.insert_indep_iff_of_notMem heJ'] at h2
      exact h2.2
    have hsub : (J : Set α) ⊆ M.closure (J' : Set α) := by
      refine hJ.subset.trans ?_
      refine subset_trans ?_ hJ'.subset_closure
      intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx ⊢
      exact ⟨hFF' hx.1, hx.2⟩
    have hncl' : e ∉ M.closure (J : Set α) := fun h =>
      hncl (M.closure_subset_closure_of_subset_closure hsub h)
    rw [Finset.coe_insert]
    have heJ : e ∉ (J : Set α) := fun h => hncl' (M.subset_closure _ hJ.indep.subset_ground h)
    rw [hJ.indep.insert_indep_iff_of_notMem heJ]
    exact ⟨hEl1 F (hFF'.trans hF'E) heF, hncl'⟩
