-- Prove2me | solution 1 for RevenueOrdered.Stackelberg.greedy_block_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T00:45:10.141627+00:00
-- url     : https://prove2.me/submissions/9c3eaad5-3fcf-415f-b010-e5948ef6fa33

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


theorem not_sublist_of_before {γ : Type*} (L l₁ l₂ : List γ) (x y : γ)
    (hsplit : L = l₁ ++ x :: l₂) (hnd : L.Nodup) (hy : y ∈ l₁) (hs : [x, y].Sublist L) :
    False := by
  have hP : L.Pairwise (fun a b => ¬ (a = x ∧ b ∈ l₁)) := by
    subst hsplit
    rw [List.nodup_append] at hnd
    rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · refine List.Pairwise.imp_of_mem ?_ hnd.1
      intro a b ha _ _ ⟨hax, _⟩
      subst hax
      exact hnd.2.2 a ha a List.mem_cons_self rfl
    · rw [List.pairwise_cons]
      refine ⟨?_, ?_⟩
      · intro b hb ⟨_, hb1⟩
        exact hnd.2.2 b hb1 b (List.mem_cons_of_mem _ hb) rfl
      · refine List.Pairwise.imp_of_mem ?_ (List.nodup_cons.mp hnd.2.1).2
        intro a b ha _ _ ⟨hax, _⟩
        subst hax
        exact (List.nodup_cons.mp hnd.2.1).1 ha
    · intro a ha b _ ⟨hax, _⟩
      subst hax
      exact hnd.2.2 a ha a List.mem_cons_self rfl
  exact hP.forall_sublist hs ⟨rfl, hy⟩

theorem sublist_or {γ : Type*} (L : List γ) (e f : γ) (he : e ∈ L) (hf : f ∈ L) (hef : e ≠ f) :
    [e, f].Sublist L ∨ [f, e].Sublist L := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem he
  rw [List.mem_append, List.mem_cons] at hf
  rcases hf with hf | rfl | hf
  · right
    have h1 : [f].Sublist s := List.singleton_sublist.mpr hf
    have h2 : [e].Sublist (e :: t) := List.singleton_sublist.mpr List.mem_cons_self
    exact h1.append h2
  · exact absurd rfl hef
  · left
    have h2 : [e, f].Sublist (e :: t) := (List.singleton_sublist.mpr hf).cons_cons e
    exact h2.trans (List.sublist_append_right s _)

/-- In a duplicate-free scan `l₁ ++ e :: l₂`, the set built from `l₁` is contained in the
final greedy set. -/
theorem greedy_prefix_subset (P : Finset β → Prop) (l₁ l₂ : List β) (e : β) (F : Finset β) :
    greedy P l₁ F ⊆ greedy P (l₁ ++ e :: l₂) F := by
  rw [greedy_append]
  exact foldl_mono P F _ _

end StackG0Aux

namespace StackG1Aux

open RevenueOrdered.Stackelberg StackG0Aux

variable {α : Type*}

theorem low_isBasis (M : Matroid α) (E : Finset α) (hE : (E : Set α) = M.E) (L : List α)
    (hL : IsLinearOrderOf L E) (blk : α → ℕ)
    (hagree : ∀ e ∈ E, ∀ f ∈ E, blk e < blk f → [e, f].Sublist L) (n : ℕ) :
    M.IsBasis (((greedyM M L E).filter (fun e => blk e < n) : Finset α) : Set α)
      ((E.filter (fun e => blk e < n) : Finset α) : Set α) := by
  have hG := greedyM_isBasis_of_subset M E hE L hL E le_rfl
  have hGE : greedyM M L E ⊆ E := by exact_mod_cast hG.subset
  refine (hG.indep.subset (by
    intro x hx; exact (Finset.mem_filter.mp hx).1)).isBasis_of_forall_insert ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter] at hx ⊢
    exact ⟨hGE hx.1, hx.2⟩
  · rintro x ⟨hxX, hxG⟩
    simp only [Finset.mem_coe, Finset.mem_filter] at hxX hxG
    have hxE := hxX.1
    have hxnG : x ∉ greedyM M L E := fun h => hxG ⟨h, hxX.2⟩
    have hxL : x ∈ L := by rw [← hL.2, List.mem_toFinset] at hxE; exact hxE
    obtain ⟨l₁, l₂, hsplit⟩ := List.append_of_mem hxL
    have hnd : (l₁ ++ x :: l₂).Nodup := hsplit ▸ hL.1
    unfold greedyM at hxnG
    rw [hsplit, mem_greedy_iff _ l₁ l₂ x E hnd] at hxnG
    have hdep : ¬ M.Indep ((insert x (greedy (fun X => M.Indep (X : Set α)) l₁ E) :
        Finset α) : Set α) := fun h => hxnG ⟨hxE, h⟩
    have hJsub : (greedy (fun X => M.Indep (X : Set α)) l₁ E) ⊆
        (greedyM M L E).filter (fun e => blk e < n) := by
      intro y hy
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · unfold greedyM; rw [hsplit]; exact greedy_prefix_subset _ l₁ l₂ x E hy
      · have hy' := Finset.mem_filter.mp (greedy_subset _ l₁ E hy)
        by_contra hlt
        have hxy : blk x < blk y := by have := hxX.2; omega
        exact not_sublist_of_before L l₁ l₂ x y hsplit hL.1 hy'.2
          (hagree x hxE y hy'.1 hxy)
    refine ⟨fun hi => hdep (hi.subset ?_), ?_⟩
    · rw [Finset.coe_insert]
      exact Set.insert_subset_insert (by exact_mod_cast hJsub)
    · refine Set.insert_subset ?_ ?_
      · rw [← hE]; exact_mod_cast hxE
      · intro z hz
        simp only [Finset.mem_coe, Finset.mem_filter] at hz
        rw [← hE]; exact_mod_cast hGE hz.1

theorem low_card_eq (M : Matroid α) (E : Finset α) (hE : (E : Set α) = M.E) (L L' : List α)
    (hL : IsLinearOrderOf L E) (hL' : IsLinearOrderOf L' E) (blk : α → ℕ)
    (hagree : ∀ e ∈ E, ∀ f ∈ E, blk e < blk f → [e, f].Sublist L ∧ [e, f].Sublist L') (n : ℕ) :
    ((greedyM M L E).filter (fun e => blk e < n)).card =
      ((greedyM M L' E).filter (fun e => blk e < n)).card := by
  have h1 := low_isBasis M E hE L hL blk (fun e he f hf h => (hagree e he f hf h).1) n
  have h2 := low_isBasis M E hE L' hL' blk (fun e he f hf h => (hagree e he f hf h).2) n
  have := h1.encard_eq_encard h2
  rw [Set.encard_coe_eq_coe_finsetCard, Set.encard_coe_eq_coe_finsetCard] at this
  exact_mod_cast this

theorem filter_split (G : Finset α) (blk : α → ℕ) (i : ℕ) :
    (G.filter (fun e => blk e < i + 1)).card =
      (G.filter (fun e => blk e = i)).card + (G.filter (fun e => blk e < i)).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_union]
    by_cases hx : x ∈ G
    · simp only [hx, true_and]; omega
    · simp [hx]
  · rw [Finset.disjoint_filter]
    intro x _ h1
    omega

end StackG1Aux

open RevenueOrdered.Stackelberg StackG1Aux in
theorem solution {α : Type*} (M : Matroid α) (E : Finset α)
    (hE : (E : Set α) = M.E) (L L' : List α) (hL : IsLinearOrderOf L E)
    (hL' : IsLinearOrderOf L' E) (blk : α → ℕ)
    (hagree : ∀ e ∈ E, ∀ f ∈ E, blk e < blk f → [e, f].Sublist L ∧ [e, f].Sublist L') :
    ∀ i : ℕ, ((greedyM M L E).filter (fun e => blk e = i)).card =
      ((greedyM M L' E).filter (fun e => blk e = i)).card := by
  intro i
  have h1 := filter_split (greedyM M L E) blk i
  have h2 := filter_split (greedyM M L' E) blk i
  have h3 := low_card_eq M E hE L L' hL hL' blk hagree (i + 1)
  have h4 := low_card_eq M E hE L L' hL hL' blk hagree i
  omega
