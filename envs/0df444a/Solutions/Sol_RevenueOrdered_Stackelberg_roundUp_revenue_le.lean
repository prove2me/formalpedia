-- Prove2me | solution 1 for RevenueOrdered.Stackelberg.roundUp_revenue_le
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T00:52:57.08187+00:00
-- url     : https://prove2.me/submissions/0bad2a97-b340-4bcf-876a-20c23975ed3b

import Mathlib
import Definitions.Def_RevenueOrdered_Ratio_Model
import Definitions.Def_RevenueOrdered_Stackelberg_Model
import Definitions.Def_RevenueOrdered_Stackelberg_Greedy
import Definitions.Def_RevenueOrdered_Stackelberg_Instance
import Definitions.Def_RevenueOrdered_Stackelberg_Assortment

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

theorem mem_of_mem_greedy (P : Finset β → Prop) (l : List β) (F : Finset β) {x : β}
    (hx : x ∈ greedy P l F) : x ∈ F ∧ x ∈ l := by
  have := greedy_subset P l F hx
  rw [Finset.mem_filter] at this
  exact this

end StackG0Aux

namespace StackG6Aux

open RevenueOrdered.Stackelberg StackG0Aux

variable {α : Type*}

theorem abovePrice_gt (I : Instance α) : ∀ f ∈ I.R, I.c f < abovePrice I := by
  intro f hf
  unfold abovePrice
  have : I.c f ≤ ∑ g ∈ I.R, I.c g :=
    Finset.single_le_sum (fun g hg => (I.cost_pos g hg).le) hf
  linarith

theorem costs_lt_abovePrice (I : Instance α) {q : ℝ} (hq : q ∈ costs I) : q < abovePrice I := by
  unfold costs at hq
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hq
  exact abovePrice_gt I f hf

theorem roundUp_ge (I : Instance α) (p : α → ℝ) (e : α) (h : ∃ f ∈ I.R, p e ≤ I.c f) :
    p e ≤ roundUp I p e := by
  obtain ⟨f, hf, hle⟩ := h
  have hne : ((costs I).filter (fun q => p e ≤ q)).Nonempty :=
    ⟨I.c f, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hf, hle⟩⟩
  unfold roundUp
  rw [dif_pos hne]
  exact (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2

theorem roundUp_le_cost (I : Instance α) (p : α → ℝ) (e : α) {q : ℝ} (hq : q ∈ costs I)
    (h : p e ≤ q) : roundUp I p e ≤ q := by
  have hmem : q ∈ (costs I).filter (fun q => p e ≤ q) := Finset.mem_filter.mpr ⟨hq, h⟩
  unfold roundUp
  rw [dif_pos ⟨q, hmem⟩]
  exact Finset.min'_le _ _ hmem

theorem roundUp_mono (I : Instance α) (p : α → ℝ) (e f : α) (h : p e ≤ p f) :
    roundUp I p e ≤ roundUp I p f := by
  by_cases hf : ((costs I).filter (fun q => p f ≤ q)).Nonempty
  · have hm := Finset.min'_mem _ hf
    rw [Finset.mem_filter] at hm
    have : roundUp I p f = ((costs I).filter (fun q => p f ≤ q)).min' hf := by
      unfold roundUp; rw [dif_pos hf]
    rw [this]
    exact roundUp_le_cost I p e hm.1 (h.trans hm.2)
  · have : roundUp I p f = abovePrice I := by unfold roundUp; rw [dif_neg hf]
    rw [this]
    unfold roundUp
    split_ifs with he
    · exact (costs_lt_abovePrice I (Finset.mem_filter.mp (Finset.min'_mem _ he)).1).le
    · exact le_rfl

theorem cost_lt_roundUp (I : Instance α) (p : α → ℝ) (e f : α) (hf : f ∈ I.R)
    (h : I.c f < p e) : I.c f < roundUp I p e := by
  unfold roundUp
  split_ifs with he
  · exact lt_of_lt_of_le h (Finset.mem_filter.mp (Finset.min'_mem _ he)).2
  · exact abovePrice_gt I f hf

theorem cost_mem (I : Instance α) {f : α} (hf : f ∈ I.R) : I.c f ∈ costs I :=
  Finset.mem_image_of_mem _ hf

/-- A blue element bought by the customer is priced at most some red cost. -/
theorem bought_le_cost (I : Instance α) (p : α → ℝ) (L : List α) (hL : I.IsCustomerOrder p L)
    (e : α) (heB : e ∈ I.B) (heG : e ∈ greedyM I.M L (I.R ∪ I.B)) :
    ∃ f ∈ I.R, p e ≤ I.c f := by
  by_contra hcon
  push_neg at hcon
  have heL : e ∈ L := by rw [← List.mem_toFinset, hL.1.2]; exact Finset.mem_union_right _ heB
  obtain ⟨l₁, l₂, hsplit⟩ := List.append_of_mem heL
  have hnd : (l₁ ++ e :: l₂).Nodup := hsplit ▸ hL.1.1
  have heR : e ∉ I.R := fun h => Finset.disjoint_left.mp I.disjoint h heB
  -- every red element is scanned before `e`
  have hRl : ∀ f ∈ I.R, f ∈ l₁ := by
    intro f hf
    have hfL : f ∈ L := by rw [← List.mem_toFinset, hL.1.2]; exact Finset.mem_union_left _ hf
    have hfe : f ≠ e := fun h => heR (h ▸ hf)
    rw [hsplit, List.mem_append, List.mem_cons] at hfL
    rcases hfL with h | h | h
    · exact h
    · exact absurd h hfe
    · exfalso
      have hsub : [e, f].Sublist L := by
        rw [hsplit]
        exact ((List.singleton_sublist.mpr h).cons_cons e).trans (List.sublist_append_right _ _)
      have hrel := hL.2.forall_sublist hsub
      have hfB : f ∉ I.B := fun h => Finset.disjoint_left.mp I.disjoint hf h
      unfold Instance.weight at hrel
      rw [if_pos heB, if_neg hfB] at hrel
      exact absurd hrel.1 (not_le.mpr (hcon f hf))
  unfold greedyM at heG
  rw [hsplit, mem_greedy_iff _ l₁ l₂ e _ hnd] at heG
  have hEsub : ((I.R ∪ I.B : Finset α) : Set α) ⊆ I.M.E := by rw [I.ground_eq]
  have hJ := greedyM_isBasis I.M l₁ (I.R ∪ I.B) hEsub
  unfold greedyM at hJ
  set J := greedy (fun X => I.M.Indep (X : Set α)) l₁ (I.R ∪ I.B)
  have heJ : e ∉ (J : Set α) := by
    intro h
    have := (mem_of_mem_greedy _ l₁ _ h).2
    rw [List.nodup_append] at hnd
    exact hnd.2.2 e this e List.mem_cons_self rfl
  obtain ⟨X, hXR, hX⟩ := I.exists_red_base
  have hcl : e ∈ I.M.closure (J : Set α) := by
    rw [hJ.closure_eq_closure]
    have hXsub : X ⊆ (((I.R ∪ I.B).filter (fun x => x ∈ l₁) : Finset α) : Set α) := by
      intro x hx
      have hxR : x ∈ I.R := hXR hx
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨Finset.mem_union_left _ hxR, hRl x hxR⟩
    refine I.M.closure_subset_closure hXsub ?_
    rw [hX.closure_eq, ← I.ground_eq]
    exact Finset.mem_coe.mpr (Finset.mem_union_right _ heB)
  have h2 := heG.2
  rw [Finset.coe_insert, hJ.indep.insert_indep_iff_of_notMem heJ] at h2
  exact h2.2 hcl

end StackG6Aux

open RevenueOrdered.Stackelberg StackG6Aux in
theorem solution {α : Type*} (I : Instance α) (p : α → ℝ)
    (hp : ∀ e ∈ I.B, 0 < p e) (L' : List α) (hL' : I.IsCustomerOrder p L') :
    I.IsCustomerOrder (roundUp I p) L' ∧
      I.stackRevenue p L' ≤ I.stackRevenue (roundUp I p) L' := by
  refine ⟨⟨hL'.1, ?_⟩, ?_⟩
  · refine hL'.2.imp_of_mem ?_
    intro e f he hf hrel
    have heE : e ∈ I.R ∪ I.B := by rw [← hL'.1.2, List.mem_toFinset]; exact he
    have hfE : f ∈ I.R ∪ I.B := by rw [← hL'.1.2, List.mem_toFinset]; exact hf
    unfold Instance.weight at hrel ⊢
    by_cases heB : e ∈ I.B <;> by_cases hfB : f ∈ I.B
    · rw [if_pos heB, if_pos hfB] at hrel ⊢
      refine ⟨roundUp_mono I p e f hrel.1, fun _ heR => ?_⟩
      exact absurd heB (Finset.disjoint_left.mp I.disjoint heR)
    · rw [if_pos heB, if_neg hfB] at hrel ⊢
      have hfR : f ∈ I.R := (Finset.mem_union.mp hfE).resolve_right hfB
      refine ⟨roundUp_le_cost I p e (cost_mem I hfR) hrel.1, fun _ heR => ?_⟩
      exact absurd heB (Finset.disjoint_left.mp I.disjoint heR)
    · rw [if_neg heB, if_pos hfB] at hrel ⊢
      have heR : e ∈ I.R := (Finset.mem_union.mp heE).resolve_right heB
      have hfR : f ∉ I.R := fun h => Finset.disjoint_left.mp I.disjoint h hfB
      have hlt : I.c e < p f := lt_of_le_of_ne hrel.1 (fun h => hfR (hrel.2 h heR))
      have := cost_lt_roundUp I p f e heR hlt
      exact ⟨this.le, fun h => absurd h this.ne⟩
    · rw [if_neg heB, if_neg hfB] at hrel ⊢
      exact hrel
  · unfold Instance.stackRevenue
    apply Finset.sum_le_sum
    intro e he
    rw [Finset.mem_inter] at he
    exact roundUp_ge I p e (bought_le_cost I p L' hL' e he.1 he.2)
