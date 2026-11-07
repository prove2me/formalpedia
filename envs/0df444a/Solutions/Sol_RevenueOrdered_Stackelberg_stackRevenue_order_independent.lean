-- Prove2me | solution 1 for RevenueOrdered.Stackelberg.stackRevenue_order_independent
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T00:47:04.940451+00:00
-- url     : https://prove2.me/submissions/e8dda487-3b97-4de9-8a02-73135da3118d

import Mathlib
import Definitions.Def_RevenueOrdered_Stackelberg_Greedy
import Definitions.Def_RevenueOrdered_Stackelberg_Instance
import Theorems.Thm_RevenueOrdered_Stackelberg_greedy_block_card_eq

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

namespace StackG2Aux

open RevenueOrdered.Stackelberg StackG0Aux

variable {α : Type*}

/-- The block key of an element: its weight, then its colour (blue `0`, red `1`). -/
noncomputable def key (I : Instance α) (p : α → ℝ) (e : α) : ℝ ×ₗ ℕ :=
  toLex (I.weight p e, if e ∈ I.R then 1 else 0)

/-- The block index: the number of smaller keys. -/
noncomputable def blkIdx (I : Instance α) (p : α → ℝ) (e : α) : ℕ :=
  (((I.R ∪ I.B).image (key I p)).filter (fun k => k < key I p e)).card

theorem blkIdx_lt_of_key_lt (I : Instance α) (p : α → ℝ) (e f : α) (he : e ∈ I.R ∪ I.B)
    (h : key I p e < key I p f) : blkIdx I p e < blkIdx I p f := by
  unfold blkIdx
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨key I p e, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_image_of_mem _ he, h⟩
    · simp
  · intro k hk
    rw [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, hk.2.trans h⟩

theorem blkIdx_le_of_key_le (I : Instance α) (p : α → ℝ) (e f : α)
    (h : key I p e ≤ key I p f) : blkIdx I p e ≤ blkIdx I p f := by
  unfold blkIdx
  apply Finset.card_le_card
  intro k hk
  rw [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, lt_of_lt_of_le hk.2 h⟩

theorem key_lt_of_blkIdx_lt (I : Instance α) (p : α → ℝ) (e f : α)
    (h : blkIdx I p e < blkIdx I p f) : key I p e < key I p f := by
  by_contra hc
  exact absurd (blkIdx_le_of_key_le I p f e (not_lt.mp hc)) (not_le.mpr h)

theorem key_eq_iff_blkIdx_eq (I : Instance α) (p : α → ℝ) (e f : α) (he : e ∈ I.R ∪ I.B)
    (hf : f ∈ I.R ∪ I.B) : key I p e = key I p f ↔ blkIdx I p e = blkIdx I p f := by
  constructor
  · intro h; unfold blkIdx; rw [h]
  · intro h
    rcases lt_trichotomy (key I p e) (key I p f) with h1 | h1 | h1
    · exact absurd h (blkIdx_lt_of_key_lt I p e f he h1).ne
    · exact h1
    · exact absurd h (blkIdx_lt_of_key_lt I p f e hf h1).ne'

theorem key_le_of_rel (I : Instance α) (p : α → ℝ) (e f : α)
    (h : I.weight p e ≤ I.weight p f ∧ (I.weight p e = I.weight p f → e ∈ I.R → f ∈ I.R)) :
    key I p e ≤ key I p f := by
  unfold key
  rw [Prod.Lex.toLex_le_toLex']
  refine ⟨h.1, fun heq => ?_⟩
  by_cases he : e ∈ I.R
  · simp [he, h.2 heq he]
  · simp [he]

theorem agree (I : Instance α) (p : α → ℝ) (L : List α) (hL : I.IsCustomerOrder p L) :
    ∀ e ∈ I.R ∪ I.B, ∀ f ∈ I.R ∪ I.B, blkIdx I p e < blkIdx I p f → [e, f].Sublist L := by
  intro e he f hf hlt
  have hk := key_lt_of_blkIdx_lt I p e f hlt
  have hef : e ≠ f := by rintro rfl; exact lt_irrefl _ hk
  have heL : e ∈ L := by rw [← List.mem_toFinset, hL.1.2]; exact he
  have hfL : f ∈ L := by rw [← List.mem_toFinset, hL.1.2]; exact hf
  rcases sublist_or L e f heL hfL hef with h | h
  · exact h
  · exact absurd (key_le_of_rel I p f e (hL.2.forall_sublist h)) (not_le.mpr hk)

theorem blue_iff_key (I : Instance α) (p : α → ℝ) (γ : ℝ) (e e₀ : α) (he₀ : e₀ ∈ I.B)
    (hpe₀ : p e₀ = γ) (he : e ∈ I.R ∪ I.B) :
    (e ∈ I.B ∧ p e = γ) ↔ key I p e = key I p e₀ := by
  have he₀R : e₀ ∉ I.R := fun h => Finset.disjoint_left.mp I.disjoint h he₀
  unfold key Instance.weight
  constructor
  · rintro ⟨heB, rfl⟩
    have heR : e ∉ I.R := fun h => Finset.disjoint_left.mp I.disjoint h heB
    simp [heB, he₀, heR, he₀R, hpe₀]
  · intro h
    have h2 := congrArg (fun x => (ofLex x).2) h
    simp only [ofLex_toLex, he₀R, if_false] at h2
    have heR : e ∉ I.R := by
      intro hR; rw [if_pos hR] at h2; exact one_ne_zero h2
    have heB : e ∈ I.B := (Finset.mem_union.mp he).resolve_left heR
    have h1 := congrArg (fun x => (ofLex x).1) h
    simp only [ofLex_toLex, he₀, heB, if_true] at h1
    exact ⟨heB, h1.trans hpe₀⟩

theorem count_eq (I : Instance α) (p : α → ℝ) (L L' : List α) (hL : I.IsCustomerOrder p L)
    (hL' : I.IsCustomerOrder p L') (γ : ℝ) :
    ((I.B ∩ greedyM I.M L (I.R ∪ I.B)).filter (fun e => p e = γ)).card =
      ((I.B ∩ greedyM I.M L' (I.R ∪ I.B)).filter (fun e => p e = γ)).card := by
  by_cases hex : ∃ e₀ ∈ I.B, p e₀ = γ
  · obtain ⟨e₀, he₀, hpe₀⟩ := hex
    have he₀E : e₀ ∈ I.R ∪ I.B := Finset.mem_union_right _ he₀
    have hblk := greedy_block_card_eq I.M (I.R ∪ I.B) I.ground_eq L L' hL.1 hL'.1
      (blkIdx I p) (fun e he f hf h => ⟨agree I p L hL e he f hf h, agree I p L' hL' e he f hf h⟩)
      (blkIdx I p e₀)
    have hrw : ∀ L₀ : List α, ((I.B ∩ greedyM I.M L₀ (I.R ∪ I.B)).filter (fun e => p e = γ)) =
        (greedyM I.M L₀ (I.R ∪ I.B)).filter (fun e => blkIdx I p e = blkIdx I p e₀) := by
      intro L₀
      ext e
      simp only [Finset.mem_filter, Finset.mem_inter]
      constructor
      · rintro ⟨⟨heB, heG⟩, hpe⟩
        refine ⟨heG, ?_⟩
        rw [← key_eq_iff_blkIdx_eq I p e e₀ (Finset.mem_union_right _ heB) he₀E]
        exact (blue_iff_key I p γ e e₀ he₀ hpe₀ (Finset.mem_union_right _ heB)).mp ⟨heB, hpe⟩
      · rintro ⟨heG, hb⟩
        have heE : e ∈ I.R ∪ I.B := by
          unfold greedyM at heG
          exact (Finset.mem_filter.mp (greedy_subset _ L₀ _ heG)).1
        rw [← key_eq_iff_blkIdx_eq I p e e₀ heE he₀E] at hb
        have := (blue_iff_key I p γ e e₀ he₀ hpe₀ heE).mpr hb
        exact ⟨⟨this.1, heG⟩, this.2⟩
    rw [hrw L, hrw L']
    exact hblk
  · push_neg at hex
    have h0 : ∀ L₀ : List α,
        ((I.B ∩ greedyM I.M L₀ (I.R ∪ I.B)).filter (fun e => p e = γ)) = ∅ := by
      intro L₀
      ext e
      simp only [Finset.mem_filter, Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
      intro heB
      exact hex e heB.1
    rw [h0 L, h0 L']

theorem sum_eq_count (I : Instance α) (p : α → ℝ) (L : List α) :
    I.stackRevenue p L = ∑ γ ∈ I.B.image p,
      (((I.B ∩ greedyM I.M L (I.R ∪ I.B)).filter (fun e => p e = γ)).card : ℝ) * γ := by
  unfold Instance.stackRevenue
  rw [← Finset.sum_fiberwise_of_maps_to' (s := I.B ∩ greedyM I.M L (I.R ∪ I.B))
    (t := I.B.image p) (g := p) (fun i hi => Finset.mem_image_of_mem _
      (Finset.mem_inter.mp hi).1) (fun γ => γ)]
  refine Finset.sum_congr rfl ?_
  intro γ _
  rw [Finset.sum_const, nsmul_eq_mul]

end StackG2Aux

open RevenueOrdered.Stackelberg StackG2Aux in
theorem solution {α : Type*} (I : Instance α) (p : α → ℝ)
    (_hp : ∀ e ∈ I.B, 0 < p e) (L L' : List α) (hL : I.IsCustomerOrder p L)
    (hL' : I.IsCustomerOrder p L') :
    (∀ γ : ℝ, ((I.B ∩ greedyM I.M L (I.R ∪ I.B)).filter (fun e => p e = γ)).card =
        ((I.B ∩ greedyM I.M L' (I.R ∪ I.B)).filter (fun e => p e = γ)).card) ∧
      I.stackRevenue p L = I.stackRevenue p L' := by
  refine ⟨count_eq I p L L' hL hL', ?_⟩
  rw [sum_eq_count, sum_eq_count]
  refine Finset.sum_congr rfl ?_
  intro γ _
  rw [count_eq I p L L' hL hL' γ]
