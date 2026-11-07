-- Prove2me | solution 1 for RevenueOrdered.Stackelberg.revenue_eq_stackRevenue_priceOfAssortment
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T01:00:11.024314+00:00
-- url     : https://prove2.me/submissions/ebddbc53-fb85-46db-a3c4-e7bb263e0fa5

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

namespace StackCoreB

open RevenueOrdered.Stackelberg StackG0Aux

variable {α : Type*}



/-- The projection `R ∪ 𝒞 → E`, `a ↦ a`, `(e, q) ↦ e`. -/
def proj : α ⊕ (α × ℝ) → α := Sum.elim id Prod.fst

theorem mem_auxGround (I : Instance α) (x : α ⊕ (α × ℝ)) :
    x ∈ auxGround I ↔ (∃ a ∈ I.R, x = Sum.inl a) ∨
      (∃ e ∈ I.B, ∃ q ∈ costs I, x = Sum.inr (e, q)) := by
  unfold auxGround products
  rcases x with a | ⟨e, q⟩ <;> simp

theorem image_eq (I : Instance α) (X : Finset (α ⊕ (α × ℝ))) (hX : X ⊆ auxGround I) :
    proj '' (X : Set (α ⊕ (α × ℝ))) =
      (((I.R.filter (fun a => Sum.inl a ∈ X)) ∪
        (I.B.filter (fun e => ∃ q ∈ costs I, Sum.inr (e, q) ∈ X)) : Finset α) : Set α) := by
  ext a
  simp only [Set.mem_image, Finset.mem_coe, Finset.coe_union, Finset.coe_filter,
    Set.mem_union]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases (mem_auxGround I x).mp (hX hx) with ⟨b, hb, rfl⟩ | ⟨e, he, q, hq, rfl⟩
    · left; exact ⟨hb, hx⟩
    · right; exact ⟨he, q, hq, hx⟩
  · rintro (⟨ha, hx⟩ | ⟨ha, q, _, hx⟩)
    · exact ⟨_, hx, rfl⟩
    · exact ⟨_, hx, rfl⟩

theorem injOn_iff (I : Instance α) (X : Finset (α ⊕ (α × ℝ))) (hX : X ⊆ auxGround I) :
    Set.InjOn proj (X : Set (α ⊕ (α × ℝ))) ↔
      ∀ e ∈ I.B, (X.filter (fun y => ∃ q ∈ costs I, y = Sum.inr (e, q))).card ≤ 1 := by
  constructor
  · intro hinj e _
    rw [Finset.card_le_one]
    intro x hx y hy
    rw [Finset.mem_filter] at hx hy
    obtain ⟨q, _, rfl⟩ := hx.2
    obtain ⟨q', _, rfl⟩ := hy.2
    exact hinj (Finset.mem_coe.mpr hx.1) (Finset.mem_coe.mpr hy.1) rfl
  · intro hc x hx y hy hxy
    rw [Finset.mem_coe] at hx hy
    rcases (mem_auxGround I x).mp (hX hx) with ⟨a, ha, rfl⟩ | ⟨e, he, q, hq, rfl⟩ <;>
      rcases (mem_auxGround I y).mp (hX hy) with ⟨b, hb, rfl⟩ | ⟨e', he', q', hq', rfl⟩
    · simp only [proj, Sum.elim_inl, id] at hxy; rw [hxy]
    · simp only [proj, Sum.elim_inl, Sum.elim_inr, id] at hxy
      subst hxy
      exact absurd he' (Finset.disjoint_left.mp I.disjoint ha)
    · simp only [proj, Sum.elim_inl, Sum.elim_inr, id] at hxy
      subst hxy
      exact absurd hb (Finset.disjoint_right.mp I.disjoint he)
    · simp only [proj, Sum.elim_inr] at hxy
      subst hxy
      have := Finset.card_le_one.mp (hc e he) (Sum.inr (e, q))
        (Finset.mem_filter.mpr ⟨hx, q, hq, rfl⟩) (Sum.inr (e, q'))
        (Finset.mem_filter.mpr ⟨hy, q', hq', rfl⟩)
      exact this


/-- The auxiliary matroid `M′`: the pull-back of `M` along the projection, restricted to
`R ∪ 𝒞`. -/
noncomputable def auxM (I : Instance α) : Matroid (α ⊕ (α × ℝ)) :=
  Matroid.restrict (I.M.comap proj) (auxGround I : Set (α ⊕ (α × ℝ)))

theorem auxM_indep (I : Instance α) (X : Finset (α ⊕ (α × ℝ))) :
    (auxM I).Indep (X : Set (α ⊕ (α × ℝ))) ↔ auxIndep I X := by
  unfold auxM
  rw [Matroid.restrict_indep_iff, Matroid.comap_indep_iff]
  unfold auxIndep
  constructor
  · rintro ⟨⟨hind, hinj⟩, hX⟩
    have hX' : X ⊆ auxGround I := by exact_mod_cast hX
    refine ⟨hX', (injOn_iff I X hX').mp hinj, ?_⟩
    rw [← image_eq I X hX']
    exact hind
  · rintro ⟨hX, hc, hind⟩
    refine ⟨⟨?_, (injOn_iff I X hX).mpr hc⟩, by exact_mod_cast hX⟩
    rw [image_eq I X hX]
    exact hind

theorem greedy_aux_eq (I : Instance α) (L : List (α ⊕ (α × ℝ))) (F : Finset (α ⊕ (α × ℝ))) :
    greedy (auxIndep I) L F = greedyM (auxM I) L F := by
  unfold greedyM
  have : (auxIndep I) =
      (fun X : Finset (α ⊕ (α × ℝ)) => (auxM I).Indep (X : Set (α ⊕ (α × ℝ)))) := by
    funext X; exact propext (auxM_indep I X).symm
  rw [this]

/-- Greedy restricted to a down-closed (with respect to the scan order) predicate is a basis. -/
theorem pref_isBasis {β : Type*} (N : Matroid β) (L : List β) (hnd : L.Nodup) (F : Finset β)
    (hF : (F : Set β) ⊆ N.E) (hFL : ∀ x ∈ F, x ∈ L) (Rel : β → β → Prop)
    (hP : L.Pairwise Rel) (D : β → Prop) (hD : ∀ y x, Rel y x → D x → D y) :
    N.IsBasis (((greedyM N L F).filter D : Finset β) : Set β) ((F.filter D : Finset β) : Set β) := by
  have hG0 := greedyM_isBasis N L F hF
  have hfil : F.filter (fun x => x ∈ L) = F := Finset.filter_true_of_mem hFL
  rw [hfil] at hG0
  have hGF : greedyM N L F ⊆ F := by exact_mod_cast hG0.subset
  refine (hG0.indep.subset (by
    intro x hx; exact (Finset.mem_filter.mp hx).1)).isBasis_of_forall_insert ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter] at hx ⊢
    exact ⟨hGF hx.1, hx.2⟩
  · rintro x ⟨hxX, hxG⟩
    simp only [Finset.mem_coe, Finset.mem_filter] at hxX hxG
    have hxF := hxX.1
    have hxnG : x ∉ greedyM N L F := fun h => hxG ⟨h, hxX.2⟩
    obtain ⟨l₁, l₂, hsplit⟩ := List.append_of_mem (hFL x hxF)
    have hnd' : (l₁ ++ x :: l₂).Nodup := hsplit ▸ hnd
    unfold greedyM at hxnG
    rw [hsplit, mem_greedy_iff _ l₁ l₂ x F hnd'] at hxnG
    have hdep : ¬ N.Indep ((insert x (greedy (fun X => N.Indep (X : Set β)) l₁ F) :
        Finset β) : Set β) := fun h => hxnG ⟨hxF, h⟩
    have hJsub : (greedy (fun X => N.Indep (X : Set β)) l₁ F) ⊆
        (greedyM N L F).filter D := by
      intro y hy
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · unfold greedyM; rw [hsplit]; exact greedy_prefix_subset _ l₁ l₂ x F hy
      · have hyl := (mem_of_mem_greedy _ l₁ F hy).2
        have hP' := hP
        rw [hsplit, List.pairwise_append] at hP'
        exact hD y x (hP'.2.2 y hyl x List.mem_cons_self) hxX.2
    refine ⟨fun hi => hdep (hi.subset ?_), ?_⟩
    · rw [Finset.coe_insert]
      exact Set.insert_subset_insert (by exact_mod_cast hJsub)
    · refine Set.insert_subset (hF hxF) ?_
      intro z hz
      simp only [Finset.mem_coe, Finset.mem_filter] at hz
      exact hF (hGF hz.1)

/-- The scanned set `R ∪ S`. -/
noncomputable def scanSet (I : Instance α) (S : Finset (Product I)) : Finset (α ⊕ (α × ℝ)) :=
  I.R.map Function.Embedding.inl ∪ S.map (productEmb I)

theorem scanSet_subset (I : Instance α) (S : Finset (Product I)) : scanSet I S ⊆ auxGround I := by
  unfold scanSet auxGround
  apply Finset.union_subset_union le_rfl
  intro z hz
  rw [Finset.mem_map] at hz ⊢
  obtain ⟨y, _, rfl⟩ := hz
  exact ⟨y.1, y.2, rfl⟩

/-- The order relation of an auxiliary ordering. -/
def auxRel (I : Instance α) (x y : α ⊕ (α × ℝ)) : Prop :=
  auxCost I x ≤ auxCost I y ∧ (auxCost I x = auxCost I y → x.isLeft = true → y.isLeft = true)

/-- The order relation of a customer ordering. -/
def custRel (I : Instance α) (p : α → ℝ) (e f : α) : Prop :=
  I.weight p e ≤ I.weight p f ∧ (I.weight p e = I.weight p f → e ∈ I.R → f ∈ I.R)

theorem auxSide (I : Instance α) (L : List (α ⊕ (α × ℝ))) (hL : IsAuxOrder I L)
    (S : Finset (Product I)) (D : α ⊕ (α × ℝ) → Prop)
    (hD : ∀ y x, auxRel I y x → D x → D y) :
    (((greedy (auxIndep I) L (scanSet I S)).filter D).card : ℕ∞) =
      I.M.eRk (proj '' (((scanSet I S).filter D : Finset (α ⊕ (α × ℝ))) : Set (α ⊕ (α × ℝ)))) := by
  rw [greedy_aux_eq]
  have hsub : ((scanSet I S : Finset (α ⊕ (α × ℝ))) : Set (α ⊕ (α × ℝ))) ⊆ (auxM I).E := by
    show _ ⊆ ((auxGround I : Finset (α ⊕ (α × ℝ))) : Set (α ⊕ (α × ℝ)))
    exact_mod_cast scanSet_subset I S
  have hFL : ∀ x ∈ scanSet I S, x ∈ L := by
    intro x hx
    have h := scanSet_subset I S hx
    rw [← hL.1.2, List.mem_toFinset] at h
    exact h
  have hB := pref_isBasis (auxM I) L hL.1.1 (scanSet I S) hsub hFL (auxRel I) hL.2 D hD
  unfold auxM at hB ⊢
  have hR : ((auxGround I : Finset _) : Set (α ⊕ (α × ℝ))) ⊆ (I.M.comap proj).E := by
    intro z hz
    rw [Matroid.comap_ground_eq, Set.mem_preimage, ← I.ground_eq]
    rcases (mem_auxGround I z).mp hz with ⟨a, ha, rfl⟩ | ⟨e, he, q, _, rfl⟩
    · exact Finset.mem_coe.mpr (Finset.mem_union_left _ ha)
    · exact Finset.mem_coe.mpr (Finset.mem_union_right _ he)
  rw [Matroid.isBasis_restrict_iff hR, Matroid.comap_isBasis_iff] at hB
  obtain ⟨⟨hB1, hinj, _⟩, _⟩ := hB
  rw [← Set.encard_coe_eq_coe_finsetCard, ← hinj.encard_image, hB1.encard_eq_eRk]

theorem mainSide (I : Instance α) (p : α → ℝ) (L : List α) (hL : I.IsCustomerOrder p L)
    (D : α → Prop) (hD : ∀ y x, custRel I p y x → D x → D y) :
    I.M.IsBasis (((greedyM I.M L (I.R ∪ I.B)).filter D : Finset α) : Set α)
      (((I.R ∪ I.B).filter D : Finset α) : Set α) := by
  refine pref_isBasis I.M L hL.1.1 (I.R ∪ I.B) (by rw [I.ground_eq]) ?_ (custRel I p) hL.2 D hD
  intro x hx
  rw [← List.mem_toFinset, hL.1.2]; exact hx

theorem eRk_sandwich {β : Type*} (N : Matroid β) (X Y Z : Set β) (hB : N.IsBasis X Z)
    (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) : N.eRk Y = (X.encard) := by
  apply le_antisymm
  · rw [← hB.eRk_eq_encard]; exact N.eRk_mono hYZ
  · rw [← hB.indep.eRk_eq_encard]; exact N.eRk_mono hXY

/-- Predicates: strictly below level `γ`, and at most level `γ` with ties only for the
non-red side. -/
def D0 (I : Instance α) (p : α → ℝ) (γ : ℝ) (x : α) : Prop := I.weight p x < γ
def D1 (I : Instance α) (p : α → ℝ) (γ : ℝ) (x : α) : Prop :=
  I.weight p x < γ ∨ (I.weight p x = γ ∧ x ∉ I.R)
def D0' (I : Instance α) (γ : ℝ) (z : α ⊕ (α × ℝ)) : Prop := auxCost I z < γ
def D1' (I : Instance α) (γ : ℝ) (z : α ⊕ (α × ℝ)) : Prop :=
  auxCost I z < γ ∨ (auxCost I z = γ ∧ z.isLeft = false)

theorem D0_closed (I : Instance α) (p : α → ℝ) (γ : ℝ) :
    ∀ y x, custRel I p y x → D0 I p γ x → D0 I p γ y := by
  intro y x h hx; unfold D0 at *; exact lt_of_le_of_lt h.1 hx

theorem D1_closed (I : Instance α) (p : α → ℝ) (γ : ℝ) :
    ∀ y x, custRel I p y x → D1 I p γ x → D1 I p γ y := by
  intro y x h hx
  unfold D1 at *
  rcases hx with hx | ⟨hx, hxR⟩
  · exact Or.inl (lt_of_le_of_lt h.1 hx)
  · rcases lt_or_eq_of_le h.1 with h1 | h1
    · exact Or.inl (h1.trans_eq hx)
    · exact Or.inr ⟨h1.trans hx, fun hyR => hxR (h.2 h1 hyR)⟩

theorem D0'_closed (I : Instance α) (γ : ℝ) :
    ∀ y x, auxRel I y x → D0' I γ x → D0' I γ y := by
  intro y x h hx; unfold D0' at *; exact lt_of_le_of_lt h.1 hx

theorem D1'_closed (I : Instance α) (γ : ℝ) :
    ∀ y x, auxRel I y x → D1' I γ x → D1' I γ y := by
  intro y x h hx
  unfold D1' at *
  rcases hx with hx | ⟨hx, hxR⟩
  · exact Or.inl (lt_of_le_of_lt h.1 hx)
  · rcases lt_or_eq_of_le h.1 with h1 | h1
    · exact Or.inl (h1.trans_eq hx)
    · refine Or.inr ⟨h1.trans hx, ?_⟩
      cases hy : y.isLeft
      · rfl
      · have := h.2 h1 hy; rw [hxR] at this; exact absurd this (by simp)

theorem weight_red (I : Instance α) (p : α → ℝ) {x : α} (hx : x ∈ I.R) :
    I.weight p x = I.c x := by
  unfold Instance.weight
  rw [if_neg (fun h => Finset.disjoint_left.mp I.disjoint hx h)]

theorem weight_blue (I : Instance α) (p : α → ℝ) {x : α} (hx : x ∈ I.B) :
    I.weight p x = p x := by
  unfold Instance.weight; rw [if_pos hx]

theorem not_red_of_blue (I : Instance α) {x : α} (hx : x ∈ I.B) : x ∉ I.R :=
  fun h => Finset.disjoint_left.mp I.disjoint h hx

theorem mem_scanSet_iff (I : Instance α) (S : Finset (Product I)) (z : α ⊕ (α × ℝ)) :
    z ∈ scanSet I S ↔ (∃ a ∈ I.R, z = Sum.inl a) ∨ (∃ y ∈ S, z = Sum.inr y.1) := by
  unfold scanSet
  rw [Finset.mem_union, Finset.mem_map, Finset.mem_map]
  constructor
  · rintro (⟨a, ha, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr ⟨y, hy, rfl⟩
  · rintro (⟨a, ha, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr ⟨y, hy, rfl⟩

theorem product_blue (I : Instance α) (y : Product I) : y.1.1 ∈ I.B := by
  have hy := y.2
  unfold products at hy
  exact (Finset.mem_product.mp hy).1

theorem product_cost (I : Instance α) (y : Product I) : y.1.2 ∈ costs I := by
  have hy := y.2
  unfold products at hy
  exact (Finset.mem_product.mp hy).2

/-- The level-wise count of picked products agrees with the level-wise count of bought blue
elements, under the matching hypotheses `hA`, `hB`. -/
theorem count_match (I : Instance α) (L : List (α ⊕ (α × ℝ))) (hL : IsAuxOrder I L)
    (S : Finset (Product I)) (p : α → ℝ) (L' : List α) (hL' : I.IsCustomerOrder p L')
    (hA : ∀ x ∈ I.B, x ∈ greedyM I.M L' (I.R ∪ I.B) → ∃ y ∈ S, y.1.1 = x ∧ y.1.2 = p x)
    (hB : ∀ y ∈ S, p y.1.1 ≤ y.1.2) (γ : ℝ) :
    ((greedy (auxIndep I) L (scanSet I S)).filter
        (fun z => z.isRight = true ∧ auxCost I z = γ)).card =
      ((I.B ∩ greedyM I.M L' (I.R ∪ I.B)).filter (fun e => p e = γ)).card := by
  set G' := greedy (auxIndep I) L (scanSet I S)
  set G := greedyM I.M L' (I.R ∪ I.B)
  have hGE : G ⊆ I.R ∪ I.B := by
    intro x hx
    exact (mem_of_mem_greedy _ L' _ hx).1
  -- the inclusions
  have hinc : ∀ (Dm : α → Prop) (Da : α ⊕ (α × ℝ) → Prop)
      (hred : ∀ a ∈ I.R, Dm a ↔ Da (Sum.inl a))
      (hAx : ∀ x ∈ I.B, Dm x → ∀ y : Product I, y.1.2 = p x → Da (Sum.inr y.1))
      (hBy : ∀ y : Product I, p y.1.1 ≤ y.1.2 → Da (Sum.inr y.1) → Dm y.1.1),
      ((G.filter Dm : Finset α) : Set α) ⊆
          proj '' (((scanSet I S).filter Da : Finset _) : Set (α ⊕ (α × ℝ))) ∧
        proj '' (((scanSet I S).filter Da : Finset _) : Set (α ⊕ (α × ℝ))) ⊆
          (((I.R ∪ I.B).filter Dm : Finset α) : Set α) := by
    intro Dm Da hred hAx hBy
    constructor
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter] at hx
      rcases Finset.mem_union.mp (hGE hx.1) with hxR | hxB
      · refine ⟨Sum.inl x, ?_, rfl⟩
        simp only [Finset.mem_coe, Finset.mem_filter]
        exact ⟨(mem_scanSet_iff I S _).mpr (Or.inl ⟨x, hxR, rfl⟩), (hred x hxR).mp hx.2⟩
      · obtain ⟨y, hyS, hy1, hy2⟩ := hA x hxB hx.1
        refine ⟨Sum.inr y.1, ?_, by simp [proj, hy1]⟩
        simp only [Finset.mem_coe, Finset.mem_filter]
        exact ⟨(mem_scanSet_iff I S _).mpr (Or.inr ⟨y, hyS, rfl⟩), hAx x hxB hx.2 y hy2⟩
    · rintro x ⟨z, hz, rfl⟩
      simp only [Finset.mem_coe, Finset.mem_filter] at hz ⊢
      rcases (mem_scanSet_iff I S z).mp hz.1 with ⟨a, ha, rfl⟩ | ⟨y, hyS, rfl⟩
      · exact ⟨Finset.mem_union_left _ ha, (hred a ha).mpr hz.2⟩
      · exact ⟨Finset.mem_union_right _ (product_blue I y), hBy y (hB y hyS) hz.2⟩
  have hc : ∀ (Dm : α → Prop) (Da : α ⊕ (α × ℝ) → Prop)
      (hDm : ∀ y x, custRel I p y x → Dm x → Dm y) (hDa : ∀ y x, auxRel I y x → Da x → Da y)
      (hred : ∀ a ∈ I.R, Dm a ↔ Da (Sum.inl a))
      (hAx : ∀ x ∈ I.B, Dm x → ∀ y : Product I, y.1.2 = p x → Da (Sum.inr y.1))
      (hBy : ∀ y : Product I, p y.1.1 ≤ y.1.2 → Da (Sum.inr y.1) → Dm y.1.1),
      (G'.filter Da).card = (G.filter Dm).card := by
    intro Dm Da hDm hDa hred hAx hBy
    have h1 := auxSide I L hL S Da hDa
    obtain ⟨i1, i2⟩ := hinc Dm Da hred hAx hBy
    have h2 := eRk_sandwich I.M _ _ _ (mainSide I p L' hL' Dm hDm) i1 i2
    rw [h2, Set.encard_coe_eq_coe_finsetCard] at h1
    exact_mod_cast h1
  have hc0 := hc (D0 I p γ) (D0' I γ) (D0_closed I p γ) (D0'_closed I γ)
    (by intro a ha; unfold D0 D0'; rw [weight_red I p ha]; rfl)
    (by intro x hx h y hy; unfold D0 D0' at *; rw [weight_blue I p hx] at h
        show y.1.2 < γ; rw [hy]; exact h)
    (by intro y hle h; unfold D0 D0' at *; rw [weight_blue I p (product_blue I y)]
        exact lt_of_le_of_lt hle h)
  have hc1 := hc (D1 I p γ) (D1' I γ) (D1_closed I p γ) (D1'_closed I γ)
    (by
      intro a ha; unfold D1 D1'; rw [weight_red I p ha]
      simp only [auxCost, Sum.elim_inl, Sum.isLeft_inl, ha, not_true_eq_false, and_false,
        or_false, Bool.true_eq_false])
    (by
      intro x hx h y hy; unfold D1 D1' at *; rw [weight_blue I p hx] at h
      show y.1.2 < γ ∨ (y.1.2 = γ ∧ (Sum.inr y.1 : α ⊕ (α × ℝ)).isLeft = false)
      rw [hy]
      rcases h with h | ⟨h, _⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, rfl⟩)
    (by
      intro y hle h; unfold D1 D1' at *
      rw [weight_blue I p (product_blue I y)]
      have h' : y.1.2 ≤ γ := by
        rcases h with h | ⟨h, _⟩
        · exact h.le
        · exact h.le
      rcases lt_or_eq_of_le (hle.trans h') with h2 | h2
      · exact Or.inl h2
      · exact Or.inr ⟨h2, not_red_of_blue I (product_blue I y)⟩)
  -- split the counts
  have hsplitA := Finset.card_filter_add_card_filter_not (s := G'.filter (D1' I γ)) (D0' I γ)
  have hsplitM := Finset.card_filter_add_card_filter_not (s := G.filter (D1 I p γ)) (D0 I p γ)
  have e1 : (G'.filter (D1' I γ)).filter (D0' I γ) = G'.filter (D0' I γ) := by
    rw [Finset.filter_filter]; congr 1; funext z
    apply propext; unfold D0' D1'
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨Or.inl h, h⟩
  have e2 : (G.filter (D1 I p γ)).filter (D0 I p γ) = G.filter (D0 I p γ) := by
    rw [Finset.filter_filter]; congr 1; funext z
    apply propext; unfold D0 D1
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨Or.inl h, h⟩
  have e3 : (G'.filter (D1' I γ)).filter (fun z => ¬ D0' I γ z) =
      G'.filter (fun z => z.isRight = true ∧ auxCost I z = γ) := by
    rw [Finset.filter_filter]; congr 1; funext z
    apply propext; unfold D0' D1'
    constructor
    · rintro ⟨h | ⟨h, hl⟩, hn⟩
      · exact absurd h hn
      · refine ⟨?_, h⟩
        rcases z with a | b
        · exact absurd hl (by simp)
        · rfl
    · rintro ⟨hr, h⟩
      refine ⟨Or.inr ⟨h, ?_⟩, by rw [h]; exact lt_irrefl _⟩
      rcases z with a | b
      · exact absurd hr (by simp)
      · rfl
  have e4 : (G.filter (D1 I p γ)).filter (fun z => ¬ D0 I p γ z) =
      (I.B ∩ G).filter (fun e => p e = γ) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_inter]
    unfold D0 D1
    constructor
    · rintro ⟨⟨hxG, h | ⟨h, hxR⟩⟩, hn⟩
      · exact absurd h hn
      · have hxB : x ∈ I.B := (Finset.mem_union.mp (hGE hxG)).resolve_left hxR
        rw [weight_blue I p hxB] at h
        exact ⟨⟨hxB, hxG⟩, h⟩
    · rintro ⟨⟨hxB, hxG⟩, h⟩
      rw [weight_blue I p hxB]
      exact ⟨⟨hxG, Or.inr ⟨h, not_red_of_blue I hxB⟩⟩, by rw [h]; exact lt_irrefl _⟩
  rw [e1, e3] at hsplitA
  rw [e2, e4] at hsplitM
  omega

/-- Main identity: under the matching hypotheses, the assortment revenue of `S` equals the
Stackelberg revenue of `p` under `L'`. -/
theorem revenue_eq_general (I : Instance α) (L : List (α ⊕ (α × ℝ))) (hL : IsAuxOrder I L)
    (S : Finset (Product I)) (p : α → ℝ) (L' : List α) (hL' : I.IsCustomerOrder p L')
    (hA : ∀ x ∈ I.B, x ∈ greedyM I.M L' (I.R ∪ I.B) → ∃ y ∈ S, y.1.1 = x ∧ y.1.2 = p x)
    (hB : ∀ y ∈ S, p y.1.1 ≤ y.1.2) :
    RevenueOrdered.Ratio.revenue (choiceProb I L) (prodRevenue I) S =
      I.stackRevenue p L' := by
  set G' := greedy (auxIndep I) L (scanSet I S)
  set G := greedyM I.M L' (I.R ∪ I.B)
  rcases Nat.eq_zero_or_pos I.B.card with h0 | hpos
  · have hBe : I.B = ∅ := Finset.card_eq_zero.mp h0
    have hSe : S = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro y _
      have := product_blue I y
      rw [hBe] at this
      exact Finset.notMem_empty _ this
    unfold RevenueOrdered.Ratio.revenue Instance.stackRevenue
    rw [hSe, hBe]
    simp
  have hBpos : (I.B.card : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  -- assortment side as a sum over picked products
  have hrevA : RevenueOrdered.Ratio.revenue (choiceProb I L) (prodRevenue I) S =
      ∑ z ∈ G'.filter (fun z => z.isRight = true), auxCost I z := by
    unfold RevenueOrdered.Ratio.revenue
    have h1 : ∀ y ∈ S, choiceProb I L y S * prodRevenue I y =
        (fun z => if z ∈ G' then auxCost I z else 0) (productEmb I y) := by
      intro y _
      unfold choiceProb prodRevenue
      show (if Sum.inr y.1 ∈ G' then 1 / (I.B.card : ℝ) else 0) * ((I.B.card : ℝ) * y.1.2) =
        if Sum.inr y.1 ∈ G' then auxCost I (Sum.inr y.1) else 0
      split_ifs
      · simp only [auxCost, Sum.elim_inr]; field_simp
      · simp
    rw [Finset.sum_congr rfl h1, ← Finset.sum_map S (productEmb I)
      (fun z => if z ∈ G' then auxCost I z else 0), ← Finset.sum_filter]
    have hset : (S.map (productEmb I)).filter (fun z => z ∈ G') =
        G'.filter (fun z => z.isRight = true) := by
      ext z
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hz, hzG⟩
        refine ⟨hzG, ?_⟩
        obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hz
        rfl
      · rintro ⟨hzG, hr⟩
        refine ⟨?_, hzG⟩
        have hzF := (mem_of_mem_greedy _ L _ hzG).1
        unfold scanSet at hzF
        rcases Finset.mem_union.mp hzF with h | h
        · obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp h
          simp at hr
        · exact h
    rw [hset]
  have hmapsA : ∀ z ∈ G'.filter (fun z => z.isRight = true), auxCost I z ∈ costs I := by
    intro z hz
    rw [Finset.mem_filter] at hz
    have hzF := (mem_of_mem_greedy _ L _ hz.1).1
    rcases (mem_scanSet_iff I S z).mp hzF with ⟨a, _, rfl⟩ | ⟨y, _, rfl⟩
    · simp at hz
    · simp only [auxCost, Sum.elim_inr]; exact product_cost I y
  have hmapsM : ∀ e ∈ I.B ∩ G, p e ∈ costs I := by
    intro e he
    rw [Finset.mem_inter] at he
    obtain ⟨y, _, hy1, hy2⟩ := hA e he.1 he.2
    rw [← hy2]; exact product_cost I y
  rw [hrevA]
  unfold Instance.stackRevenue
  rw [← Finset.sum_fiberwise_of_maps_to' hmapsA (fun γ => γ),
    ← Finset.sum_fiberwise_of_maps_to' hmapsM (fun γ => γ)]
  refine Finset.sum_congr rfl ?_
  intro γ _
  rw [Finset.sum_const, Finset.sum_const, Finset.filter_filter]
  rw [count_match I L hL S p L' hL' hA hB γ]

end StackCoreB

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

open RevenueOrdered.Stackelberg StackCoreB StackG6Aux in
theorem solution {α : Type*} (I : Instance α)
    (L : List (α ⊕ (α × ℝ))) (hL : IsAuxOrder I L) (S : Finset (Product I)) (L' : List α)
    (hL' : I.IsCustomerOrder (priceOfAssortment I S) L') :
    RevenueOrdered.Ratio.revenue (choiceProb I L) (prodRevenue I) S =
      I.stackRevenue (priceOfAssortment I S) L' := by
  apply revenue_eq_general I L hL S (priceOfAssortment I S) L' hL'
  · intro x hxB hxG
    obtain ⟨f, hf, hle⟩ := bought_le_cost I _ L' hL' x hxB hxG
    set Q := (S.filter (fun y => y.1.1 = x)).image (fun y => y.1.2) with hQ
    have hQne : Q.Nonempty := by
      by_contra hne
      have : priceOfAssortment I S x = abovePrice I := by
        unfold priceOfAssortment; simp only; rw [dif_neg hne]
      rw [this] at hle
      exact absurd hle (not_le.mpr (abovePrice_gt I f hf))
    have hval : priceOfAssortment I S x = Q.min' hQne := by
      unfold priceOfAssortment; simp only; rw [dif_pos hQne]
    obtain ⟨y, hy, hyq⟩ := Finset.mem_image.mp (Finset.min'_mem Q hQne)
    rw [Finset.mem_filter] at hy
    exact ⟨y, hy.1, hy.2, by rw [hval, hyq]⟩
  · intro y hy
    set Q := (S.filter (fun z => z.1.1 = y.1.1)).image (fun z => z.1.2) with hQ
    have hmem : y.1.2 ∈ Q := Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, rfl⟩, rfl⟩
    have hval : priceOfAssortment I S y.1.1 = Q.min' ⟨_, hmem⟩ := by
      unfold priceOfAssortment; simp only; rw [dif_pos ⟨_, hmem⟩]
    rw [hval]
    exact Finset.min'_le _ _ hmem
