-- Prove2me | solution 1 for RevenueOrdered.Stackelberg.choiceProb_isRegular
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T00:51:33.448206+00:00
-- url     : https://prove2.me/submissions/a6114c51-9887-4157-b522-68fe9ab77a80

import Mathlib
import Definitions.Def_RevenueOrdered_Ratio_Model
import Definitions.Def_RevenueOrdered_Stackelberg_Model
import Definitions.Def_RevenueOrdered_Stackelberg_Greedy
import Definitions.Def_RevenueOrdered_Stackelberg_Instance
import Definitions.Def_RevenueOrdered_Stackelberg_Assortment
import Theorems.Thm_RevenueOrdered_Stackelberg_greedy_card_mono_inter_subset
import Theorems.Thm_RevenueOrdered_Stackelberg_auxIndep_isMatroid

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

namespace StackG4Aux

open RevenueOrdered.Stackelberg StackG0Aux

variable {α : Type*}

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

theorem scanSet_mono (I : Instance α) {S S' : Finset (Product I)} (h : S ⊆ S') :
    scanSet I S ⊆ scanSet I S' := by
  unfold scanSet
  exact Finset.union_subset_union le_rfl (Finset.map_subset_map.mpr h)

theorem greedy_eq (I : Instance α) (M' : Matroid (α ⊕ (α × ℝ)))
    (hM' : ∀ X : Finset (α ⊕ (α × ℝ)), M'.Indep (X : Set (α ⊕ (α × ℝ))) ↔ auxIndep I X)
    (L : List (α ⊕ (α × ℝ))) (F : Finset (α ⊕ (α × ℝ))) :
    greedy (auxIndep I) L F = greedyM M' L F := by
  unfold greedyM
  have : (auxIndep I) = (fun X : Finset (α ⊕ (α × ℝ)) => M'.Indep (X : Set (α ⊕ (α × ℝ)))) := by
    funext X; exact propext (hM' X).symm
  rw [this]

theorem sum_choiceProb (I : Instance α) (L : List (α ⊕ (α × ℝ))) (S : Finset (Product I)) :
    ∑ x ∈ S, choiceProb I L x S =
      ((greedy (auxIndep I) L (scanSet I S)).filter (fun z => z.isRight = true)).card *
        (1 / (I.B.card : ℝ)) := by
  set G := greedy (auxIndep I) L (scanSet I S)
  unfold choiceProb
  have h1 : ∀ x ∈ S, (if Sum.inr x.1 ∈ greedy (auxIndep I) L
      (I.R.map Function.Embedding.inl ∪ S.map (productEmb I)) then 1 / (I.B.card : ℝ) else 0) =
      (fun z => if z ∈ G then 1 / (I.B.card : ℝ) else 0) (productEmb I x) := by
    intro x _; rfl
  rw [Finset.sum_congr rfl h1, ← Finset.sum_map S (productEmb I)
    (fun z => if z ∈ G then 1 / (I.B.card : ℝ) else 0)]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
  have hset : (S.map (productEmb I)).filter (fun z => z ∈ G) =
      G.filter (fun z => z.isRight = true) := by
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

end StackG4Aux

open RevenueOrdered.Stackelberg StackG0Aux StackG4Aux in
theorem solution {α : Type*} (I : Instance α) (L : List (α ⊕ (α × ℝ)))
    (hL : IsAuxOrder I L) :
    RevenueOrdered.Ratio.IsRegular (choiceProb I L) := by
  obtain ⟨M', hM'E, hM'⟩ := auxIndep_isMatroid I
  have hcard : ∀ S : Finset (Product I),
      ((greedy (auxIndep I) L (scanSet I S)).filter (fun z => z.isRight = true)).card ≤
        I.B.card := by
    intro S
    set G := greedy (auxIndep I) L (scanSet I S)
    have hGind : auxIndep I G := by
      rw [← hM', show G = greedyM M' L (scanSet I S) from greedy_eq I M' hM' L _]
      exact (greedyM_isBasis M' L (scanSet I S) (by
        rw [hM'E]; exact_mod_cast scanSet_subset I S)).indep
    apply Finset.card_le_card_of_injOn (fun z => Sum.elim id Prod.fst z)
    · intro z hz
      rw [Finset.mem_coe, Finset.mem_filter] at hz
      have hzA := hGind.1 hz.1
      unfold auxGround at hzA
      rcases Finset.mem_union.mp hzA with h | h
      · obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp h
        simp at hz
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp h
        unfold products at hy
        exact (Finset.mem_product.mp hy).1
    · intro z hz w hw hzw
      rw [Finset.mem_coe, Finset.mem_filter] at hz hw
      have hzA := hGind.1 hz.1
      have hwA := hGind.1 hw.1
      unfold auxGround at hzA hwA
      rcases Finset.mem_union.mp hzA with h | h
      · obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp h; simp at hz
      rcases Finset.mem_union.mp hwA with h' | h'
      · obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp h'; simp at hw
      obtain ⟨⟨e, q⟩, hy, rfl⟩ := Finset.mem_map.mp h
      obtain ⟨⟨e', q'⟩, hy', rfl⟩ := Finset.mem_map.mp h'
      simp only [Function.Embedding.inr_apply, Sum.elim_inr] at hzw
      subst hzw
      unfold products at hy hy'
      rw [Finset.mem_product] at hy hy'
      exact Finset.card_le_one.mp (hGind.2.1 e hy.1) _
        (Finset.mem_filter.mpr ⟨hz.1, q, hy.2, rfl⟩) _
        (Finset.mem_filter.mpr ⟨hw.1, q', hy'.2, rfl⟩)
  have hsum_le : ∀ S : Finset (Product I), ∑ x ∈ S, choiceProb I L x S ≤ 1 := by
    intro S
    rw [sum_choiceProb]
    rcases Nat.eq_zero_or_pos I.B.card with h0 | hpos
    · rw [h0]; simp
    · have hBpos : (0 : ℝ) < I.B.card := by exact_mod_cast hpos
      rw [mul_one_div, div_le_one hBpos]
      exact_mod_cast hcard S
  have hlemma := fun (S S' : Finset (Product I)) (h : S ⊆ S') =>
    greedy_card_mono_inter_subset M' (auxGround I) hM'E.symm L (by convert hL.1) (scanSet I S)
      (scanSet I S') (scanSet_mono I h) (scanSet_subset I S')
  have hlemma2 : ∀ (S S' : Finset (Product I)), S ⊆ S' → ∀ z, z ∈ scanSet I S →
      z ∈ greedyM M' L (scanSet I S') → z ∈ greedyM M' L (scanSet I S) := by
    intro S S' h z hz hz'
    apply (hlemma S S' h).2
    convert Finset.mem_inter.mpr ⟨hz, hz'⟩
  refine ⟨?_, ?_, ?_, hsum_le, ?_, ?_⟩
  · intro x S
    unfold choiceProb
    split_ifs
    · positivity
    · exact le_rfl
  · intro S
    unfold RevenueOrdered.Ratio.noPurchase
    linarith [hsum_le S]
  · intro x S hx
    unfold choiceProb
    rw [if_neg]
    intro hmem
    have hF := (mem_of_mem_greedy _ L _ hmem).1
    rcases Finset.mem_union.mp hF with h | h
    · obtain ⟨a, _, ha⟩ := Finset.mem_map.mp h
      simp at ha
    · obtain ⟨y, hy, hyx⟩ := Finset.mem_map.mp h
      have : y = x := by
        apply Subtype.ext
        simpa [productEmb] using hyx
      exact hx (this ▸ hy)
  · intro S S' x hSS' hx
    unfold choiceProb
    by_cases h' : Sum.inr x.1 ∈ greedy (auxIndep I) L
        (I.R.map Function.Embedding.inl ∪ S'.map (productEmb I))
    · have hin : Sum.inr x.1 ∈ scanSet I S := by
        unfold scanSet
        exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨x, hx, rfl⟩)
      have := hlemma2 S S' hSS' _ hin (by
        rw [← greedy_eq I M' hM']; exact h')
      rw [← greedy_eq I M' hM'] at this
      have this' : Sum.inr x.1 ∈ greedy (auxIndep I) L
          (I.R.map Function.Embedding.inl ∪ S.map (productEmb I)) := this
      rw [if_pos h', if_pos this']
    · rw [if_neg h']
      split_ifs
      · positivity
      · exact le_rfl
  · intro S S' hSS'
    unfold RevenueOrdered.Ratio.noPurchase
    rw [sum_choiceProb, sum_choiceProb]
    have h2 := hlemma2 S S' hSS'
    have h1 := (hlemma S S' hSS').1
    rw [← greedy_eq I M' hM', ← greedy_eq I M' hM'] at h1
    simp only [← greedy_eq I M' hM'] at h2
    set G := greedy (auxIndep I) L (scanSet I S)
    set G' := greedy (auxIndep I) L (scanSet I S')
    have hred : G'.filter (fun z => ¬ z.isRight = true) ⊆ G.filter (fun z => ¬ z.isRight = true) := by
      intro z hz
      rw [Finset.mem_filter] at hz ⊢
      refine ⟨?_, hz.2⟩
      refine h2 z ?_ hz.1
      have hzF := (mem_of_mem_greedy _ L _ hz.1).1
      unfold scanSet at hzF ⊢
      rcases Finset.mem_union.mp hzF with h | h
      · exact Finset.mem_union_left _ h
      · obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp h
        exact absurd rfl hz.2
    have hc1 := Finset.card_filter_add_card_filter_not (s := G) (fun z => z.isRight = true)
    have hc2 := Finset.card_filter_add_card_filter_not (s := G') (fun z => z.isRight = true)
    have hc3 := Finset.card_le_card hred
    have hle : (G.filter (fun z => z.isRight = true)).card ≤
        (G'.filter (fun z => z.isRight = true)).card := by omega
    have hle' : ((G.filter (fun z => z.isRight = true)).card : ℝ) ≤
        (G'.filter (fun z => z.isRight = true)).card := by exact_mod_cast hle
    have hnn : (0 : ℝ) ≤ 1 / (I.B.card : ℝ) := by positivity
    nlinarith
