-- Prove2me | solution 1 for PancakeHard.property_9
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-10T07:47:53.532169+00:00
-- url     : https://prove2.me/submissions/3ac16769-2c8e-457c-9176-ac6982f1a57d

import Mathlib
import Definitions.Def_PancakeHard_Variable
import Theorems.Thm_PancakeHard_property_4
import Theorems.Thm_PancakeHard_property_6
import Theorems.Thm_PancakeHard_property_7
import Theorems.Thm_PancakeHard_property_8

set_option autoImplicit false

namespace PancakeHard

lemma EfficientFlip.length_eq {S S' : List ℕ} (h : EfficientFlip S S') :
    S.length = S'.length := by
  obtain ⟨⟨r, hr1, hr2, rfl⟩, _⟩ := h
  simp [flip, List.length_take, List.length_drop, List.length_reverse, List.length_append]
  omega

lemma EfficientFlip.perm {S S' : List ℕ} (h : EfficientFlip S S') : S.Perm S' := by
  obtain ⟨⟨r, _, _, rfl⟩, _⟩ := h
  have h1 : ((S.take r).reverse ++ S.drop r).Perm (S.take r ++ S.drop r) :=
    (List.reverse_perm (S.take r)).append_right (S.drop r)
  simpa [flip, List.take_append_drop] using h1.symm

lemma IsEfficientPath.refl (S : List ℕ) : IsEfficientPath [S] S S :=
  ⟨rfl, rfl, List.IsChain.singleton _⟩

private theorem length_const_chain (l : List (List ℕ)) (hch : l.IsChain EfficientFlip)
    (A B : List ℕ) (hA : A ∈ l) (hB : B ∈ l) : A.length = B.length := by
  match l with
  | [] => cases hA
  | [_] =>
      simp at hA hB; subst hA; subst hB; rfl
  | C :: D :: t =>
      rw [List.isChain_cons_cons] at hch
      have hCD := EfficientFlip.length_eq hch.1
      have hrest : ∀ (A B : List ℕ), A ∈ D :: t → B ∈ D :: t → A.length = B.length :=
        fun A B hA hB => length_const_chain (D :: t) hch.2 A B hA hB
      have hA' := (List.mem_cons).1 hA
      have hB' := (List.mem_cons).1 hB
      rcases hA' with rfl | hA' <;> rcases hB' with rfl | hB'
      · rfl
      · exact hCD.trans (hrest D B (@List.mem_cons_self _ D t) hB')
      · exact (hrest D A (@List.mem_cons_self _ D t) hA').symm.trans hCD.symm
      · exact hrest A B hA' hB'

private theorem perm_const_chain (l : List (List ℕ)) (hch : l.IsChain EfficientFlip)
    (A B : List ℕ) (hA : A ∈ l) (hB : B ∈ l) : A.Perm B := by
  match l with
  | [] => cases hA
  | [_] =>
      simp at hA hB; subst hA; subst hB; exact .refl _
  | C :: D :: t =>
      rw [List.isChain_cons_cons] at hch
      have hCD := EfficientFlip.perm hch.1
      have hrest : ∀ (A B : List ℕ), A ∈ D :: t → B ∈ D :: t → A.Perm B :=
        fun A B hA hB => perm_const_chain (D :: t) hch.2 A B hA hB
      have hA' := (List.mem_cons).1 hA
      have hB' := (List.mem_cons).1 hB
      rcases hA' with rfl | hA' <;> rcases hB' with rfl | hB'
      · exact .refl _
      · exact hCD.trans (hrest D B (@List.mem_cons_self _ D t) hB')
      · exact (hrest D A (@List.mem_cons_self _ D t) hA').symm.trans hCD.symm
      · exact hrest A B hA' hB'

lemma IsEfficientPath.mem_start (π : List (List ℕ)) (S T : List ℕ)
    (h : IsEfficientPath π S T) : S ∈ π := by
  obtain ⟨hhd, _, _⟩ := h
  cases π with
  | nil => simp at hhd
  | cons a t =>
    simp at hhd ⊢
    exact Or.inl hhd.symm

lemma IsEfficientPath.mem_end (π : List (List ℕ)) (S T : List ℕ)
    (h : IsEfficientPath π S T) : T ∈ π := by
  obtain ⟨_, htl, _⟩ := h
  obtain ⟨ys, hπ⟩ := List.getLast?_eq_some_iff.mp htl
  simp [hπ]

lemma IsEfficientPath.length_eq (π : List (List ℕ)) (S T : List ℕ)
    (h : IsEfficientPath π S T) : S.length = T.length :=
  length_const_chain π h.2.2 S T (IsEfficientPath.mem_start π S T h)
    (IsEfficientPath.mem_end π S T h)

lemma IsStack_of_IsEfficientPath (π : List (List ℕ)) (S T : List ℕ)
    (hS : IsStack S) (h : IsEfficientPath π S T) : IsStack T := by
  have hp := perm_const_chain π h.2.2 S T (IsEfficientPath.mem_start π S T h)
    (IsEfficientPath.mem_end π S T h)
  have hlen := IsEfficientPath.length_eq π S T h
  unfold IsStack at hS ⊢
  exact hp.symm.trans (hS.trans (by rw [hlen]))


/-- Concatenate efficient paths sharing midpoint `T`. Avoids `subst` on `S`/`T`. -/

lemma IsEfficientPath.trans (π ρ : List (List ℕ)) (S T U : List ℕ)
    (hπ : IsEfficientPath π S T) (hρ : IsEfficientPath ρ T U) :
    IsEfficientPath (π ++ ρ.tail) S U := by
  obtain ⟨hπhd, hπtl, hπch⟩ := hπ
  obtain ⟨hρhd, hρtl, hρch⟩ := hρ
  cases ρ with
  | nil => simp at hρhd
  | cons b ρt =>
    have hb : b = T := Option.some_injective _ (by simpa using hρhd)
    cases π with
    | nil => simp at hπhd
    | cons a πt =>
      have ha : a = S := Option.some_injective _ (by simpa using hπhd)
      refine ⟨?hd, ?tl, ?ch⟩
      · simp [ha]
      · cases ρt with
        | nil =>
          have hUb : b = U := Option.some_injective _ (by simpa using hρtl)
          have : U = T := hUb.symm.trans hb
          simpa [this] using hπtl
        | cons c ρu =>
          have hget : ((a :: πt) ++ (c :: ρu)).getLast? = (c :: ρu).getLast? :=
            List.getLast?_append_of_ne_nil _ (by simp)
          have hρlast : (c :: ρu).getLast? = some U := by
            -- getLast (b::c::ρu) = getLast (c::ρu)
            simpa [List.getLast?_cons_cons, hb] using hρtl
          exact hget.symm ▸ hρlast
      · cases ρt with
        | nil => simpa using hπch
        | cons c ρu =>
          have hchT : List.IsChain EfficientFlip (T :: c :: ρu) := by
            simpa [hb] using hρch
          have hTC : EfficientFlip T c := (List.isChain_cons_cons.1 hchT).1
          have hchRest : List.IsChain EfficientFlip (c :: ρu) :=
            (List.isChain_cons_cons.1 hchT).2
          refine List.IsChain.append hπch hchRest ?_
          intro x hx y hy
          have hxT : x = T := by
            have h1 : (a :: πt).getLast? = some x := Option.mem_def.mp hx
            exact Option.some_injective _ (h1.symm.trans hπtl)
          have hyC : y = c := by
            have h1 : (c :: ρu).head? = some y := Option.mem_def.mp hy
            exact Option.some_injective _ (h1.symm.trans rfl)
          rw [hxT, hyC]
          exact hTC

private lemma isChain_of_append_left {α : Type*} {R : α → α → Prop}
    {l₁ l₂ : List α} (h : (l₁ ++ l₂).IsChain R) : l₁.IsChain R :=
  (List.isChain_append.1 h).1

private lemma isChain_drop_prefix {α : Type*} {R : α → α → Prop}
    {l₁ : List α} {x : α} {l₂ : List α}
    (h : (l₁ ++ x :: l₂).IsChain R) : (x :: l₂).IsChain R :=
  (List.isChain_append.1 h).2.1

lemma IsEfficientPath.split (π : List (List ℕ)) (S T U : List ℕ)
    (h : IsEfficientPath π S U) (hT : T ∈ π) :
    ∃ π1 π2, IsEfficientPath π1 S T ∧ IsEfficientPath π2 T U ∧ π = π1 ++ π2.tail := by
  obtain ⟨hhd, htl, hch⟩ := h
  obtain ⟨l₁, l₂, rfl⟩ := (List.mem_iff_append).1 hT
  refine ⟨l₁ ++ [T], T :: l₂, ⟨?hd1, by simp, ?ch1⟩,
    ⟨rfl, ?tl2, isChain_drop_prefix (l₁ := l₁) hch⟩, by simp⟩
  · cases l₁ with
    | nil => simp at hhd ⊢; exact hhd
    | cons a l => simp at hhd ⊢; exact hhd
  · have h' : (l₁ ++ [T] ++ l₂).IsChain EfficientFlip := by
      simpa [List.append_assoc] using hch
    exact isChain_of_append_left (l₂ := l₂) h'
  · cases l₂ with
    | nil =>
      have : (l₁ ++ [T]).getLast? = some U := by simpa using htl
      simpa using this
    | cons b l₂ =>
      simpa [List.getLast?_append, List.getLast?_cons] using htl

private lemma mem_concat_of_second (π1 : List (List ℕ)) (T : List ℕ) (t : List (List ℕ))
    (U : List ℕ) (hend : π1.getLast? = some T) (hU : U ∈ T :: t) : U ∈ π1 ++ t := by
  rcases (List.mem_cons).1 hU with rfl | hU
  · obtain ⟨ys, hπ1⟩ := List.getLast?_eq_some_iff.mp hend
    simp [hπ1]
  · exact List.mem_append_right _ hU

private lemma path_retarget_identity (π : List (List ℕ)) (S T : List ℕ)
    (hlen : S.length = T.length)
    (h : IsEfficientPath π T (identity S.length)) :
    IsEfficientPath π T (identity T.length) := by
  obtain ⟨hd, tl, ch⟩ := h
  refine ⟨hd, ?_, ch⟩
  simpa [hlen] using tl

lemma LeadsTo.trans_singleton {S T : List ℕ} {𝕋 : Set (List ℕ)}
    (hST : LeadsTo S {T}) (hT : LeadsTo T 𝕋) : LeadsTo S 𝕋 := by
  obtain ⟨hST1, hST2⟩ := hST
  obtain ⟨hT1, hT2⟩ := hT
  refine ⟨?fwd, ?bwd⟩
  · intro U hU
    obtain ⟨π1, hπ1⟩ := hST1 T (Set.mem_singleton _)
    obtain ⟨π2, hπ2⟩ := hT1 U hU
    exact ⟨π1 ++ π2.tail, IsEfficientPath.trans π1 π2 S T U hπ1 hπ2⟩
  · intro π hπ
    obtain ⟨T', hTmem, hTin⟩ := hST2 π hπ
    have hEqT : T' = T := Set.mem_singleton_iff.mp hTmem
    rw [hEqT] at hTin
    obtain ⟨π1, π2, hπ1, hπ2, hEq⟩ :=
      IsEfficientPath.split π S T (identity S.length) hπ hTin
    have hlen : S.length = T.length := IsEfficientPath.length_eq π1 S T hπ1
    have hπ2' := path_retarget_identity π2 S T hlen hπ2
    obtain ⟨U, hU, hUin⟩ := hT2 π2 hπ2'
    refine ⟨U, hU, ?_⟩
    rw [hEq]
    have hend : π1.getLast? = some T := hπ1.2.1
    cases π2 with
    | nil =>
      have := hπ2.1; simp at this
    | cons b t =>
      have hb : b = T := Option.some_injective _ (by simpa using hπ2.1)
      rw [hb] at hUin
      exact mem_concat_of_second π1 T t U hend hUin

lemma LeadsTo.pair_union {S A B : List ℕ} {𝕋₁ 𝕋₂ : Set (List ℕ)}
    (hS : LeadsTo S {A, B}) (hA : LeadsTo A 𝕋₁) (hB : LeadsTo B 𝕋₂) :
    LeadsTo S (𝕋₁ ∪ 𝕋₂) := by
  obtain ⟨hS1, hS2⟩ := hS
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  refine ⟨?fwd, ?bwd⟩
  · intro U hU
    rcases (Set.mem_union U 𝕋₁ 𝕋₂).mp hU with hU | hU
    · obtain ⟨π1, hπ1⟩ := hS1 A (by simp)
      obtain ⟨π2, hπ2⟩ := hA1 U hU
      exact ⟨π1 ++ π2.tail, IsEfficientPath.trans π1 π2 S A U hπ1 hπ2⟩
    · obtain ⟨π1, hπ1⟩ := hS1 B (by simp)
      obtain ⟨π2, hπ2⟩ := hB1 U hU
      exact ⟨π1 ++ π2.tail, IsEfficientPath.trans π1 π2 S B U hπ1 hπ2⟩
  · intro π hπ
    obtain ⟨W, hWmem, hWin⟩ := hS2 π hπ
    have hcases : W = A ∨ W = B := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hWmem
    rcases hcases with hWA | hWB
    · rw [hWA] at hWin
      obtain ⟨π1, π2, hπ1, hπ2, hEq⟩ :=
        IsEfficientPath.split π S A (identity S.length) hπ hWin
      have hlen : S.length = A.length := IsEfficientPath.length_eq π1 S A hπ1
      have hπ2' := path_retarget_identity π2 S A hlen hπ2
      obtain ⟨U, hU, hUin⟩ := hA2 π2 hπ2'
      refine ⟨U, Or.inl hU, ?_⟩
      rw [hEq]
      have hend : π1.getLast? = some A := hπ1.2.1
      cases π2 with
      | nil =>
        have := hπ2.1; simp at this
      | cons b t =>
        have hb : b = A := Option.some_injective _ (by simpa using hπ2.1)
        rw [hb] at hUin
        exact mem_concat_of_second π1 A t U hend hUin
    · rw [hWB] at hWin
      obtain ⟨π1, π2, hπ1, hπ2, hEq⟩ :=
        IsEfficientPath.split π S B (identity S.length) hπ hWin
      have hlen : S.length = B.length := IsEfficientPath.length_eq π1 S B hπ1
      have hπ2' := path_retarget_identity π2 S B hlen hπ2
      obtain ⟨U, hU, hUin⟩ := hB2 π2 hπ2'
      refine ⟨U, Or.inr hU, ?_⟩
      rw [hEq]
      have hend : π1.getLast? = some B := hπ1.2.1
      cases π2 with
      | nil =>
        have := hπ2.1; simp at this
      | cons b t =>
        have hb : b = B := Option.some_injective _ (by simpa using hπ2.1)
        rw [hb] at hUin
        exact mem_concat_of_second π1 B t U hend hUin

lemma LeadsTo.pair_same {S A B : List ℕ} {𝕋 : Set (List ℕ)}
    (hS : LeadsTo S {A, B}) (hA : LeadsTo A 𝕋) (hB : LeadsTo B 𝕋) :
    LeadsTo S 𝕋 := by
  simpa [Set.union_self] using LeadsTo.pair_union hS hA hB


lemma offset_add (p : ℤ) (c : ℕ) (hp : -2 ≤ p) (hc : 2 ≤ c) :
    (p + (c : ℤ)).toNat = (p + 2).toNat + (c - 2) := by
  have hp' : (0 : ℤ) ≤ p + 2 := by linarith
  have hc' : (0 : ℤ) ≤ (c : ℤ) - 2 := by omega
  have hsplit : p + (c : ℤ) = (p + 2) + ((c : ℤ) - 2) := by omega
  have hcn : (c : ℤ) - 2 = ((c - 2 : ℕ) : ℤ) := by omega
  rw [hsplit, Int.toNat_add hp' hc', hcn, Int.toNat_natCast]

lemma offset_p14 (p : ℤ) (hp : -2 ≤ p) :
    (p + 14).toNat = (p + 2).toNat + 12 := by
  simpa using offset_add p 14 hp (by decide)

lemma IsStack_of_LeadsTo_singleton {S T : List ℕ}
    (hS : IsStack S) (h : LeadsTo S {T}) : IsStack T := by
  obtain ⟨π, hπ⟩ := h.1 T (Set.mem_singleton _)
  exact IsStack_of_IsEfficientPath π S T hS hπ

lemma LeadsTo.refl (S0 : List ℕ) : LeadsTo S0 {S0} := by
  refine ⟨?_, ?_⟩
  · intro T hT
    have hEq : T = S0 := Set.mem_singleton_iff.mp hT
    cases hEq
    exact ⟨[S0], IsEfficientPath.refl S0⟩
  · intro π hπ
    exact ⟨S0, Set.mem_singleton _, IsEfficientPath.mem_start π S0 (identity S0.length) hπ⟩

lemma leadsTo_open_keys (pΛ m : ℕ) (ks : List ℕ) (O I : Finset ℕ) (mid : List ℕ)
    (hO : O ⊆ Finset.Icc 1 m) (hI : I ⊆ Finset.Icc 1 m) (hOI : Disjoint O I)
    (hks : ∀ j ∈ ks, j ∈ Finset.Icc 1 m) (hNodup : ks.Nodup)
    (hDisjO : ∀ j ∈ ks, j ∉ O) (hDisjI : ∀ j ∈ ks, j ∉ I)
    (hStack : IsStack (ks.map (litKey pΛ) ++ mid ++ literals pΛ m O I)) :
    LeadsTo (ks.map (litKey pΛ) ++ mid ++ literals pΛ m O I)
      {mid ++ literals pΛ m (O ∪ ks.toFinset) I} := by
  induction ks generalizing O with
  | nil =>
    simpa [List.toFinset] using LeadsTo.refl (mid ++ literals pΛ m O I)
  | cons i rest ih =>
    have hi : i ∈ Finset.Icc 1 m := hks i List.mem_cons_self
    have hiO : i ∉ O := hDisjO i List.mem_cons_self
    have hiI : i ∉ I := hDisjI i List.mem_cons_self
    have hrest_nodup : rest.Nodup := List.Nodup.of_cons hNodup
    have hi_notin_rest : i ∉ rest := (List.nodup_cons.1 hNodup).1
    have hStack' :
        IsStack (litKey pΛ i :: (rest.map (litKey pΛ) ++ mid) ++ literals pΛ m O I) := by
      simpa [List.map_cons, List.append_assoc] using hStack
    have hmid1 :
        LeadsTo (litKey pΛ i :: (rest.map (litKey pΛ) ++ mid) ++ literals pΛ m O I)
          {rest.map (litKey pΛ) ++ mid ++ literals pΛ m (insert i O) I} :=
      (property_8 pΛ m O I (rest.map (litKey pΛ) ++ mid) hO hI hOI).1 i hi hiO hiI hStack'
    have hStack2 :
        IsStack (rest.map (litKey pΛ) ++ mid ++ literals pΛ m (insert i O) I) :=
      IsStack_of_LeadsTo_singleton hStack' hmid1
    have hO' : insert i O ⊆ Finset.Icc 1 m := Finset.insert_subset hi hO
    have hOI' : Disjoint (insert i O) I :=
      (Finset.disjoint_insert_left).2 ⟨hiI, hOI⟩
    have hDisjO' : ∀ j ∈ rest, j ∉ insert i O := by
      intro j hj
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun hji => hi_notin_rest (hji ▸ hj), hDisjO j (List.mem_cons_of_mem _ hj)⟩
    have hDisjI' : ∀ j ∈ rest, j ∉ I := fun j hj =>
      hDisjI j (List.mem_cons_of_mem _ hj)
    have hks' : ∀ j ∈ rest, j ∈ Finset.Icc 1 m := fun j hj =>
      hks j (List.mem_cons_of_mem _ hj)
    have ih' := ih (insert i O) hO' hOI' hks' hrest_nodup hDisjO' hDisjI' hStack2
    have hset : insert i O ∪ rest.toFinset = O ∪ (i :: rest).toFinset := by
      ext x
      simp [List.mem_toFinset, Finset.mem_union, Finset.mem_insert]
    have ih'' :
        LeadsTo (rest.map (litKey pΛ) ++ mid ++ literals pΛ m (insert i O) I)
          {mid ++ literals pΛ m (O ∪ (i :: rest).toFinset) I} := by
      simpa [hset] using ih'
    have hmid1' :
        LeadsTo ((i :: rest).map (litKey pΛ) ++ mid ++ literals pΛ m O I)
          {rest.map (litKey pΛ) ++ mid ++ literals pΛ m (insert i O) I} := by
      simpa [List.map_cons, List.append_assoc] using hmid1
    exact LeadsTo.trans_singleton hmid1' ih''

lemma leadsTo_open_keys_reverse (pΛ m : ℕ) (ks : List ℕ) (O I : Finset ℕ) (mid : List ℕ)
    (hO : O ⊆ Finset.Icc 1 m) (hI : I ⊆ Finset.Icc 1 m) (hOI : Disjoint O I)
    (hks : ∀ j ∈ ks, j ∈ Finset.Icc 1 m) (hNodup : ks.Nodup)
    (hDisjO : ∀ j ∈ ks, j ∉ O) (hDisjI : ∀ j ∈ ks, j ∉ I)
    (hStack : IsStack (ks.reverse.map (litKey pΛ) ++ mid ++ literals pΛ m O I)) :
    LeadsTo (ks.reverse.map (litKey pΛ) ++ mid ++ literals pΛ m O I)
      {mid ++ literals pΛ m (O ∪ ks.toFinset) I} := by
  have h1 := leadsTo_open_keys pΛ m ks.reverse O I mid hO hI hOI
    (fun j hj => hks j (List.mem_reverse.mp hj)) (List.nodup_reverse.mpr hNodup)
    (fun j hj => hDisjO j (List.mem_reverse.mp hj))
    (fun j hj => hDisjI j (List.mem_reverse.mp hj)) hStack
  simpa [List.toFinset_reverse] using h1


lemma varV_eq (pΛ : ℕ) (P N : List ℕ) (p : ℤ) :
    varV pΛ P N p =
      hookG (p + 2).toNat ++ forkE (p + 14).toNat ++ P.map (litKey pΛ) ++
        [hookPut (p + 2).toNat] ++ N.map (litKey pΛ) ++ forkF (p + 14).toNat ++
        hookH (p + 2).toNat := rfl

lemma varNu_eq (p : ℤ) : varNu p = hookTake (p + 2).toNat := rfl

lemma varV1_eq (pΛ : ℕ) (N : List ℕ) (p : ℤ) :
    varV1 pΛ N p =
      hookG'' (p + 2).toNat ++ N.map (litKey pΛ) ++ forkF1 (p + 14).toNat ++
        hookH'' (p + 2).toNat := rfl

lemma varV2_eq (pΛ : ℕ) (P : List ℕ) (p : ℤ) :
    varV2 pΛ P p =
      hookG'' (p + 2).toNat ++ P.reverse.map (litKey pΛ) ++ forkF2 (p + 14).toNat ++
        hookH'' (p + 2).toNat := rfl

lemma append_reverse_mid {α : Type*} (A : List α) (x : α) (B : List α) :
    (A ++ x :: B).reverse = B.reverse ++ x :: A.reverse := by
  simp [List.reverse_append, List.reverse_cons, List.append_assoc]

/-- Property 9 (a), with explicit disjointness side conditions (implied by IsStack). -/
lemma prop9_a
    (pΛ m : ℕ) (p : ℤ) (_hp : -2 ≤ p) (P N : List ℕ) (O I : Finset ℕ) (X Y : List ℕ)
    (hP : P.Nodup) (hN : N.Nodup)
    (hPm : ∀ j ∈ P, j ∈ Finset.Icc 1 m) (hNm : ∀ j ∈ N, j ∈ Finset.Icc 1 m)
    (_hPN : P.Disjoint N) (hO : O ⊆ Finset.Icc 1 m) (hI : I ⊆ Finset.Icc 1 m)
    (hOI : Disjoint O I)
    (hPO : ∀ j ∈ P, j ∉ O) (hPI : ∀ j ∈ P, j ∉ I)
    (hNO : ∀ j ∈ N, j ∉ O) (hNI : ∀ j ∈ N, j ∉ I)
    (hStack0 : IsStack (varNu p :: X ++ varV pΛ P N p ++ Y ++ literals pΛ m O I)) :
    LeadsTo (varNu p :: X ++ varV pΛ P N p ++ Y ++ literals pΛ m O I)
      {X ++ varV1 pΛ N p ++ Y ++ literals pΛ m (O ∪ P.toFinset) I,
        X ++ varV2 pΛ P p ++ Y ++ literals pΛ m (O ∪ N.toFinset) I} := by
  set ph : ℕ := (p + 2).toNat
  set pf : ℕ := (p + 14).toNat
  set Zh : List ℕ := Y ++ literals pΛ m O I
  set Yh : List ℕ :=
    forkE pf ++ P.map (litKey pΛ) ++ [hookPut ph] ++ N.map (litKey pΛ) ++ forkF pf
  have hArr :
      varNu p :: X ++ varV pΛ P N p ++ Y ++ literals pΛ m O I =
        hookTake ph :: X ++ hookG ph ++ Yh ++ hookH ph ++ Zh := by
    simp [varNu_eq, varV_eq, Yh, Zh, ph, pf, List.append_assoc, List.cons_append]
  rw [hArr] at hStack0 ⊢
  -- Hook.a
  have hHook : LeadsTo (hookTake ph :: X ++ hookG ph ++ Yh ++ hookH ph ++ Zh)
      {Yh ++ hookG' ph ++ X.reverse ++ hookH' ph ++ Zh} :=
    (property_6 ph X Yh Zh).1 hStack0
  set T0 : List ℕ := Yh ++ hookG' ph ++ X.reverse ++ hookH' ph ++ Zh
  have hStackT0 : IsStack T0 := IsStack_of_LeadsTo_singleton hStack0 hHook
  set Xf : List ℕ := P.map (litKey pΛ) ++ [hookPut ph] ++ N.map (litKey pΛ)
  set Zf : List ℕ := hookG' ph ++ X.reverse ++ hookH' ph ++ Zh
  have hT0eq : T0 = forkE pf ++ Xf ++ forkF pf ++ Zf := by
    simp [T0, Yh, Xf, Zf, List.append_assoc]
  have hStackT0' : IsStack (forkE pf ++ Xf ++ forkF pf ++ Zf) := by
    rwa [hT0eq] at hStackT0
  have hFork : LeadsTo (forkE pf ++ Xf ++ forkF pf ++ Zf)
      {Xf ++ forkF1 pf ++ Zf, Xf.reverse ++ forkF2 pf ++ Zf} :=
    (property_7 pf Xf Zf).1 hStackT0'
  set S1 : List ℕ := Xf ++ forkF1 pf ++ Zf
  set S2 : List ℕ := Xf.reverse ++ forkF2 pf ++ Zf
  have hS1stack : IsStack S1 := by
    obtain ⟨π, hπ⟩ := hFork.1 S1 (by simp [S1])
    exact IsStack_of_IsEfficientPath π _ _ hStackT0' hπ
  have hS2stack : IsStack S2 := by
    obtain ⟨π, hπ⟩ := hFork.1 S2 (by simp [S2])
    exact IsStack_of_IsEfficientPath π _ _ hStackT0' hπ
  -- ----- Path S1: open P keys, then Hook.b -----
  set mid1 : List ℕ :=
    [hookPut ph] ++ N.map (litKey pΛ) ++ forkF1 pf ++ hookG' ph ++ X.reverse ++ hookH' ph ++ Y
  have hS1arr : S1 = P.map (litKey pΛ) ++ mid1 ++ literals pΛ m O I := by
    simp [S1, Xf, Zf, Zh, mid1, List.append_assoc]
  have hOpenP : LeadsTo S1 {mid1 ++ literals pΛ m (O ∪ P.toFinset) I} := by
    simpa [hS1arr] using
      leadsTo_open_keys pΛ m P O I mid1 hO hI hOI hPm hP hPO hPI (by simpa [hS1arr] using hS1stack)
  have hStackAfterP : IsStack (mid1 ++ literals pΛ m (O ∪ P.toFinset) I) :=
    IsStack_of_LeadsTo_singleton hS1stack hOpenP
  -- mid1 ++ Λ' = put :: (N.map ++ F1) ++ G' ++ X.reverse ++ H' ++ Y ++ Λ'
  set Xh1 : List ℕ := N.map (litKey pΛ) ++ forkF1 pf
  have hmid1eq :
      mid1 ++ literals pΛ m (O ∪ P.toFinset) I =
        hookPut ph :: Xh1 ++ hookG' ph ++ X.reverse ++ hookH' ph ++
          (Y ++ literals pΛ m (O ∪ P.toFinset) I) := by
    simp [mid1, Xh1, List.append_assoc]
  have hStackPut : IsStack
      (hookPut ph :: Xh1 ++ hookG' ph ++ X.reverse ++ hookH' ph ++
        (Y ++ literals pΛ m (O ∪ P.toFinset) I)) := by
    rwa [← hmid1eq]
  have hHookB : LeadsTo
      (hookPut ph :: Xh1 ++ hookG' ph ++ X.reverse ++ hookH' ph ++
        (Y ++ literals pΛ m (O ∪ P.toFinset) I))
      {X ++ hookG'' ph ++ Xh1 ++ hookH'' ph ++
        (Y ++ literals pΛ m (O ∪ P.toFinset) I)} := by
    -- property_6.b needs Y.reverse in the middle; here middle is X.reverse so Y_arg = X
    simpa using (property_6 ph Xh1 X (Y ++ literals pΛ m (O ∪ P.toFinset) I)).2.1 hStackPut
  have hS1final :
      X ++ hookG'' ph ++ Xh1 ++ hookH'' ph ++ (Y ++ literals pΛ m (O ∪ P.toFinset) I) =
        X ++ varV1 pΛ N p ++ Y ++ literals pΛ m (O ∪ P.toFinset) I := by
    simp [varV1_eq, Xh1, ph, pf, List.append_assoc]
  have hPath1 : LeadsTo S1
      {X ++ varV1 pΛ N p ++ Y ++ literals pΛ m (O ∪ P.toFinset) I} := by
    have hHookB' : LeadsTo (mid1 ++ literals pΛ m (O ∪ P.toFinset) I)
        {X ++ varV1 pΛ N p ++ Y ++ literals pΛ m (O ∪ P.toFinset) I} := by
      rw [hmid1eq]
      have hset := congrArg (fun t : List ℕ => ({t} : Set (List ℕ))) hS1final
      rwa [← hset]
    exact LeadsTo.trans_singleton hOpenP hHookB'
  -- ----- Path S2: open N keys (reversed), then Hook.b -----
  -- Xf.reverse = N.reverse.map litKey ++ [put] ++ P.reverse.map litKey
  have hXfrev :
      Xf.reverse = N.reverse.map (litKey pΛ) ++ [hookPut ph] ++ P.reverse.map (litKey pΛ) := by
    -- Xf = P.map ++ [put] ++ N.map
    -- reverse = (N.map).reverse ++ [put] ++ (P.map).reverse
    --         = N.reverse.map ++ [put] ++ P.reverse.map
    simp [Xf, List.reverse_append, List.map_reverse, List.append_assoc]
  set mid2 : List ℕ :=
    [hookPut ph] ++ P.reverse.map (litKey pΛ) ++ forkF2 pf ++ hookG' ph ++ X.reverse ++
      hookH' ph ++ Y
  have hS2arr : S2 = N.reverse.map (litKey pΛ) ++ mid2 ++ literals pΛ m O I := by
    simp [S2, hXfrev, Zf, Zh, mid2, List.append_assoc]
  have hOpenN : LeadsTo S2 {mid2 ++ literals pΛ m (O ∪ N.toFinset) I} := by
    have h := leadsTo_open_keys_reverse pΛ m N O I mid2 hO hI hOI hNm hN hNO hNI
      (by simpa [hS2arr] using hS2stack)
    simpa [hS2arr] using h
  have hStackAfterN : IsStack (mid2 ++ literals pΛ m (O ∪ N.toFinset) I) :=
    IsStack_of_LeadsTo_singleton hS2stack hOpenN
  set Xh2 : List ℕ := P.reverse.map (litKey pΛ) ++ forkF2 pf
  have hmid2eq :
      mid2 ++ literals pΛ m (O ∪ N.toFinset) I =
        hookPut ph :: Xh2 ++ hookG' ph ++ X.reverse ++ hookH' ph ++
          (Y ++ literals pΛ m (O ∪ N.toFinset) I) := by
    simp [mid2, Xh2, List.append_assoc]
  have hStackPut2 : IsStack
      (hookPut ph :: Xh2 ++ hookG' ph ++ X.reverse ++ hookH' ph ++
        (Y ++ literals pΛ m (O ∪ N.toFinset) I)) := by
    rwa [← hmid2eq]
  have hHookB2 : LeadsTo
      (hookPut ph :: Xh2 ++ hookG' ph ++ X.reverse ++ hookH' ph ++
        (Y ++ literals pΛ m (O ∪ N.toFinset) I))
      {X ++ hookG'' ph ++ Xh2 ++ hookH'' ph ++
        (Y ++ literals pΛ m (O ∪ N.toFinset) I)} := by
    simpa using (property_6 ph Xh2 X (Y ++ literals pΛ m (O ∪ N.toFinset) I)).2.1 hStackPut2
  have hS2final :
      X ++ hookG'' ph ++ Xh2 ++ hookH'' ph ++ (Y ++ literals pΛ m (O ∪ N.toFinset) I) =
        X ++ varV2 pΛ P p ++ Y ++ literals pΛ m (O ∪ N.toFinset) I := by
    simp [varV2_eq, Xh2, ph, pf, List.append_assoc]
  have hPath2 : LeadsTo S2
      {X ++ varV2 pΛ P p ++ Y ++ literals pΛ m (O ∪ N.toFinset) I} := by
    have hHookB2' : LeadsTo (mid2 ++ literals pΛ m (O ∪ N.toFinset) I)
        {X ++ varV2 pΛ P p ++ Y ++ literals pΛ m (O ∪ N.toFinset) I} := by
      rw [hmid2eq]
      have hset := congrArg (fun t : List ℕ => ({t} : Set (List ℕ))) hS2final
      rwa [← hset]
    exact LeadsTo.trans_singleton hOpenN hHookB2'
  -- Compose: start -hook-> T0 -fork-> {S1,S2} -paths-> targets
  have hFork' : LeadsTo T0 {S1, S2} := by
    simpa [hT0eq, S1, S2] using hFork
  have hAfterFork : LeadsTo T0
      {X ++ varV1 pΛ N p ++ Y ++ literals pΛ m (O ∪ P.toFinset) I,
        X ++ varV2 pΛ P p ++ Y ++ literals pΛ m (O ∪ N.toFinset) I} :=
    LeadsTo.pair_union hFork' hPath1 hPath2
  exact LeadsTo.trans_singleton hHook hAfterFork


lemma varD_eq (p : ℤ) : varD p = Dock (p + 2).toNat (p + 29).toNat := rfl

lemma interval_concat (a b c : ℕ) (hab : a ≤ b) (hbc : b + 1 ≤ c) :
    interval a b ++ interval (b + 1) c = interval a c := by
  simp only [interval]
  have hlen : b + 1 - a + (c + 1 - (b + 1)) = c + 1 - a := by omega
  have ham : a + (b + 1 - a) = b + 1 := by omega
  rw [← hlen, ← List.range'_append_1, ham]

lemma interval_reverse_concat (a b c : ℕ) (hab : a ≤ b) (hbc : b + 1 ≤ c) :
    (interval (b + 1) c).reverse ++ (interval a b).reverse =
      (interval a c).reverse := by
  rw [← List.reverse_append, interval_concat a b c hab hbc]

lemma mem_IsStack_pos {S : List ℕ} (h : IsStack S) {x : ℕ} (hx : x ∈ S) : 0 < x := by
  have hx' : x ∈ identity S.length := (List.Perm.mem_iff h).mp hx
  simp [identity, interval, List.mem_range'] at hx'
  omega

lemma toNat_add_of_nonneg (p : ℤ) (hp : 0 ≤ p) (c : ℕ) :
    (p + (c : ℤ)).toNat = p.toNat + c := by
  have hp' : 0 ≤ (c : ℤ) := Int.natCast_nonneg _
  rw [Int.toNat_add hp hp', Int.toNat_natCast]

/-- Property 9 (b). -/
lemma prop9_b
    (pΛ m : ℕ) (p : ℤ) (hp : -2 ≤ p) (N : List ℕ) (O I : Finset ℕ) (X Y : List ℕ)
    (hN : N.Nodup)
    (hNm : ∀ j ∈ N, j ∈ Finset.Icc 1 m)
    (hO : O ⊆ Finset.Icc 1 m) (hI : I ⊆ Finset.Icc 1 m)
    (hOI : Disjoint O I)
    (hNO : ∀ j ∈ N, j ∉ O) (hNI : ∀ j ∈ N, j ∉ I)
    (hStack0 : IsStack (varV1 pΛ N p ++ X ++ varD p ++ Y ++ literals pΛ m O I)) :
    LeadsTo (varV1 pΛ N p ++ X ++ varD p ++ Y ++ literals pΛ m O I)
      {X ++ interval (p + 1).toNat (p + 31).toNat ++ Y ++ literals pΛ m (O ∪ N.toFinset) I} := by
  set ph : ℕ := (p + 2).toNat
  set pf : ℕ := (p + 14).toNat
  have hp0 : 0 ≤ p := by
    have hmem : (p + 2).toNat - 1 ∈
        varV1 pΛ N p ++ X ++ varD p ++ Y ++ literals pΛ m O I := by
      simp [varD_eq, Dock, List.mem_append]
    have hpos : 0 < (p + 2).toNat - 1 := mem_IsStack_pos hStack0 hmem
    have hph : 2 ≤ (p + 2).toNat := by omega
    have hnn : 0 ≤ p + 2 := by
      by_contra h
      push Not at h
      have hz : (p + 2).toNat = 0 := Int.toNat_eq_zero.mpr (le_of_lt h)
      omega
    have heq : ((p + 2).toNat : ℤ) = p + 2 := Int.toNat_of_nonneg hnn
    have : (2 : ℤ) ≤ p + 2 := by
      have hcast : (2 : ℤ) ≤ ((p + 2).toNat : ℤ) := Nat.cast_le.mpr hph
      linarith
    linarith

  have hpf : pf = ph + 12 := by
    simp [ph, pf, offset_p14 p hp]
  have hph_val : ph = p.toNat + 2 := by
    simpa [ph] using toNat_add_of_nonneg p hp0 2
  have hp1 : (p + 1).toNat = p.toNat + 1 := toNat_add_of_nonneg p hp0 1
  have hp29 : (p + 29).toNat = p.toNat + 29 := toNat_add_of_nonneg p hp0 29
  have hp31 : (p + 31).toNat = p.toNat + 31 := toNat_add_of_nonneg p hp0 31

  set Z0 : List ℕ := X ++ varD p ++ Y ++ literals pΛ m O I
  set Xh : List ℕ := N.map (litKey pΛ) ++ forkF1 pf
  have hArr :
      varV1 pΛ N p ++ X ++ varD p ++ Y ++ literals pΛ m O I =
        hookG'' ph ++ Xh ++ hookH'' ph ++ Z0 := by
    simp [varV1_eq, Xh, Z0, ph, pf, List.append_assoc]

  rw [hArr] at hStack0 ⊢
  -- Hook.c
  have hHookC : LeadsTo (hookG'' ph ++ Xh ++ hookH'' ph ++ Z0)
      {Xh ++ (interval (ph + 1) (ph + 12)).reverse ++ Z0} :=
    (property_6 ph Xh Z0 []).2.2 hStack0
  have hStack1 : IsStack (Xh ++ (interval (ph + 1) (ph + 12)).reverse ++ Z0) :=
    IsStack_of_LeadsTo_singleton hStack0 hHookC

  -- Open N keys
  set mid : List ℕ :=
    forkF1 pf ++ (interval (ph + 1) (ph + 12)).reverse ++ X ++ varD p ++ Y
  have hXhZ :
      Xh ++ (interval (ph + 1) (ph + 12)).reverse ++ Z0 =
        N.map (litKey pΛ) ++ mid ++ literals pΛ m O I := by
    simp [Xh, mid, Z0, List.append_assoc]
  have hOpen : LeadsTo (Xh ++ (interval (ph + 1) (ph + 12)).reverse ++ Z0)
      {mid ++ literals pΛ m (O ∪ N.toFinset) I} := by
    simpa [hXhZ] using
      leadsTo_open_keys pΛ m N O I mid hO hI hOI hNm hN hNO hNI
        (by simpa [hXhZ] using hStack1)
  have hStack2 : IsStack (mid ++ literals pΛ m (O ∪ N.toFinset) I) :=
    IsStack_of_LeadsTo_singleton hStack1 hOpen

  -- Fork.b
  set Yf : List ℕ :=
    (interval (ph + 1) (ph + 12)).reverse ++ X ++ varD p ++ Y ++
      literals pΛ m (O ∪ N.toFinset) I
  have hmid :
      mid ++ literals pΛ m (O ∪ N.toFinset) I = forkF1 pf ++ Yf := by
    simp [mid, Yf, List.append_assoc]
  have hStackF : IsStack (forkF1 pf ++ Yf) := by
    rwa [← hmid]
  have hForkB : LeadsTo (forkF1 pf ++ Yf)
      {(interval (pf + 1) (pf + 15)).reverse ++ Yf} :=
    (property_7 pf [] Yf).2.1 hStackF
  have hForkB' : LeadsTo (mid ++ literals pΛ m (O ∪ N.toFinset) I)
      {(interval (pf + 1) (pf + 15)).reverse ++ Yf} := by
    simpa [hmid] using hForkB
  have hStack3 :
      IsStack ((interval (pf + 1) (pf + 15)).reverse ++ Yf) :=
    IsStack_of_LeadsTo_singleton hStack2 hForkB'

  -- Rearrange as dock input: ⋆I^{ph+1}_{p+29} ++ X ++ Dock ph (p+29) ++ Y ++ Λ'
  have hpf1 : pf + 1 = ph + 13 := by omega
  have hpf15 : pf + 15 = ph + 27 := by omega
  -- ⋆I^{pf+1}_{pf+15} ++ ⋆I^{ph+1}_{ph+12} = ⋆I^{ph+1}_{ph+27}
  -- and ph+27 = (p+29).toNat when p≥0: ph+27 = p.toNat+2+27 = p.toNat+29
  have hq : (p + 29).toNat = ph + 27 := by
    simp [hp29, hph_val]
  have hab : ph + 1 ≤ ph + 12 := by omega
  have hbc : ph + 12 + 1 ≤ ph + 27 := by omega
  have hInt :
      (interval (pf + 1) (pf + 15)).reverse ++ (interval (ph + 1) (ph + 12)).reverse =
        (interval (ph + 1) (ph + 27)).reverse := by
    simp only [hpf1, hpf15]
    simpa using (interval_reverse_concat (ph + 1) (ph + 12) (ph + 27) hab hbc)

  set Λ' : List ℕ := literals pΛ m (O ∪ N.toFinset) I
  have hDockArr :
      (interval (pf + 1) (pf + 15)).reverse ++ Yf =
        (interval (ph + 1) ((p + 29).toNat)).reverse ++ X ++
          Dock ph (p + 29).toNat ++ Y ++ Λ' := by
    have h1 :
        (interval (pf + 1) (pf + 15)).reverse ++ Yf =
          (interval (pf + 1) (pf + 15)).reverse ++ (interval (ph + 1) (ph + 12)).reverse ++
            X ++ varD p ++ Y ++ Λ' := by
      simp [Yf, Λ', List.append_assoc]
    rw [h1]
    have h2 :
        (interval (pf + 1) (pf + 15)).reverse ++ (interval (ph + 1) (ph + 12)).reverse =
          (interval (ph + 1) (ph + 27)).reverse := hInt
    simp [h2, varD_eq, hq, ph, List.append_assoc]

  have hStackDock : IsStack
      ((interval (ph + 1) ((p + 29).toNat)).reverse ++ X ++
        Dock ph (p + 29).toNat ++ Y ++ Λ') := by
    rwa [← hDockArr]

  have hpq : ph < (p + 29).toNat := by
    simp [hph_val, hp29]

  -- property_4 with concatenated Y++Λ'
  have hFinalInt :
      interval (ph - 1) ((p + 29).toNat + 2) =
        interval (p + 1).toNat (p + 31).toNat := by
    have hA : ph - 1 = p.toNat + 1 := by
      rw [hph_val]; omega
    have hB : (p + 29).toNat + 2 = p.toNat + 31 := by
      simp [hp29]
    simp [hA, hB, hp1, hp31]

  have hDock : LeadsTo
      ((interval (pf + 1) (pf + 15)).reverse ++ Yf)
      {X ++ interval (p + 1).toNat (p + 31).toNat ++ Y ++ Λ'} := by
    have hL :
        (interval (ph + 1) ((p + 29).toNat)).reverse ++ X ++
            Dock ph (p + 29).toNat ++ (Y ++ Λ') =
          (interval (pf + 1) (pf + 15)).reverse ++ Yf := by
      simpa [List.append_assoc] using hDockArr.symm
    have hS : IsStack
        ((interval (ph + 1) ((p + 29).toNat)).reverse ++ X ++
          Dock ph (p + 29).toNat ++ (Y ++ Λ')) := by
      simpa [List.append_assoc] using hStackDock
    have hP4 := property_4 ph (p + 29).toNat X (Y ++ Λ') hpq hS
    -- rewrite LHS
    have hP4' : LeadsTo ((interval (pf + 1) (pf + 15)).reverse ++ Yf)
        {X ++ interval (ph - 1) ((p + 29).toNat + 2) ++ (Y ++ Λ')} := by
      rwa [hL] at hP4
    -- rewrite RHS interval and flatten append
    have hset :
        ({X ++ interval (ph - 1) ((p + 29).toNat + 2) ++ (Y ++ Λ')} :
          Set (List ℕ)) =
        {X ++ interval (p + 1).toNat (p + 31).toNat ++ Y ++ Λ'} := by
      simp [hFinalInt, List.append_assoc]
    rwa [hset] at hP4'

  -- Compose all
  have hAfterOpen : LeadsTo (Xh ++ (interval (ph + 1) (ph + 12)).reverse ++ Z0)
      {X ++ interval (p + 1).toNat (p + 31).toNat ++ Y ++
        literals pΛ m (O ∪ N.toFinset) I} := by
    have h1 := LeadsTo.trans_singleton hOpen hForkB'
    have h2 : LeadsTo ((interval (pf + 1) (pf + 15)).reverse ++ Yf)
        {X ++ interval (p + 1).toNat (p + 31).toNat ++ Y ++
          literals pΛ m (O ∪ N.toFinset) I} := by
      simpa [Λ'] using hDock
    exact LeadsTo.trans_singleton h1 h2

  exact LeadsTo.trans_singleton hHookC hAfterOpen

/-- Property 9 (c), mirror of (b) with `V²` / `P` / `Fork.c`. -/
lemma prop9_c
    (pΛ m : ℕ) (p : ℤ) (hp : -2 ≤ p) (P : List ℕ) (O I : Finset ℕ) (X Y : List ℕ)
    (hP : P.Nodup)
    (hPm : ∀ j ∈ P, j ∈ Finset.Icc 1 m)
    (hO : O ⊆ Finset.Icc 1 m) (hI : I ⊆ Finset.Icc 1 m)
    (hOI : Disjoint O I)
    (hPO : ∀ j ∈ P, j ∉ O) (hPI : ∀ j ∈ P, j ∉ I)
    (hStack0 : IsStack (varV2 pΛ P p ++ X ++ varD p ++ Y ++ literals pΛ m O I)) :
    LeadsTo (varV2 pΛ P p ++ X ++ varD p ++ Y ++ literals pΛ m O I)
      {X ++ interval (p + 1).toNat (p + 31).toNat ++ Y ++ literals pΛ m (O ∪ P.toFinset) I} := by
  set ph : ℕ := (p + 2).toNat
  set pf : ℕ := (p + 14).toNat
  have hp0 : 0 ≤ p := by
    have hmem : (p + 2).toNat - 1 ∈
        varV2 pΛ P p ++ X ++ varD p ++ Y ++ literals pΛ m O I := by
      simp [varD_eq, Dock, List.mem_append]
    have hpos : 0 < (p + 2).toNat - 1 := mem_IsStack_pos hStack0 hmem
    have hph : 2 ≤ (p + 2).toNat := by omega
    have hnn : 0 ≤ p + 2 := by
      by_contra h
      push Not at h
      have hz : (p + 2).toNat = 0 := Int.toNat_eq_zero.mpr (le_of_lt h)
      omega
    have heq : ((p + 2).toNat : ℤ) = p + 2 := Int.toNat_of_nonneg hnn
    have : (2 : ℤ) ≤ p + 2 := by
      have hcast : (2 : ℤ) ≤ ((p + 2).toNat : ℤ) := Nat.cast_le.mpr hph
      linarith
    linarith
  have hpf : pf = ph + 12 := by simp [ph, pf, offset_p14 p hp]
  have hph_val : ph = p.toNat + 2 := by simpa [ph] using toNat_add_of_nonneg p hp0 2
  have hp1 : (p + 1).toNat = p.toNat + 1 := toNat_add_of_nonneg p hp0 1
  have hp29 : (p + 29).toNat = p.toNat + 29 := toNat_add_of_nonneg p hp0 29
  have hp31 : (p + 31).toNat = p.toNat + 31 := toNat_add_of_nonneg p hp0 31
  set Z0 : List ℕ := X ++ varD p ++ Y ++ literals pΛ m O I
  set Xh : List ℕ := P.reverse.map (litKey pΛ) ++ forkF2 pf
  have hArr :
      varV2 pΛ P p ++ X ++ varD p ++ Y ++ literals pΛ m O I =
        hookG'' ph ++ Xh ++ hookH'' ph ++ Z0 := by
    simp [varV2_eq, Xh, Z0, ph, pf, List.append_assoc]
  rw [hArr] at hStack0 ⊢
  have hHookC : LeadsTo (hookG'' ph ++ Xh ++ hookH'' ph ++ Z0)
      {Xh ++ (interval (ph + 1) (ph + 12)).reverse ++ Z0} :=
    (property_6 ph Xh Z0 []).2.2 hStack0
  have hStack1 : IsStack (Xh ++ (interval (ph + 1) (ph + 12)).reverse ++ Z0) :=
    IsStack_of_LeadsTo_singleton hStack0 hHookC
  set mid : List ℕ :=
    forkF2 pf ++ (interval (ph + 1) (ph + 12)).reverse ++ X ++ varD p ++ Y
  have hXhZ :
      Xh ++ (interval (ph + 1) (ph + 12)).reverse ++ Z0 =
        P.reverse.map (litKey pΛ) ++ mid ++ literals pΛ m O I := by
    simp [Xh, mid, Z0, List.append_assoc]
  have hOpen : LeadsTo (Xh ++ (interval (ph + 1) (ph + 12)).reverse ++ Z0)
      {mid ++ literals pΛ m (O ∪ P.toFinset) I} := by
    simpa [hXhZ] using
      leadsTo_open_keys_reverse pΛ m P O I mid hO hI hOI hPm hP hPO hPI
        (by simpa [hXhZ] using hStack1)
  have hStack2 : IsStack (mid ++ literals pΛ m (O ∪ P.toFinset) I) :=
    IsStack_of_LeadsTo_singleton hStack1 hOpen
  set Yf : List ℕ :=
    (interval (ph + 1) (ph + 12)).reverse ++ X ++ varD p ++ Y ++
      literals pΛ m (O ∪ P.toFinset) I
  have hmid :
      mid ++ literals pΛ m (O ∪ P.toFinset) I = forkF2 pf ++ Yf := by
    simp [mid, Yf, List.append_assoc]
  have hStackF : IsStack (forkF2 pf ++ Yf) := by rwa [← hmid]
  have hForkC : LeadsTo (forkF2 pf ++ Yf)
      {(interval (pf + 1) (pf + 15)).reverse ++ Yf} :=
    (property_7 pf [] Yf).2.2 hStackF
  have hForkC' : LeadsTo (mid ++ literals pΛ m (O ∪ P.toFinset) I)
      {(interval (pf + 1) (pf + 15)).reverse ++ Yf} := by
    simpa [hmid] using hForkC
  have hStack3 : IsStack ((interval (pf + 1) (pf + 15)).reverse ++ Yf) :=
    IsStack_of_LeadsTo_singleton hStack2 hForkC'
  have hpf1 : pf + 1 = ph + 13 := by omega
  have hpf15 : pf + 15 = ph + 27 := by omega
  have hq : (p + 29).toNat = ph + 27 := by simp [hp29, hph_val]
  have hab : ph + 1 ≤ ph + 12 := by omega
  have hbc : ph + 12 + 1 ≤ ph + 27 := by omega
  have hInt :
      (interval (pf + 1) (pf + 15)).reverse ++ (interval (ph + 1) (ph + 12)).reverse =
        (interval (ph + 1) (ph + 27)).reverse := by
    simp only [hpf1, hpf15]
    simpa using (interval_reverse_concat (ph + 1) (ph + 12) (ph + 27) hab hbc)
  set Λ' : List ℕ := literals pΛ m (O ∪ P.toFinset) I
  have hDockArr :
      (interval (pf + 1) (pf + 15)).reverse ++ Yf =
        (interval (ph + 1) ((p + 29).toNat)).reverse ++ X ++
          Dock ph (p + 29).toNat ++ Y ++ Λ' := by
    have h1 :
        (interval (pf + 1) (pf + 15)).reverse ++ Yf =
          (interval (pf + 1) (pf + 15)).reverse ++ (interval (ph + 1) (ph + 12)).reverse ++
            X ++ varD p ++ Y ++ Λ' := by
      simp [Yf, Λ', List.append_assoc]
    simp [h1, hInt, varD_eq, hq, ph, List.append_assoc]
  have hStackDock : IsStack
      ((interval (ph + 1) ((p + 29).toNat)).reverse ++ X ++
        Dock ph (p + 29).toNat ++ Y ++ Λ') := by
    rwa [← hDockArr]
  have hpq : ph < (p + 29).toNat := by simp [hph_val, hp29]
  have hFinalInt :
      interval (ph - 1) ((p + 29).toNat + 2) =
        interval (p + 1).toNat (p + 31).toNat := by
    have hA : ph - 1 = p.toNat + 1 := by rw [hph_val]; omega
    have hB : (p + 29).toNat + 2 = p.toNat + 31 := by simp [hp29]
    simp [hA, hB, hp1, hp31]
  have hDock : LeadsTo
      ((interval (pf + 1) (pf + 15)).reverse ++ Yf)
      {X ++ interval (p + 1).toNat (p + 31).toNat ++ Y ++ Λ'} := by
    have hL :
        (interval (ph + 1) ((p + 29).toNat)).reverse ++ X ++
            Dock ph (p + 29).toNat ++ (Y ++ Λ') =
          (interval (pf + 1) (pf + 15)).reverse ++ Yf := by
      simpa [List.append_assoc] using hDockArr.symm
    have hS : IsStack
        ((interval (ph + 1) ((p + 29).toNat)).reverse ++ X ++
          Dock ph (p + 29).toNat ++ (Y ++ Λ')) := by
      simpa [List.append_assoc] using hStackDock
    have hP4 := property_4 ph (p + 29).toNat X (Y ++ Λ') hpq hS
    have hP4' : LeadsTo ((interval (pf + 1) (pf + 15)).reverse ++ Yf)
        {X ++ interval (ph - 1) ((p + 29).toNat + 2) ++ (Y ++ Λ')} := by
      rwa [hL] at hP4
    have hset :
        ({X ++ interval (ph - 1) ((p + 29).toNat + 2) ++ (Y ++ Λ')} :
          Set (List ℕ)) =
        {X ++ interval (p + 1).toNat (p + 31).toNat ++ Y ++ Λ'} := by
      simp [hFinalInt, List.append_assoc]
    rwa [hset] at hP4'
  have hAfterOpen : LeadsTo (Xh ++ (interval (ph + 1) (ph + 12)).reverse ++ Z0)
      {X ++ interval (p + 1).toNat (p + 31).toNat ++ Y ++
        literals pΛ m (O ∪ P.toFinset) I} := by
    have h1 := LeadsTo.trans_singleton hOpen hForkC'
    have h2 : LeadsTo ((interval (pf + 1) (pf + 15)).reverse ++ Yf)
        {X ++ interval (p + 1).toNat (p + 31).toNat ++ Y ++
          literals pΛ m (O ∪ P.toFinset) I} := by
      simpa [Λ'] using hDock
    exact LeadsTo.trans_singleton h1 h2
  exact LeadsTo.trans_singleton hHookC hAfterOpen


lemma IsStack.nodup {S : List ℕ} (h : IsStack S) : S.Nodup := by
  have hid : (identity S.length).Nodup := by
    simp [identity, interval]
    exact List.nodup_range' _
  exact (List.Perm.nodup_iff h).2 hid

lemma litKey_mem_literals_of_mem_O (pΛ m : ℕ) (O I : Finset ℕ) (j : ℕ)
    (hj : j ∈ Finset.Icc 1 m) (hO : j ∈ O) :
    litKey pΛ j ∈ literals pΛ m O I := by
  have ⟨hj1, hjm⟩ := Finset.mem_Icc.mp hj
  have hj0 : j - 1 < m := by omega
  have hjid : j - 1 + 1 = j := by omega
  refine List.mem_flatMap.mpr ?_
  refine ⟨j - 1, List.mem_range.mpr hj0, ?_⟩
  show litKey pΛ j ∈
    (if j - 1 + 1 ∈ O then lockOpen (pΛ + 12 * (j - 1))
     else if j - 1 + 1 ∈ I then interval (pΛ + 12 * (j - 1) + 1) (pΛ + 12 * (j - 1) + 12)
     else lockSeq (pΛ + 12 * (j - 1)))
  rw [hjid, if_pos hO]
  -- lockOpen contains p+10 = lockKey
  simp [litKey, lockKey, lockOpen, shift]

lemma litKey_mem_literals_of_mem_I (pΛ m : ℕ) (O I : Finset ℕ) (j : ℕ)
    (hj : j ∈ Finset.Icc 1 m) (hO : j ∉ O) (hI : j ∈ I) :
    litKey pΛ j ∈ literals pΛ m O I := by
  have ⟨hj1, hjm⟩ := Finset.mem_Icc.mp hj
  have hj0 : j - 1 < m := by omega
  have hjid : j - 1 + 1 = j := by omega
  refine List.mem_flatMap.mpr ⟨j - 1, List.mem_range.mpr hj0, ?_⟩
  show litKey pΛ j ∈
    (if j - 1 + 1 ∈ O then lockOpen (pΛ + 12 * (j - 1))
     else if j - 1 + 1 ∈ I then interval (pΛ + 12 * (j - 1) + 1) (pΛ + 12 * (j - 1) + 12)
     else lockSeq (pΛ + 12 * (j - 1)))
  rw [hjid, if_neg hO, if_pos hI]
  -- interval (p+1) (p+12) contains p+10
  simp [litKey, lockKey, interval, List.mem_range']
  exact ⟨9, by omega, by ring⟩

lemma not_IsStack_key_in_literals' (pΛ m : ℕ) (pre : List ℕ) (O I : Finset ℕ)
    (j : ℕ) (hpfx : litKey pΛ j ∈ pre)
    (hmem : litKey pΛ j ∈ literals pΛ m O I) :
    ¬ IsStack (pre ++ literals pΛ m O I) := by
  intro hS
  have hnd := hS.nodup
  exact (List.nodup_append.1 hnd).2.2 (litKey pΛ j) hpfx (litKey pΛ j) hmem rfl

lemma key_in_varV_of_mem_P (pΛ : ℕ) (P N : List ℕ) (p : ℤ) (j : ℕ) (hj : j ∈ P) :
    litKey pΛ j ∈ varV pΛ P N p := by
  simp [varV_eq, List.mem_append, List.mem_map]
  exact Or.inr (Or.inr (Or.inl ⟨j, hj, rfl⟩))

lemma key_in_varV_of_mem_N (pΛ : ℕ) (P N : List ℕ) (p : ℤ) (j : ℕ) (hj : j ∈ N) :
    litKey pΛ j ∈ varV pΛ P N p := by
  simp [varV_eq, List.mem_append, List.mem_map]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, hj, rfl⟩))))

lemma key_in_varV1_of_mem_N (pΛ : ℕ) (N : List ℕ) (p : ℤ) (j : ℕ) (hj : j ∈ N) :
    litKey pΛ j ∈ varV1 pΛ N p := by
  simp [varV1_eq, List.mem_append, List.mem_map]
  exact Or.inr (Or.inl ⟨j, hj, rfl⟩)

lemma key_in_varV2_of_mem_P (pΛ : ℕ) (P : List ℕ) (p : ℤ) (j : ℕ) (hj : j ∈ P) :
    litKey pΛ j ∈ varV2 pΛ P p := by
  simp [varV2_eq, List.mem_append, List.mem_map, List.map_reverse, List.mem_reverse]
  exact Or.inr (Or.inl ⟨j, hj, rfl⟩)

lemma property_9_proof (pΛ m : ℕ) (p : ℤ) (hp : -2 ≤ p) (P N : List ℕ) (O I : Finset ℕ)
    (X Y : List ℕ) (hP : P.Nodup) (hN : N.Nodup)
    (hPm : ∀ j ∈ P, j ∈ Finset.Icc 1 m) (hNm : ∀ j ∈ N, j ∈ Finset.Icc 1 m)
    (hPN : P.Disjoint N) (hO : O ⊆ Finset.Icc 1 m) (hI : I ⊆ Finset.Icc 1 m)
    (hOI : Disjoint O I) :
    (IsStack (varNu p :: X ++ varV pΛ P N p ++ Y ++ literals pΛ m O I) →
      LeadsTo (varNu p :: X ++ varV pΛ P N p ++ Y ++ literals pΛ m O I)
        {X ++ varV1 pΛ N p ++ Y ++ literals pΛ m (O ∪ P.toFinset) I,
          X ++ varV2 pΛ P p ++ Y ++ literals pΛ m (O ∪ N.toFinset) I}) ∧
    (IsStack (varV1 pΛ N p ++ X ++ varD p ++ Y ++ literals pΛ m O I) →
      LeadsTo (varV1 pΛ N p ++ X ++ varD p ++ Y ++ literals pΛ m O I)
        {X ++ interval (p + 1).toNat (p + 31).toNat ++ Y ++ literals pΛ m (O ∪ N.toFinset) I}) ∧
    (IsStack (varV2 pΛ P p ++ X ++ varD p ++ Y ++ literals pΛ m O I) →
      LeadsTo (varV2 pΛ P p ++ X ++ varD p ++ Y ++ literals pΛ m O I)
        {X ++ interval (p + 1).toNat (p + 31).toNat ++ Y ++ literals pΛ m (O ∪ P.toFinset) I}) := by
  refine ⟨?a, ?b, ?c⟩
  · intro hStack
    have hPO : ∀ j ∈ P, j ∉ O := by
      intro j hj hOj
      have hpfx : litKey pΛ j ∈ varNu p :: X ++ varV pΛ P N p ++ Y := by
        simp [List.mem_append, List.mem_cons, key_in_varV_of_mem_P pΛ P N p j hj]
      exact (not_IsStack_key_in_literals' pΛ m (varNu p :: X ++ varV pΛ P N p ++ Y) O I j hpfx
        (litKey_mem_literals_of_mem_O pΛ m O I j (hPm j hj) hOj)) (by
          simpa [List.append_assoc] using hStack)
    have hPI : ∀ j ∈ P, j ∉ I := by
      intro j hj hIj
      by_cases hOj : j ∈ O
      · exact hPO j hj hOj
      · have hpfx : litKey pΛ j ∈ varNu p :: X ++ varV pΛ P N p ++ Y := by
          simp [List.mem_append, List.mem_cons, key_in_varV_of_mem_P pΛ P N p j hj]
        exact (not_IsStack_key_in_literals' pΛ m (varNu p :: X ++ varV pΛ P N p ++ Y) O I j hpfx
          (litKey_mem_literals_of_mem_I pΛ m O I j (hPm j hj) hOj hIj)) (by
            simpa [List.append_assoc] using hStack)
    have hNO : ∀ j ∈ N, j ∉ O := by
      intro j hj hOj
      have hpfx : litKey pΛ j ∈ varNu p :: X ++ varV pΛ P N p ++ Y := by
        simp [List.mem_append, List.mem_cons, key_in_varV_of_mem_N pΛ P N p j hj]
      exact (not_IsStack_key_in_literals' pΛ m (varNu p :: X ++ varV pΛ P N p ++ Y) O I j hpfx
        (litKey_mem_literals_of_mem_O pΛ m O I j (hNm j hj) hOj)) (by
          simpa [List.append_assoc] using hStack)
    have hNI : ∀ j ∈ N, j ∉ I := by
      intro j hj hIj
      by_cases hOj : j ∈ O
      · exact hNO j hj hOj
      · have hpfx : litKey pΛ j ∈ varNu p :: X ++ varV pΛ P N p ++ Y := by
          simp [List.mem_append, List.mem_cons, key_in_varV_of_mem_N pΛ P N p j hj]
        exact (not_IsStack_key_in_literals' pΛ m (varNu p :: X ++ varV pΛ P N p ++ Y) O I j hpfx
          (litKey_mem_literals_of_mem_I pΛ m O I j (hNm j hj) hOj hIj)) (by
            simpa [List.append_assoc] using hStack)
    exact prop9_a pΛ m p hp P N O I X Y hP hN hPm hNm hPN hO hI hOI hPO hPI hNO hNI hStack
  · intro hStack
    have hNO : ∀ j ∈ N, j ∉ O := by
      intro j hj hOj
      have hpfx : litKey pΛ j ∈ varV1 pΛ N p ++ X ++ varD p ++ Y := by
        simp [List.mem_append, key_in_varV1_of_mem_N pΛ N p j hj]
      exact (not_IsStack_key_in_literals' pΛ m (varV1 pΛ N p ++ X ++ varD p ++ Y) O I j hpfx
        (litKey_mem_literals_of_mem_O pΛ m O I j (hNm j hj) hOj)) (by
          simpa [List.append_assoc] using hStack)
    have hNI : ∀ j ∈ N, j ∉ I := by
      intro j hj hIj
      by_cases hOj : j ∈ O
      · exact hNO j hj hOj
      · have hpfx : litKey pΛ j ∈ varV1 pΛ N p ++ X ++ varD p ++ Y := by
          simp [List.mem_append, key_in_varV1_of_mem_N pΛ N p j hj]
        exact (not_IsStack_key_in_literals' pΛ m (varV1 pΛ N p ++ X ++ varD p ++ Y) O I j hpfx
          (litKey_mem_literals_of_mem_I pΛ m O I j (hNm j hj) hOj hIj)) (by
            simpa [List.append_assoc] using hStack)
    exact prop9_b pΛ m p hp N O I X Y hN hNm hO hI hOI hNO hNI hStack
  · intro hStack
    have hPO : ∀ j ∈ P, j ∉ O := by
      intro j hj hOj
      have hpfx : litKey pΛ j ∈ varV2 pΛ P p ++ X ++ varD p ++ Y := by
        simp [List.mem_append, key_in_varV2_of_mem_P pΛ P p j hj]
      exact (not_IsStack_key_in_literals' pΛ m (varV2 pΛ P p ++ X ++ varD p ++ Y) O I j hpfx
        (litKey_mem_literals_of_mem_O pΛ m O I j (hPm j hj) hOj)) (by
          simpa [List.append_assoc] using hStack)
    have hPI : ∀ j ∈ P, j ∉ I := by
      intro j hj hIj
      by_cases hOj : j ∈ O
      · exact hPO j hj hOj
      · have hpfx : litKey pΛ j ∈ varV2 pΛ P p ++ X ++ varD p ++ Y := by
          simp [List.mem_append, key_in_varV2_of_mem_P pΛ P p j hj]
        exact (not_IsStack_key_in_literals' pΛ m (varV2 pΛ P p ++ X ++ varD p ++ Y) O I j hpfx
          (litKey_mem_literals_of_mem_I pΛ m O I j (hPm j hj) hOj hIj)) (by
            simpa [List.append_assoc] using hStack)
    exact prop9_c pΛ m p hp P O I X Y hP hPm hO hI hOI hPO hPI hStack

end PancakeHard

theorem solution (pΛ m : ℕ) (p : ℤ) (hp : -2 ≤ p) (P N : List ℕ) (O I : Finset ℕ) (X Y : List ℕ)
    (hP : P.Nodup) (hN : N.Nodup) (hPm : ∀ j ∈ P, j ∈ Finset.Icc 1 m)
    (hNm : ∀ j ∈ N, j ∈ Finset.Icc 1 m) (hPN : P.Disjoint N) (hO : O ⊆ Finset.Icc 1 m)
    (hI : I ⊆ Finset.Icc 1 m) (hOI : Disjoint O I) :
    (PancakeHard.IsStack (PancakeHard.varNu p :: X ++ PancakeHard.varV pΛ P N p ++ Y ++
        PancakeHard.literals pΛ m O I) →
      PancakeHard.LeadsTo (PancakeHard.varNu p :: X ++ PancakeHard.varV pΛ P N p ++ Y ++
          PancakeHard.literals pΛ m O I)
        {X ++ PancakeHard.varV1 pΛ N p ++ Y ++ PancakeHard.literals pΛ m (O ∪ P.toFinset) I,
          X ++ PancakeHard.varV2 pΛ P p ++ Y ++ PancakeHard.literals pΛ m (O ∪ N.toFinset) I}) ∧
    (PancakeHard.IsStack (PancakeHard.varV1 pΛ N p ++ X ++ PancakeHard.varD p ++ Y ++
        PancakeHard.literals pΛ m O I) →
      PancakeHard.LeadsTo (PancakeHard.varV1 pΛ N p ++ X ++ PancakeHard.varD p ++ Y ++
          PancakeHard.literals pΛ m O I)
        {X ++ PancakeHard.interval (p + 1).toNat (p + 31).toNat ++ Y ++
          PancakeHard.literals pΛ m (O ∪ N.toFinset) I}) ∧
    (PancakeHard.IsStack (PancakeHard.varV2 pΛ P p ++ X ++ PancakeHard.varD p ++ Y ++
        PancakeHard.literals pΛ m O I) →
      PancakeHard.LeadsTo (PancakeHard.varV2 pΛ P p ++ X ++ PancakeHard.varD p ++ Y ++
          PancakeHard.literals pΛ m O I)
        {X ++ PancakeHard.interval (p + 1).toNat (p + 31).toNat ++ Y ++
          PancakeHard.literals pΛ m (O ∪ P.toFinset) I}) :=
  PancakeHard.property_9_proof pΛ m p hp P N O I X Y hP hN hPm hNm hPN hO hI hOI
