-- Prove2me | solution 1 for PancakeHard.property_11
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-10T18:57:28.523881+00:00
-- url     : https://prove2.me/submissions/ddb3f6b6-d975-4b01-b91b-8816493613e0

/-
Path composition helpers adapted from the accepted Property 10 submission
c86bdf35-2049-4bd7-9ccc-d8d4f186b0e2 (public Prove2Me contribution).
The clause completion argument follows Bulteau–Fertin–Rusu, Property 11.
-/
import Mathlib
import Definitions.Def_PancakeHard_Clause
import Theorems.Thm_PancakeHard_property_4
import Theorems.Thm_PancakeHard_property_6
import Theorems.Thm_PancakeHard_property_7
import Theorems.Thm_PancakeHard_property_8

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option pp.proofs false

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


lemma stack_positive {S : List ℕ} (hS : IsStack S) {x : ℕ} (hx : x ∈ S) : 0 < x := by
  have hm := hS.mem_iff.mp hx
  simp only [identity, interval, List.mem_range'] at hm
  omega

lemma clause_offset_nonneg (pΛ m : ℕ) (p : ℤ) (B Y Z : List ℕ) (O I : Finset ℕ)
    (hS : IsStack (B ++ Y ++ clauseΔ p ++ Z ++ literals pΛ m O I)) : 0 ≤ p := by
  have hm : (p + 2).toNat - 1 ∈ B ++ Y ++ clauseΔ p ++ Z ++ literals pΛ m O I := by
    simp [clauseΔ, Dock]
  have hpos := stack_positive hS hm
  omega

lemma offset_sub_two (p : ℕ) : p + 2 - 1 = p + 1 := by omega

lemma offset_sub_twentyone (p : ℕ) : p + 21 - 1 = p + 20 := by omega

lemma join_intervals (p : ℕ) :
    interval (p + 1) (p + 19) ++ interval (p + 20) (p + 62) =
      interval (p + 1) (p + 62) := by
  simp only [interval]
  have h1 : p + 19 + 1 - (p + 1) = 19 := by omega
  have h2 : p + 62 + 1 - (p + 20) = 43 := by omega
  have h3 : p + 62 + 1 - (p + 1) = 62 := by omega
  rw [h1, h2, h3]
  simp

lemma join_reversed_intervals (p : ℕ) :
    (interval (p + 46) (p + 60)).reverse ++
      (interval (p + 34) (p + 45)).reverse ++
      (interval (p + 22) (p + 33)).reverse =
    (interval (p + 22) (p + 60)).reverse := by
  apply List.reverse_injective
  simp only [List.reverse_append, List.reverse_reverse]
  simp only [interval]
  have h1 : p + 33 + 1 - (p + 22) = 12 := by omega
  have h2 : p + 45 + 1 - (p + 34) = 12 := by omega
  have h3 : p + 60 + 1 - (p + 46) = 15 := by omega
  have h4 : p + 60 + 1 - (p + 22) = 39 := by omega
  rw [h1, h2, h3, h4]
  simp only [← List.append_assoc]
  have h12 : List.range' (p + 22) 12 ++ List.range' (p + 34) 12 =
      List.range' (p + 22) 24 := by
    simp
  rw [h12]
  simp


lemma nat_cast_1 (p : ℕ) : ((p : ℤ) + 1).toNat = p + 1 := by rfl

lemma nat_cast_2 (p : ℕ) : ((p : ℤ) + 2).toNat = p + 2 := by rfl

lemma nat_cast_17 (p : ℕ) : ((p : ℤ) + 17).toNat = p + 17 := by rfl

lemma nat_cast_21 (p : ℕ) : ((p : ℤ) + 21).toNat = p + 21 := by rfl

lemma nat_cast_33 (p : ℕ) : ((p : ℤ) + 33).toNat = p + 33 := by rfl

lemma nat_cast_45 (p : ℕ) : ((p : ℤ) + 45).toNat = p + 45 := by rfl

lemma nat_cast_60 (p : ℕ) : ((p : ℤ) + 60).toNat = p + 60 := by rfl

lemma nat_cast_62 (p : ℕ) : ((p : ℤ) + 62).toNat = p + 62 := by rfl
lemma complete_1_nat (pΛ m p x y : ℕ) (O I : Finset ℕ) (Y Z : List ℕ)
    (hO : O ⊆ Finset.Icc 1 m) (hI : I ⊆ Finset.Icc 1 m) (hOI : Disjoint O I)
    (hxy : x ≠ y) (hxO : x ∈ O) (hyO : y ∈ O)
    (hS : IsStack (hookG'' (p + 21) ++ ([litTest pΛ y] ++ (forkF1 (p + 2) ++ (hookG'' (p + 33) ++ ([litTest pΛ x] ++ (forkF1 (p + 45) ++ (hookH'' (p + 33) ++ (hookH'' (p + 21) ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (O) (I))))))))))))))) :
    LeadsTo (hookG'' (p + 21) ++ ([litTest pΛ y] ++ (forkF1 (p + 2) ++ (hookG'' (p + 33) ++ ([litTest pΛ x] ++ (forkF1 (p + 45) ++ (hookH'' (p + 33) ++ (hookH'' (p + 21) ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (O) (I)))))))))))))) {Y ++ interval (p + 1) (p + 62) ++ Z ++ literals pΛ m (O \ {x, y}) (I ∪ {x, y})} := by
  let S0 : List ℕ := hookG'' (p + 21) ++ ([litTest pΛ y] ++ (forkF1 (p + 2) ++ (hookG'' (p + 33) ++ ([litTest pΛ x] ++ (forkF1 (p + 45) ++ (hookH'' (p + 33) ++ (hookH'' (p + 21) ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (O) (I)))))))))))))
  have h0 : IsStack S0 := hS
  let S1 : List ℕ := [litTest pΛ y] ++ (forkF1 (p + 2) ++ (hookG'' (p + 33) ++ ([litTest pΛ x] ++ (forkF1 (p + 45) ++ (hookH'' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (O) (I))))))))))))
  have e1 : LeadsTo S0 {S1} := by
    simpa only [S0, S1, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      (property_6 (p + 21) ([litTest pΛ y] ++ (forkF1 (p + 2) ++ (hookG'' (p + 33) ++ ([litTest pΛ x] ++ (forkF1 (p + 45) ++ (hookH'' (p + 33))))))) (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (O) (I)))))) []).2.2 (by simpa only [S0, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h0)
  have h1 : IsStack S1 := IsStack_of_LeadsTo_singleton h0 e1
  let S2 : List ℕ := forkF1 (p + 2) ++ (hookG'' (p + 33) ++ ([litTest pΛ x] ++ (forkF1 (p + 45) ++ (hookH'' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m ((O).erase y) (insert y (I))))))))))))
  have e2 : LeadsTo S1 {S2} := by
    simpa only [S1, S2, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      (property_8 pΛ m (O) (I) (forkF1 (p + 2) ++ (hookG'' (p + 33) ++ ([litTest pΛ x] ++ (forkF1 (p + 45) ++ (hookH'' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z)))))))))) hO hI hOI).2.1 y hyO (by simpa only [S1, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h1)
  have h2 : IsStack S2 := IsStack_of_LeadsTo_singleton h1 e2
  have hO1 : (O).erase y ⊆ Finset.Icc 1 m := fun z hz => hO (Finset.mem_erase.mp hz).2
  have hI1 : insert y (I) ⊆ Finset.Icc 1 m := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hO hyO
    · exact hI hz
  have hD1 : Disjoint ((O).erase y) (insert y (I)) := by
    apply Finset.disjoint_left.mpr
    intro z hzO hzI
    rcases Finset.mem_insert.mp hzI with rfl | hzI
    · exact (Finset.mem_erase.mp hzO).1 rfl
    · exact Finset.disjoint_left.mp hOI (Finset.mem_erase.mp hzO).2 hzI
  let S3 : List ℕ := (interval (p + 3) (p + 17)).reverse ++ (hookG'' (p + 33) ++ ([litTest pΛ x] ++ (forkF1 (p + 45) ++ (hookH'' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m ((O).erase y) (insert y (I))))))))))))
  have e3 : LeadsTo S2 {S3} := by
    simpa only [S2, S3, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      (property_7 (p + 2) [] (hookG'' (p + 33) ++ ([litTest pΛ x] ++ (forkF1 (p + 45) ++ (hookH'' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m ((O).erase y) (insert y (I))))))))))))).2.1 (by simpa only [S2, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h2)
  have h3 : IsStack S3 := IsStack_of_LeadsTo_singleton h2 e3
  let S4 : List ℕ := hookG'' (p + 33) ++ ([litTest pΛ x] ++ (forkF1 (p + 45) ++ (hookH'' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m ((O).erase y) (insert y (I)))))))))))
  have e4 : LeadsTo S3 {S4} := by
    simpa only [S3, S4, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      property_4 (p + 2) (p + 17) (hookG'' (p + 33) ++ ([litTest pΛ x] ++ (forkF1 (p + 45) ++ (hookH'' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y)))))) (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m ((O).erase y) (insert y (I))))) (by omega) (by simpa only [S3, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h3)
  have h4 : IsStack S4 := IsStack_of_LeadsTo_singleton h3 e4
  let S5 : List ℕ := [litTest pΛ x] ++ (forkF1 (p + 45) ++ ((interval (p + 34) (p + 45)).reverse ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m ((O).erase y) (insert y (I))))))))))
  have e5 : LeadsTo S4 {S5} := by
    simpa only [S4, S5, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      (property_6 (p + 33) ([litTest pΛ x] ++ (forkF1 (p + 45))) ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m ((O).erase y) (insert y (I)))))))) []).2.2 (by simpa only [S4, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h4)
  have h5 : IsStack S5 := IsStack_of_LeadsTo_singleton h4 e5
  let S6 : List ℕ := forkF1 (p + 45) ++ ((interval (p + 34) (p + 45)).reverse ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (((O).erase y).erase x) (insert x (insert y (I))))))))))
  have e6 : LeadsTo S5 {S6} := by
    simpa only [S5, S6, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      (property_8 pΛ m ((O).erase y) (insert y (I)) (forkF1 (p + 45) ++ ((interval (p + 34) (p + 45)).reverse ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z))))))) hO1 hI1 hD1).2.1 x (by simp [hxO, hxy]) (by simpa only [S5, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h5)
  have h6 : IsStack S6 := IsStack_of_LeadsTo_singleton h5 e6
  let S7 : List ℕ := (interval (p + 46) (p + 60)).reverse ++ ((interval (p + 34) (p + 45)).reverse ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (((O).erase y).erase x) (insert x (insert y (I))))))))))
  have e7 : LeadsTo S6 {S7} := by
    simpa only [S6, S7, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      (property_7 (p + 45) [] ((interval (p + 34) (p + 45)).reverse ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (((O).erase y).erase x) (insert x (insert y (I))))))))))).2.1 (by simpa only [S6, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h6)
  have h7 : IsStack S7 := IsStack_of_LeadsTo_singleton h6 e7
  let S8 : List ℕ := (interval (p + 22) (p + 60)).reverse ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (((O).erase y).erase x) (insert x (insert y (I))))))))
  have eq8 : S7 = S8 := by
    simpa only [S7, S8, List.append_assoc] using congrArg (fun Q : List ℕ => Q ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (((O).erase y).erase x) (insert x (insert y (I))))))))) (join_reversed_intervals p)
  have e8 : LeadsTo S7 {S8} := by
    rw [eq8]
    exact LeadsTo.refl _
  have h8 : IsStack S8 := eq8 ▸ h7
  let S9 : List ℕ := Y ++ (interval (p + 1) (p + 19) ++ (interval (p + 20) (p + 62) ++ (Z ++ (literals pΛ m (((O).erase y).erase x) (insert x (insert y (I)))))))
  have e9 : LeadsTo S8 {S9} := by
    simpa only [S8, S9, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      property_4 (p + 21) (p + 60) (Y ++ (interval (p + 1) (p + 19))) (Z ++ (literals pΛ m (((O).erase y).erase x) (insert x (insert y (I))))) (by omega) (by simpa only [S8, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h8)
  have h9 : IsStack S9 := IsStack_of_LeadsTo_singleton h8 e9
  let S10 : List ℕ := Y ++ (interval (p + 1) (p + 62) ++ (Z ++ (literals pΛ m (((O).erase y).erase x) (insert x (insert y (I))))))
  have eq10 : S9 = S10 := by
    simpa only [S9, S10, List.append_assoc] using congrArg (fun Q : List ℕ => Y ++ Q ++ (Z ++ (literals pΛ m (((O).erase y).erase x) (insert x (insert y (I)))))) (join_intervals p)
  have e10 : LeadsTo S9 {S10} := by
    rw [eq10]
    exact LeadsTo.refl _
  have h10 : IsStack S10 := eq10 ▸ h9
  have ho : ((O).erase y).erase x = O \ {x, y} := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hi : insert x (insert y (I)) = I ∪ {x, y} := by
    ext z
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
    tauto
  simpa only [S0, S10, ho, hi, List.append_assoc] using (LeadsTo.trans_singleton e1 (LeadsTo.trans_singleton e2 (LeadsTo.trans_singleton e3 (LeadsTo.trans_singleton e4 (LeadsTo.trans_singleton e5 (LeadsTo.trans_singleton e6 (LeadsTo.trans_singleton e7 (LeadsTo.trans_singleton e8 (LeadsTo.trans_singleton e9 (e10))))))))))

lemma complete_2_nat (pΛ m p x y : ℕ) (O I : Finset ℕ) (Y Z : List ℕ)
    (hO : O ⊆ Finset.Icc 1 m) (hI : I ⊆ Finset.Icc 1 m) (hOI : Disjoint O I)
    (hxy : x ≠ y) (hxO : x ∈ O) (hyO : y ∈ O)
    (hS : IsStack (hookG'' (p + 21) ++ ([litTest pΛ y] ++ (forkF1 (p + 2) ++ (hookG'' (p + 33) ++ ([litTest pΛ x] ++ (forkF2 (p + 45) ++ (hookH'' (p + 33) ++ (hookH'' (p + 21) ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (O) (I))))))))))))))) :
    LeadsTo (hookG'' (p + 21) ++ ([litTest pΛ y] ++ (forkF1 (p + 2) ++ (hookG'' (p + 33) ++ ([litTest pΛ x] ++ (forkF2 (p + 45) ++ (hookH'' (p + 33) ++ (hookH'' (p + 21) ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (O) (I)))))))))))))) {Y ++ interval (p + 1) (p + 62) ++ Z ++ literals pΛ m (O \ {x, y}) (I ∪ {x, y})} := by
  let S0 : List ℕ := hookG'' (p + 21) ++ ([litTest pΛ y] ++ (forkF1 (p + 2) ++ (hookG'' (p + 33) ++ ([litTest pΛ x] ++ (forkF2 (p + 45) ++ (hookH'' (p + 33) ++ (hookH'' (p + 21) ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (O) (I)))))))))))))
  have h0 : IsStack S0 := hS
  let S1 : List ℕ := [litTest pΛ y] ++ (forkF1 (p + 2) ++ (hookG'' (p + 33) ++ ([litTest pΛ x] ++ (forkF2 (p + 45) ++ (hookH'' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (O) (I))))))))))))
  have e1 : LeadsTo S0 {S1} := by
    simpa only [S0, S1, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      (property_6 (p + 21) ([litTest pΛ y] ++ (forkF1 (p + 2) ++ (hookG'' (p + 33) ++ ([litTest pΛ x] ++ (forkF2 (p + 45) ++ (hookH'' (p + 33))))))) (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (O) (I)))))) []).2.2 (by simpa only [S0, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h0)
  have h1 : IsStack S1 := IsStack_of_LeadsTo_singleton h0 e1
  let S2 : List ℕ := forkF1 (p + 2) ++ (hookG'' (p + 33) ++ ([litTest pΛ x] ++ (forkF2 (p + 45) ++ (hookH'' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m ((O).erase y) (insert y (I))))))))))))
  have e2 : LeadsTo S1 {S2} := by
    simpa only [S1, S2, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      (property_8 pΛ m (O) (I) (forkF1 (p + 2) ++ (hookG'' (p + 33) ++ ([litTest pΛ x] ++ (forkF2 (p + 45) ++ (hookH'' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z)))))))))) hO hI hOI).2.1 y hyO (by simpa only [S1, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h1)
  have h2 : IsStack S2 := IsStack_of_LeadsTo_singleton h1 e2
  have hO1 : (O).erase y ⊆ Finset.Icc 1 m := fun z hz => hO (Finset.mem_erase.mp hz).2
  have hI1 : insert y (I) ⊆ Finset.Icc 1 m := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hO hyO
    · exact hI hz
  have hD1 : Disjoint ((O).erase y) (insert y (I)) := by
    apply Finset.disjoint_left.mpr
    intro z hzO hzI
    rcases Finset.mem_insert.mp hzI with rfl | hzI
    · exact (Finset.mem_erase.mp hzO).1 rfl
    · exact Finset.disjoint_left.mp hOI (Finset.mem_erase.mp hzO).2 hzI
  let S3 : List ℕ := (interval (p + 3) (p + 17)).reverse ++ (hookG'' (p + 33) ++ ([litTest pΛ x] ++ (forkF2 (p + 45) ++ (hookH'' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m ((O).erase y) (insert y (I))))))))))))
  have e3 : LeadsTo S2 {S3} := by
    simpa only [S2, S3, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      (property_7 (p + 2) [] (hookG'' (p + 33) ++ ([litTest pΛ x] ++ (forkF2 (p + 45) ++ (hookH'' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m ((O).erase y) (insert y (I))))))))))))).2.1 (by simpa only [S2, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h2)
  have h3 : IsStack S3 := IsStack_of_LeadsTo_singleton h2 e3
  let S4 : List ℕ := hookG'' (p + 33) ++ ([litTest pΛ x] ++ (forkF2 (p + 45) ++ (hookH'' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m ((O).erase y) (insert y (I)))))))))))
  have e4 : LeadsTo S3 {S4} := by
    simpa only [S3, S4, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      property_4 (p + 2) (p + 17) (hookG'' (p + 33) ++ ([litTest pΛ x] ++ (forkF2 (p + 45) ++ (hookH'' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y)))))) (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m ((O).erase y) (insert y (I))))) (by omega) (by simpa only [S3, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h3)
  have h4 : IsStack S4 := IsStack_of_LeadsTo_singleton h3 e4
  let S5 : List ℕ := [litTest pΛ x] ++ (forkF2 (p + 45) ++ ((interval (p + 34) (p + 45)).reverse ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m ((O).erase y) (insert y (I))))))))))
  have e5 : LeadsTo S4 {S5} := by
    simpa only [S4, S5, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      (property_6 (p + 33) ([litTest pΛ x] ++ (forkF2 (p + 45))) ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m ((O).erase y) (insert y (I)))))))) []).2.2 (by simpa only [S4, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h4)
  have h5 : IsStack S5 := IsStack_of_LeadsTo_singleton h4 e5
  let S6 : List ℕ := forkF2 (p + 45) ++ ((interval (p + 34) (p + 45)).reverse ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (((O).erase y).erase x) (insert x (insert y (I))))))))))
  have e6 : LeadsTo S5 {S6} := by
    simpa only [S5, S6, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      (property_8 pΛ m ((O).erase y) (insert y (I)) (forkF2 (p + 45) ++ ((interval (p + 34) (p + 45)).reverse ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z))))))) hO1 hI1 hD1).2.1 x (by simp [hxO, hxy]) (by simpa only [S5, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h5)
  have h6 : IsStack S6 := IsStack_of_LeadsTo_singleton h5 e6
  let S7 : List ℕ := (interval (p + 46) (p + 60)).reverse ++ ((interval (p + 34) (p + 45)).reverse ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (((O).erase y).erase x) (insert x (insert y (I))))))))))
  have e7 : LeadsTo S6 {S7} := by
    simpa only [S6, S7, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      (property_7 (p + 45) [] ((interval (p + 34) (p + 45)).reverse ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (((O).erase y).erase x) (insert x (insert y (I))))))))))).2.2 (by simpa only [S6, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h6)
  have h7 : IsStack S7 := IsStack_of_LeadsTo_singleton h6 e7
  let S8 : List ℕ := (interval (p + 22) (p + 60)).reverse ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (((O).erase y).erase x) (insert x (insert y (I))))))))
  have eq8 : S7 = S8 := by
    simpa only [S7, S8, List.append_assoc] using congrArg (fun Q : List ℕ => Q ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (((O).erase y).erase x) (insert x (insert y (I))))))))) (join_reversed_intervals p)
  have e8 : LeadsTo S7 {S8} := by
    rw [eq8]
    exact LeadsTo.refl _
  have h8 : IsStack S8 := eq8 ▸ h7
  let S9 : List ℕ := Y ++ (interval (p + 1) (p + 19) ++ (interval (p + 20) (p + 62) ++ (Z ++ (literals pΛ m (((O).erase y).erase x) (insert x (insert y (I)))))))
  have e9 : LeadsTo S8 {S9} := by
    simpa only [S8, S9, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      property_4 (p + 21) (p + 60) (Y ++ (interval (p + 1) (p + 19))) (Z ++ (literals pΛ m (((O).erase y).erase x) (insert x (insert y (I))))) (by omega) (by simpa only [S8, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h8)
  have h9 : IsStack S9 := IsStack_of_LeadsTo_singleton h8 e9
  let S10 : List ℕ := Y ++ (interval (p + 1) (p + 62) ++ (Z ++ (literals pΛ m (((O).erase y).erase x) (insert x (insert y (I))))))
  have eq10 : S9 = S10 := by
    simpa only [S9, S10, List.append_assoc] using congrArg (fun Q : List ℕ => Y ++ Q ++ (Z ++ (literals pΛ m (((O).erase y).erase x) (insert x (insert y (I)))))) (join_intervals p)
  have e10 : LeadsTo S9 {S10} := by
    rw [eq10]
    exact LeadsTo.refl _
  have h10 : IsStack S10 := eq10 ▸ h9
  have ho : ((O).erase y).erase x = O \ {x, y} := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hi : insert x (insert y (I)) = I ∪ {x, y} := by
    ext z
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
    tauto
  simpa only [S0, S10, ho, hi, List.append_assoc] using (LeadsTo.trans_singleton e1 (LeadsTo.trans_singleton e2 (LeadsTo.trans_singleton e3 (LeadsTo.trans_singleton e4 (LeadsTo.trans_singleton e5 (LeadsTo.trans_singleton e6 (LeadsTo.trans_singleton e7 (LeadsTo.trans_singleton e8 (LeadsTo.trans_singleton e9 (e10))))))))))

lemma complete_3_path1_nat (pΛ m p x y : ℕ) (O I : Finset ℕ) (Y Z : List ℕ)
    (hO : O ⊆ Finset.Icc 1 m) (hI : I ⊆ Finset.Icc 1 m) (hOI : Disjoint O I)
    (hxy : x ≠ y) (hxO : x ∈ O) (hyO : y ∈ O)
    (hS : IsStack ([litTest pΛ x] ++ ([hookPut (p + 33)] ++ ([litTest pΛ y] ++ (forkF1 (p + 45) ++ (hookG' (p + 33) ++ ((forkF2 (p + 2)).reverse ++ (hookH' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (O) (I))))))))))))))) :
    LeadsTo ([litTest pΛ x] ++ ([hookPut (p + 33)] ++ ([litTest pΛ y] ++ (forkF1 (p + 45) ++ (hookG' (p + 33) ++ ((forkF2 (p + 2)).reverse ++ (hookH' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (O) (I)))))))))))))) {Y ++ interval (p + 1) (p + 62) ++ Z ++ literals pΛ m (O \ {x, y}) (I ∪ {x, y})} := by
  let S0 : List ℕ := [litTest pΛ x] ++ ([hookPut (p + 33)] ++ ([litTest pΛ y] ++ (forkF1 (p + 45) ++ (hookG' (p + 33) ++ ((forkF2 (p + 2)).reverse ++ (hookH' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (O) (I)))))))))))))
  have h0 : IsStack S0 := hS
  let S1 : List ℕ := [hookPut (p + 33)] ++ ([litTest pΛ y] ++ (forkF1 (p + 45) ++ (hookG' (p + 33) ++ ((forkF2 (p + 2)).reverse ++ (hookH' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m ((O).erase x) (insert x (I)))))))))))))
  have e1 : LeadsTo S0 {S1} := by
    simpa only [S0, S1, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      (property_8 pΛ m (O) (I) ([hookPut (p + 33)] ++ ([litTest pΛ y] ++ (forkF1 (p + 45) ++ (hookG' (p + 33) ++ ((forkF2 (p + 2)).reverse ++ (hookH' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z))))))))))) hO hI hOI).2.1 x hxO (by simpa only [S0, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h0)
  have h1 : IsStack S1 := IsStack_of_LeadsTo_singleton h0 e1
  have hO1 : (O).erase x ⊆ Finset.Icc 1 m := fun z hz => hO (Finset.mem_erase.mp hz).2
  have hI1 : insert x (I) ⊆ Finset.Icc 1 m := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hO hxO
    · exact hI hz
  have hD1 : Disjoint ((O).erase x) (insert x (I)) := by
    apply Finset.disjoint_left.mpr
    intro z hzO hzI
    rcases Finset.mem_insert.mp hzI with rfl | hzI
    · exact (Finset.mem_erase.mp hzO).1 rfl
    · exact Finset.disjoint_left.mp hOI (Finset.mem_erase.mp hzO).2 hzI
  let S2 : List ℕ := forkF2 (p + 2) ++ (hookG'' (p + 33) ++ ([litTest pΛ y] ++ (forkF1 (p + 45) ++ (hookH'' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m ((O).erase x) (insert x (I))))))))))))
  have e2 : LeadsTo S1 {S2} := by
    simpa only [S1, S2, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      (property_6 (p + 33) ([litTest pΛ y] ++ (forkF1 (p + 45))) (forkF2 (p + 2)) ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m ((O).erase x) (insert x (I))))))))).2.1 (by simpa only [S1, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h1)
  have h2 : IsStack S2 := IsStack_of_LeadsTo_singleton h1 e2
  let S3 : List ℕ := (interval (p + 3) (p + 17)).reverse ++ (hookG'' (p + 33) ++ ([litTest pΛ y] ++ (forkF1 (p + 45) ++ (hookH'' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m ((O).erase x) (insert x (I))))))))))))
  have e3 : LeadsTo S2 {S3} := by
    simpa only [S2, S3, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      (property_7 (p + 2) [] (hookG'' (p + 33) ++ ([litTest pΛ y] ++ (forkF1 (p + 45) ++ (hookH'' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m ((O).erase x) (insert x (I))))))))))))).2.2 (by simpa only [S2, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h2)
  have h3 : IsStack S3 := IsStack_of_LeadsTo_singleton h2 e3
  let S4 : List ℕ := hookG'' (p + 33) ++ ([litTest pΛ y] ++ (forkF1 (p + 45) ++ (hookH'' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m ((O).erase x) (insert x (I)))))))))))
  have e4 : LeadsTo S3 {S4} := by
    simpa only [S3, S4, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      property_4 (p + 2) (p + 17) (hookG'' (p + 33) ++ ([litTest pΛ y] ++ (forkF1 (p + 45) ++ (hookH'' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y)))))) (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m ((O).erase x) (insert x (I))))) (by omega) (by simpa only [S3, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h3)
  have h4 : IsStack S4 := IsStack_of_LeadsTo_singleton h3 e4
  let S5 : List ℕ := [litTest pΛ y] ++ (forkF1 (p + 45) ++ ((interval (p + 34) (p + 45)).reverse ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m ((O).erase x) (insert x (I))))))))))
  have e5 : LeadsTo S4 {S5} := by
    simpa only [S4, S5, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      (property_6 (p + 33) ([litTest pΛ y] ++ (forkF1 (p + 45))) ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m ((O).erase x) (insert x (I)))))))) []).2.2 (by simpa only [S4, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h4)
  have h5 : IsStack S5 := IsStack_of_LeadsTo_singleton h4 e5
  let S6 : List ℕ := forkF1 (p + 45) ++ ((interval (p + 34) (p + 45)).reverse ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (((O).erase x).erase y) (insert y (insert x (I))))))))))
  have e6 : LeadsTo S5 {S6} := by
    simpa only [S5, S6, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      (property_8 pΛ m ((O).erase x) (insert x (I)) (forkF1 (p + 45) ++ ((interval (p + 34) (p + 45)).reverse ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z))))))) hO1 hI1 hD1).2.1 y (by simp [hyO, Ne.symm hxy]) (by simpa only [S5, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h5)
  have h6 : IsStack S6 := IsStack_of_LeadsTo_singleton h5 e6
  let S7 : List ℕ := (interval (p + 46) (p + 60)).reverse ++ ((interval (p + 34) (p + 45)).reverse ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (((O).erase x).erase y) (insert y (insert x (I))))))))))
  have e7 : LeadsTo S6 {S7} := by
    simpa only [S6, S7, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      (property_7 (p + 45) [] ((interval (p + 34) (p + 45)).reverse ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (((O).erase x).erase y) (insert y (insert x (I))))))))))).2.1 (by simpa only [S6, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h6)
  have h7 : IsStack S7 := IsStack_of_LeadsTo_singleton h6 e7
  let S8 : List ℕ := (interval (p + 22) (p + 60)).reverse ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (((O).erase x).erase y) (insert y (insert x (I))))))))
  have eq8 : S7 = S8 := by
    simpa only [S7, S8, List.append_assoc] using congrArg (fun Q : List ℕ => Q ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (((O).erase x).erase y) (insert y (insert x (I))))))))) (join_reversed_intervals p)
  have e8 : LeadsTo S7 {S8} := by
    rw [eq8]
    exact LeadsTo.refl _
  have h8 : IsStack S8 := eq8 ▸ h7
  let S9 : List ℕ := Y ++ (interval (p + 1) (p + 19) ++ (interval (p + 20) (p + 62) ++ (Z ++ (literals pΛ m (((O).erase x).erase y) (insert y (insert x (I)))))))
  have e9 : LeadsTo S8 {S9} := by
    simpa only [S8, S9, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      property_4 (p + 21) (p + 60) (Y ++ (interval (p + 1) (p + 19))) (Z ++ (literals pΛ m (((O).erase x).erase y) (insert y (insert x (I))))) (by omega) (by simpa only [S8, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h8)
  have h9 : IsStack S9 := IsStack_of_LeadsTo_singleton h8 e9
  let S10 : List ℕ := Y ++ (interval (p + 1) (p + 62) ++ (Z ++ (literals pΛ m (((O).erase x).erase y) (insert y (insert x (I))))))
  have eq10 : S9 = S10 := by
    simpa only [S9, S10, List.append_assoc] using congrArg (fun Q : List ℕ => Y ++ Q ++ (Z ++ (literals pΛ m (((O).erase x).erase y) (insert y (insert x (I)))))) (join_intervals p)
  have e10 : LeadsTo S9 {S10} := by
    rw [eq10]
    exact LeadsTo.refl _
  have h10 : IsStack S10 := eq10 ▸ h9
  have ho : ((O).erase x).erase y = O \ {x, y} := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hi : insert y (insert x (I)) = I ∪ {x, y} := by
    ext z
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
    tauto
  simpa only [S0, S10, ho, hi, List.append_assoc] using (LeadsTo.trans_singleton e1 (LeadsTo.trans_singleton e2 (LeadsTo.trans_singleton e3 (LeadsTo.trans_singleton e4 (LeadsTo.trans_singleton e5 (LeadsTo.trans_singleton e6 (LeadsTo.trans_singleton e7 (LeadsTo.trans_singleton e8 (LeadsTo.trans_singleton e9 (e10))))))))))

lemma complete_3_path2_nat (pΛ m p x y : ℕ) (O I : Finset ℕ) (Y Z : List ℕ)
    (hO : O ⊆ Finset.Icc 1 m) (hI : I ⊆ Finset.Icc 1 m) (hOI : Disjoint O I)
    (hxy : x ≠ y) (hxO : x ∈ O) (hyO : y ∈ O)
    (hS : IsStack ([litTest pΛ y] ++ ([hookPut (p + 33)] ++ ([litTest pΛ x] ++ (forkF2 (p + 45) ++ (hookG' (p + 33) ++ ((forkF2 (p + 2)).reverse ++ (hookH' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (O) (I))))))))))))))) :
    LeadsTo ([litTest pΛ y] ++ ([hookPut (p + 33)] ++ ([litTest pΛ x] ++ (forkF2 (p + 45) ++ (hookG' (p + 33) ++ ((forkF2 (p + 2)).reverse ++ (hookH' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (O) (I)))))))))))))) {Y ++ interval (p + 1) (p + 62) ++ Z ++ literals pΛ m (O \ {x, y}) (I ∪ {x, y})} := by
  let S0 : List ℕ := [litTest pΛ y] ++ ([hookPut (p + 33)] ++ ([litTest pΛ x] ++ (forkF2 (p + 45) ++ (hookG' (p + 33) ++ ((forkF2 (p + 2)).reverse ++ (hookH' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (O) (I)))))))))))))
  have h0 : IsStack S0 := hS
  let S1 : List ℕ := [hookPut (p + 33)] ++ ([litTest pΛ x] ++ (forkF2 (p + 45) ++ (hookG' (p + 33) ++ ((forkF2 (p + 2)).reverse ++ (hookH' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m ((O).erase y) (insert y (I)))))))))))))
  have e1 : LeadsTo S0 {S1} := by
    simpa only [S0, S1, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      (property_8 pΛ m (O) (I) ([hookPut (p + 33)] ++ ([litTest pΛ x] ++ (forkF2 (p + 45) ++ (hookG' (p + 33) ++ ((forkF2 (p + 2)).reverse ++ (hookH' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z))))))))))) hO hI hOI).2.1 y hyO (by simpa only [S0, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h0)
  have h1 : IsStack S1 := IsStack_of_LeadsTo_singleton h0 e1
  have hO1 : (O).erase y ⊆ Finset.Icc 1 m := fun z hz => hO (Finset.mem_erase.mp hz).2
  have hI1 : insert y (I) ⊆ Finset.Icc 1 m := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hO hyO
    · exact hI hz
  have hD1 : Disjoint ((O).erase y) (insert y (I)) := by
    apply Finset.disjoint_left.mpr
    intro z hzO hzI
    rcases Finset.mem_insert.mp hzI with rfl | hzI
    · exact (Finset.mem_erase.mp hzO).1 rfl
    · exact Finset.disjoint_left.mp hOI (Finset.mem_erase.mp hzO).2 hzI
  let S2 : List ℕ := forkF2 (p + 2) ++ (hookG'' (p + 33) ++ ([litTest pΛ x] ++ (forkF2 (p + 45) ++ (hookH'' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m ((O).erase y) (insert y (I))))))))))))
  have e2 : LeadsTo S1 {S2} := by
    simpa only [S1, S2, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      (property_6 (p + 33) ([litTest pΛ x] ++ (forkF2 (p + 45))) (forkF2 (p + 2)) ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m ((O).erase y) (insert y (I))))))))).2.1 (by simpa only [S1, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h1)
  have h2 : IsStack S2 := IsStack_of_LeadsTo_singleton h1 e2
  let S3 : List ℕ := (interval (p + 3) (p + 17)).reverse ++ (hookG'' (p + 33) ++ ([litTest pΛ x] ++ (forkF2 (p + 45) ++ (hookH'' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m ((O).erase y) (insert y (I))))))))))))
  have e3 : LeadsTo S2 {S3} := by
    simpa only [S2, S3, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      (property_7 (p + 2) [] (hookG'' (p + 33) ++ ([litTest pΛ x] ++ (forkF2 (p + 45) ++ (hookH'' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m ((O).erase y) (insert y (I))))))))))))).2.2 (by simpa only [S2, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h2)
  have h3 : IsStack S3 := IsStack_of_LeadsTo_singleton h2 e3
  let S4 : List ℕ := hookG'' (p + 33) ++ ([litTest pΛ x] ++ (forkF2 (p + 45) ++ (hookH'' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m ((O).erase y) (insert y (I)))))))))))
  have e4 : LeadsTo S3 {S4} := by
    simpa only [S3, S4, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      property_4 (p + 2) (p + 17) (hookG'' (p + 33) ++ ([litTest pΛ x] ++ (forkF2 (p + 45) ++ (hookH'' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y)))))) (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m ((O).erase y) (insert y (I))))) (by omega) (by simpa only [S3, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h3)
  have h4 : IsStack S4 := IsStack_of_LeadsTo_singleton h3 e4
  let S5 : List ℕ := [litTest pΛ x] ++ (forkF2 (p + 45) ++ ((interval (p + 34) (p + 45)).reverse ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m ((O).erase y) (insert y (I))))))))))
  have e5 : LeadsTo S4 {S5} := by
    simpa only [S4, S5, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      (property_6 (p + 33) ([litTest pΛ x] ++ (forkF2 (p + 45))) ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m ((O).erase y) (insert y (I)))))))) []).2.2 (by simpa only [S4, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h4)
  have h5 : IsStack S5 := IsStack_of_LeadsTo_singleton h4 e5
  let S6 : List ℕ := forkF2 (p + 45) ++ ((interval (p + 34) (p + 45)).reverse ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (((O).erase y).erase x) (insert x (insert y (I))))))))))
  have e6 : LeadsTo S5 {S6} := by
    simpa only [S5, S6, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      (property_8 pΛ m ((O).erase y) (insert y (I)) (forkF2 (p + 45) ++ ((interval (p + 34) (p + 45)).reverse ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z))))))) hO1 hI1 hD1).2.1 x (by simp [hxO, hxy]) (by simpa only [S5, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h5)
  have h6 : IsStack S6 := IsStack_of_LeadsTo_singleton h5 e6
  let S7 : List ℕ := (interval (p + 46) (p + 60)).reverse ++ ((interval (p + 34) (p + 45)).reverse ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (((O).erase y).erase x) (insert x (insert y (I))))))))))
  have e7 : LeadsTo S6 {S7} := by
    simpa only [S6, S7, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      (property_7 (p + 45) [] ((interval (p + 34) (p + 45)).reverse ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (((O).erase y).erase x) (insert x (insert y (I))))))))))).2.2 (by simpa only [S6, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h6)
  have h7 : IsStack S7 := IsStack_of_LeadsTo_singleton h6 e7
  let S8 : List ℕ := (interval (p + 22) (p + 60)).reverse ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (((O).erase y).erase x) (insert x (insert y (I))))))))
  have eq8 : S7 = S8 := by
    simpa only [S7, S8, List.append_assoc] using congrArg (fun Q : List ℕ => Q ++ (Y ++ (interval (p + 1) (p + 19) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (((O).erase y).erase x) (insert x (insert y (I))))))))) (join_reversed_intervals p)
  have e8 : LeadsTo S7 {S8} := by
    rw [eq8]
    exact LeadsTo.refl _
  have h8 : IsStack S8 := eq8 ▸ h7
  let S9 : List ℕ := Y ++ (interval (p + 1) (p + 19) ++ (interval (p + 20) (p + 62) ++ (Z ++ (literals pΛ m (((O).erase y).erase x) (insert x (insert y (I)))))))
  have e9 : LeadsTo S8 {S9} := by
    simpa only [S8, S9, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      property_4 (p + 21) (p + 60) (Y ++ (interval (p + 1) (p + 19))) (Z ++ (literals pΛ m (((O).erase y).erase x) (insert x (insert y (I))))) (by omega) (by simpa only [S8, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h8)
  have h9 : IsStack S9 := IsStack_of_LeadsTo_singleton h8 e9
  let S10 : List ℕ := Y ++ (interval (p + 1) (p + 62) ++ (Z ++ (literals pΛ m (((O).erase y).erase x) (insert x (insert y (I))))))
  have eq10 : S9 = S10 := by
    simpa only [S9, S10, List.append_assoc] using congrArg (fun Q : List ℕ => Y ++ Q ++ (Z ++ (literals pΛ m (((O).erase y).erase x) (insert x (insert y (I)))))) (join_intervals p)
  have e10 : LeadsTo S9 {S10} := by
    rw [eq10]
    exact LeadsTo.refl _
  have h10 : IsStack S10 := eq10 ▸ h9
  have ho : ((O).erase y).erase x = O \ {x, y} := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hi : insert x (insert y (I)) = I ∪ {x, y} := by
    ext z
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
    tauto
  simpa only [S0, S10, ho, hi, List.append_assoc] using (LeadsTo.trans_singleton e1 (LeadsTo.trans_singleton e2 (LeadsTo.trans_singleton e3 (LeadsTo.trans_singleton e4 (LeadsTo.trans_singleton e5 (LeadsTo.trans_singleton e6 (LeadsTo.trans_singleton e7 (LeadsTo.trans_singleton e8 (LeadsTo.trans_singleton e9 (e10))))))))))

lemma complete_3_nat (pΛ m p x y : ℕ) (O I : Finset ℕ) (Y Z : List ℕ)
    (hO : O ⊆ Finset.Icc 1 m) (hI : I ⊆ Finset.Icc 1 m) (hOI : Disjoint O I)
    (hxy : x ≠ y) (hxO : x ∈ O) (hyO : y ∈ O)
    (hS : IsStack (hookG'' (p + 21) ++ ([hookTake (p + 33)] ++ (forkF2 (p + 2) ++ (hookG (p + 33) ++ (forkE (p + 45) ++ ([litTest pΛ x] ++ ([hookPut (p + 33)] ++ ([litTest pΛ y] ++ (forkF (p + 45) ++ (hookH (p + 33) ++ (hookH'' (p + 21) ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (O) (I)))))))))))))))))) :
    LeadsTo (hookG'' (p + 21) ++ ([hookTake (p + 33)] ++ (forkF2 (p + 2) ++ (hookG (p + 33) ++ (forkE (p + 45) ++ ([litTest pΛ x] ++ ([hookPut (p + 33)] ++ ([litTest pΛ y] ++ (forkF (p + 45) ++ (hookH (p + 33) ++ (hookH'' (p + 21) ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (O) (I))))))))))))))))) {Y ++ interval (p + 1) (p + 62) ++ Z ++ literals pΛ m (O \ {x, y}) (I ∪ {x, y})} := by
  let S0 : List ℕ := hookG'' (p + 21) ++ ([hookTake (p + 33)] ++ (forkF2 (p + 2) ++ (hookG (p + 33) ++ (forkE (p + 45) ++ ([litTest pΛ x] ++ ([hookPut (p + 33)] ++ ([litTest pΛ y] ++ (forkF (p + 45) ++ (hookH (p + 33) ++ (hookH'' (p + 21) ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (O) (I))))))))))))))))
  have h0 : IsStack S0 := hS
  let S1 : List ℕ := [hookTake (p + 33)] ++ (forkF2 (p + 2) ++ (hookG (p + 33) ++ (forkE (p + 45) ++ ([litTest pΛ x] ++ ([hookPut (p + 33)] ++ ([litTest pΛ y] ++ (forkF (p + 45) ++ (hookH (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (O) (I)))))))))))))))
  have e1 : LeadsTo S0 {S1} := by
    simpa only [S0, S1, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      (property_6 (p + 21) ([hookTake (p + 33)] ++ (forkF2 (p + 2) ++ (hookG (p + 33) ++ (forkE (p + 45) ++ ([litTest pΛ x] ++ ([hookPut (p + 33)] ++ ([litTest pΛ y] ++ (forkF (p + 45) ++ (hookH (p + 33)))))))))) (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (O) (I)))))) []).2.2 (by simpa only [S0, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h0)
  have h1 : IsStack S1 := IsStack_of_LeadsTo_singleton h0 e1
  let S2 : List ℕ := forkE (p + 45) ++ ([litTest pΛ x] ++ ([hookPut (p + 33)] ++ ([litTest pΛ y] ++ (forkF (p + 45) ++ (hookG' (p + 33) ++ ((forkF2 (p + 2)).reverse ++ (hookH' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (O) (I))))))))))))))
  have e2 : LeadsTo S1 {S2} := by
    simpa only [S1, S2, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      (property_6 (p + 33) (forkF2 (p + 2)) (forkE (p + 45) ++ ([litTest pΛ x] ++ ([hookPut (p + 33)] ++ ([litTest pΛ y] ++ (forkF (p + 45)))))) ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (O) (I)))))))).1 (by simpa only [S1, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h1)
  have h2 : IsStack S2 := IsStack_of_LeadsTo_singleton h1 e2
  let A : List ℕ := [litTest pΛ x] ++ ([hookPut (p + 33)] ++ ([litTest pΛ y] ++ (forkF1 (p + 45) ++ (hookG' (p + 33) ++ ((forkF2 (p + 2)).reverse ++ (hookH' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (O) (I)))))))))))))
  let B : List ℕ := [litTest pΛ y] ++ ([hookPut (p + 33)] ++ ([litTest pΛ x] ++ (forkF2 (p + 45) ++ (hookG' (p + 33) ++ ((forkF2 (p + 2)).reverse ++ (hookH' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (O) (I)))))))))))))
  have split : LeadsTo S2 {A, B} := by
    simpa only [S2, A, B, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using
      (property_7 (p + 45) ([litTest pΛ x] ++ ([hookPut (p + 33)] ++ ([litTest pΛ y]))) (hookG' (p + 33) ++ ((forkF2 (p + 2)).reverse ++ (hookH' (p + 33) ++ ((interval (p + 22) (p + 33)).reverse ++ (Y ++ (Dock (p + 2) (p + 17) ++ (Dock (p + 21) (p + 60) ++ (Z ++ (literals pΛ m (O) (I))))))))))).1 (by simpa only [S2, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append, List.append_nil, List.reverse_append, List.reverse_singleton, List.reverse_reverse, List.reverse_cons, List.reverse_nil, Nat.add_assoc, offset_sub_two, offset_sub_twentyone] using h2)
  have hA : IsStack A := by
    obtain ⟨π, hπ⟩ := split.1 A (by simp)
    exact IsStack_of_IsEfficientPath π _ _ h2 hπ
  have hB : IsStack B := by
    obtain ⟨π, hπ⟩ := split.1 B (by simp)
    exact IsStack_of_IsEfficientPath π _ _ h2 hπ
  have finish : LeadsTo S2 {Y ++ interval (p + 1) (p + 62) ++ Z ++ literals pΛ m (O \ {x, y}) (I ∪ {x, y})} :=
    LeadsTo.pair_same split
      (complete_3_path1_nat pΛ m p x y O I Y Z hO hI hOI hxy hxO hyO hA)
      (complete_3_path2_nat pΛ m p x y O I Y Z hO hI hOI hxy hxO hyO hB)
  exact LeadsTo.trans_singleton e1 (LeadsTo.trans_singleton e2 (finish))

end PancakeHard

open PancakeHard

theorem solution (pΛ m : ℕ) (p : ℤ) (hp : -2 ≤ p) (a b c : ℕ) (O I : Finset ℕ) (Y Z : List ℕ)
    (ha : a ∈ Finset.Icc 1 m) (hb : b ∈ Finset.Icc 1 m) (hc : c ∈ Finset.Icc 1 m)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hO : O ⊆ Finset.Icc 1 m)
    (hI : I ⊆ Finset.Icc 1 m) (hOI : Disjoint O I) :
    (b ∈ O → c ∈ O →
      IsStack (clauseΓ1 pΛ b c p ++ Y ++ clauseΔ p ++ Z ++ literals pΛ m O I) →
      LeadsTo (clauseΓ1 pΛ b c p ++ Y ++ clauseΔ p ++ Z ++ literals pΛ m O I)
        {Y ++ interval (p + 1).toNat (p + 62).toNat ++ Z ++ literals pΛ m (O \ {b, c}) (I ∪ {b, c})}) ∧
    (a ∈ O → c ∈ O →
      IsStack (clauseΓ2 pΛ a c p ++ Y ++ clauseΔ p ++ Z ++ literals pΛ m O I) →
      LeadsTo (clauseΓ2 pΛ a c p ++ Y ++ clauseΔ p ++ Z ++ literals pΛ m O I)
        {Y ++ interval (p + 1).toNat (p + 62).toNat ++ Z ++ literals pΛ m (O \ {a, c}) (I ∪ {a, c})}) ∧
    (a ∈ O → b ∈ O →
      IsStack (clauseΓ3 pΛ a b p ++ Y ++ clauseΔ p ++ Z ++ literals pΛ m O I) →
      LeadsTo (clauseΓ3 pΛ a b p ++ Y ++ clauseΔ p ++ Z ++ literals pΛ m O I)
        {Y ++ interval (p + 1).toNat (p + 62).toNat ++ Z ++ literals pΛ m (O \ {a, b}) (I ∪ {a, b})}) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hx hy hS
    have hp0 := clause_offset_nonneg pΛ m p _ Y Z O I hS
    lift p to ℕ using hp0
    simp only [clauseΓ1, clauseΔ, nat_cast_1, nat_cast_2, nat_cast_17, nat_cast_21,
      nat_cast_33, nat_cast_45, nat_cast_60, nat_cast_62, List.append_assoc,
      List.cons_append, List.nil_append] at hS ⊢
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      complete_1_nat pΛ m p b c O I Y Z hO hI hOI hbc hx hy hS
  · intro hx hy hS
    have hp0 := clause_offset_nonneg pΛ m p _ Y Z O I hS
    lift p to ℕ using hp0
    simp only [clauseΓ2, clauseΔ, nat_cast_1, nat_cast_2, nat_cast_17, nat_cast_21,
      nat_cast_33, nat_cast_45, nat_cast_60, nat_cast_62, List.append_assoc,
      List.cons_append, List.nil_append] at hS ⊢
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      complete_2_nat pΛ m p a c O I Y Z hO hI hOI hac hx hy hS
  · intro hx hy hS
    have hp0 := clause_offset_nonneg pΛ m p _ Y Z O I hS
    lift p to ℕ using hp0
    simp only [clauseΓ3, clauseΔ, nat_cast_1, nat_cast_2, nat_cast_17, nat_cast_21,
      nat_cast_33, nat_cast_45, nat_cast_60, nat_cast_62, List.append_assoc,
      List.cons_append, List.nil_append] at hS ⊢
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      complete_3_nat pΛ m p a b O I Y Z hO hI hOI hab hx hy hS
