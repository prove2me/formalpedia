-- Prove2me | solution 1 for PancakeHard.property_10
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-10T14:26:41.504674+00:00
-- url     : https://prove2.me/submissions/c86bdf35-2049-4bd7-9ccc-d8d4f186b0e2

import Mathlib
import Definitions.Def_PancakeHard_Clause
import Theorems.Thm_PancakeHard_property_6
import Theorems.Thm_PancakeHard_property_7
import Theorems.Thm_PancakeHard_property_8

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace PancakeHard

/-! ### from PH10_helpers.lean -/

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

private lemma no_eff_path_of_deadlock {S : List ℕ} (h : IsDeadlock S)
    (π : List (List ℕ)) (hπ : IsEfficientPath π S (identity S.length)) : False := by
  obtain ⟨hne, hno⟩ := h
  obtain ⟨hd, tl, ch⟩ := hπ
  match π with
  | [] => simp at hd
  | a :: t =>
    have ha : a = S := by
      simpa using hd
    match t with
    | [] =>
      have hid : a = identity S.length := by
        simpa using Option.some_injective _ tl
      exact hne (by simpa [ha] using hid)
    | b :: _u =>
      have hef : EfficientFlip a b := (List.isChain_cons_cons.1 ch).1
      exact hno b (by simpa [ha] using hef)

lemma LeadsTo.of_deadlock {S : List ℕ} (h : IsDeadlock S) : LeadsTo S (∅ : Set (List ℕ)) := by
  refine ⟨fun T hT => False.elim hT, ?_⟩
  intro π hπ
  exact False.elim (no_eff_path_of_deadlock h π hπ)

/-! ### from PH10_unfold.lean -/

lemma clauseGamma_eq (p : ℤ) : clauseGamma p = hookTake (p + 21).toNat := rfl

lemma clauseΓ_eq (pΛ a b c : ℕ) (p : ℤ) :
    clauseΓ pΛ a b c p =
      hookG (p + 21).toNat ++ forkE (p + 2).toNat ++
        [hookTake (p + 33).toNat, hookPut (p + 21).toNat, litTest pΛ c] ++
        forkF (p + 2).toNat ++ hookG (p + 33).toNat ++ forkE (p + 45).toNat ++
        [litTest pΛ a, hookPut (p + 33).toNat, litTest pΛ b] ++
        forkF (p + 45).toNat ++ hookH (p + 33).toNat ++ hookH (p + 21).toNat := rfl

lemma clauseΓ1_eq (pΛ b c : ℕ) (p : ℤ) :
    clauseΓ1 pΛ b c p =
      hookG'' (p + 21).toNat ++ [litTest pΛ c] ++ forkF1 (p + 2).toNat ++
        hookG'' (p + 33).toNat ++ [litTest pΛ b] ++ forkF1 (p + 45).toNat ++
        hookH'' (p + 33).toNat ++ hookH'' (p + 21).toNat := rfl

lemma clauseΓ2_eq (pΛ a c : ℕ) (p : ℤ) :
    clauseΓ2 pΛ a c p =
      hookG'' (p + 21).toNat ++ [litTest pΛ c] ++ forkF1 (p + 2).toNat ++
        hookG'' (p + 33).toNat ++ [litTest pΛ a] ++ forkF2 (p + 45).toNat ++
        hookH'' (p + 33).toNat ++ hookH'' (p + 21).toNat := rfl

lemma clauseΓ3_eq (pΛ a b : ℕ) (p : ℤ) :
    clauseΓ3 pΛ a b p =
      hookG'' (p + 21).toNat ++ [hookTake (p + 33).toNat] ++ forkF2 (p + 2).toNat ++
        hookG (p + 33).toNat ++ forkE (p + 45).toNat ++
        [litTest pΛ a, hookPut (p + 33).toNat, litTest pΛ b] ++
        forkF (p + 45).toNat ++ hookH (p + 33).toNat ++ hookH'' (p + 21).toNat := rfl

/-- Rearrangement of the Property 10 start state into Hook(p+21) form. -/
lemma prop10_start_eq (pΛ a b c : ℕ) (p : ℤ) (X Y Z : List ℕ) :
    let p1 := (p + 21).toNat
    let p0 := (p + 2).toNat
    let p2 := (p + 33).toNat
    let p3 := (p + 45).toNat
    let Yh :=
      forkE p0 ++ [hookTake p2, hookPut p1, litTest pΛ c] ++ forkF p0 ++
        hookG p2 ++ forkE p3 ++ [litTest pΛ a, hookPut p2, litTest pΛ b] ++
        forkF p3 ++ hookH p2
    clauseGamma p :: X ++ clauseΓ pΛ a b c p ++ Y ++ Z =
      hookTake p1 :: X ++ hookG p1 ++ Yh ++ hookH p1 ++ (Y ++ Z) := by
  intro p1 p0 p2 p3 Yh
  simp [clauseGamma_eq, clauseΓ_eq, Yh, p1, p0, p2, p3, List.append_assoc, List.cons_append]

/-- After Hook.a + identifying the Fork(p+2) spine. -/
lemma prop10_after_hook_eq (pΛ a b c : ℕ) (p : ℤ) (X Y Z : List ℕ) :
    let p1 := (p + 21).toNat
    let p0 := (p + 2).toNat
    let p2 := (p + 33).toNat
    let p3 := (p + 45).toNat
    let Xf := [hookTake p2, hookPut p1, litTest pΛ c]
    let Zf :=
      hookG p2 ++ forkE p3 ++ [litTest pΛ a, hookPut p2, litTest pΛ b] ++
        forkF p3 ++ hookH p2 ++ hookG' p1 ++ X.reverse ++ hookH' p1 ++ (Y ++ Z)
    let Yh :=
      forkE p0 ++ Xf ++ forkF p0 ++
        hookG p2 ++ forkE p3 ++ [litTest pΛ a, hookPut p2, litTest pΛ b] ++
        forkF p3 ++ hookH p2
    Yh ++ hookG' p1 ++ X.reverse ++ hookH' p1 ++ (Y ++ Z) =
      forkE p0 ++ Xf ++ forkF p0 ++ Zf := by
  intro p1 p0 p2 p3 Xf Zf Yh
  simp [Yh, Xf, Zf, List.append_assoc]

/-! ### from PH10_spine.lean -/

/-- First two steps of Property 10: Hook(p+21).a then Fork(p+2).a, landing on {S0, S3}. -/
lemma prop10_hook_fork1
    (pΛ m : ℕ) (p : ℤ) (_hp : -2 ≤ p) (a b c : ℕ) (O I : Finset ℕ) (X Y : List ℕ)
    (_ha : a ∈ Finset.Icc 1 m) (_hb : b ∈ Finset.Icc 1 m) (_hc : c ∈ Finset.Icc 1 m)
    (_hab : a ≠ b) (_hac : a ≠ c) (_hbc : b ≠ c)
    (_hO : O ⊆ Finset.Icc 1 m) (_hI : I ⊆ Finset.Icc 1 m) (_hOI : Disjoint O I)
    (hS : IsStack (clauseGamma p :: X ++ clauseΓ pΛ a b c p ++ Y ++ literals pΛ m O I)) :
    let p1 := (p + 21).toNat
    let p0 := (p + 2).toNat
    let p2 := (p + 33).toNat
    let p3 := (p + 45).toNat
    let Zh := Y ++ literals pΛ m O I
    let Xf := [hookTake p2, hookPut p1, litTest pΛ c]
    let Zf :=
      hookG p2 ++ forkE p3 ++ [litTest pΛ a, hookPut p2, litTest pΛ b] ++
        forkF p3 ++ hookH p2 ++ hookG' p1 ++ X.reverse ++ hookH' p1 ++ Zh
    let S0 := Xf ++ forkF1 p0 ++ Zf
    let S3 := Xf.reverse ++ forkF2 p0 ++ Zf
    LeadsTo (clauseGamma p :: X ++ clauseΓ pΛ a b c p ++ Y ++ literals pΛ m O I) {S0, S3} := by
  intro p1 p0 p2 p3 Zh Xf Zf S0 S3
  set Yh : List ℕ :=
    forkE p0 ++ [hookTake p2, hookPut p1, litTest pΛ c] ++ forkF p0 ++
      hookG p2 ++ forkE p3 ++ [litTest pΛ a, hookPut p2, litTest pΛ b] ++
      forkF p3 ++ hookH p2
  have hArr :
      clauseGamma p :: X ++ clauseΓ pΛ a b c p ++ Y ++ literals pΛ m O I =
        hookTake p1 :: X ++ hookG p1 ++ Yh ++ hookH p1 ++ Zh := by
    simpa [Zh, Yh, p1, p0, p2, p3] using prop10_start_eq pΛ a b c p X Y (literals pΛ m O I)
  rw [hArr] at hS ⊢
  have hHook : LeadsTo (hookTake p1 :: X ++ hookG p1 ++ Yh ++ hookH p1 ++ Zh)
      {Yh ++ hookG' p1 ++ X.reverse ++ hookH' p1 ++ Zh} :=
    (property_6 p1 X Yh Zh).1 hS
  set T0 : List ℕ := Yh ++ hookG' p1 ++ X.reverse ++ hookH' p1 ++ Zh
  have hStackT0 : IsStack T0 := IsStack_of_LeadsTo_singleton hS hHook
  have hT0eq : T0 = forkE p0 ++ Xf ++ forkF p0 ++ Zf := by
    simp [T0, Yh, Xf, Zf, Zh, List.append_assoc]
  have hStackT0' : IsStack (forkE p0 ++ Xf ++ forkF p0 ++ Zf) := by
    rwa [← hT0eq]
  have hFork : LeadsTo (forkE p0 ++ Xf ++ forkF p0 ++ Zf)
      {Xf ++ forkF1 p0 ++ Zf, Xf.reverse ++ forkF2 p0 ++ Zf} :=
    (property_7 p0 Xf Zf).1 hStackT0'
  have hHook' : LeadsTo (hookTake p1 :: X ++ hookG p1 ++ Yh ++ hookH p1 ++ Zh) {T0} := by
    simpa [T0] using hHook
  have hFork' : LeadsTo T0 {S0, S3} := by
    simpa [T0, hT0eq, S0, S3] using hFork
  exact LeadsTo.trans_singleton hHook' hFork'

/-- From S0: Hook(p+33).a then Fork(p+45).a → {S1, S2}.
S0 = take₂::put₁::test_c ++ F₁¹ ++ G₂ ++ E₂ ++ [test_a,put₂,test_b] ++ F₂ ++ H₂ ++ G₁' ++ ★X ++ H₁' ++ Zh -/
lemma prop10_from_S0
    (pΛ : ℕ) (p : ℤ) (a b c : ℕ) (X : List ℕ) (Zh : List ℕ)
    (hS0 : IsStack (
      let p1 := (p + 21).toNat
      let p0 := (p + 2).toNat
      let p2 := (p + 33).toNat
      let p3 := (p + 45).toNat
      let Xf := [hookTake p2, hookPut p1, litTest pΛ c]
      let Zf :=
        hookG p2 ++ forkE p3 ++ [litTest pΛ a, hookPut p2, litTest pΛ b] ++
          forkF p3 ++ hookH p2 ++ hookG' p1 ++ X.reverse ++ hookH' p1 ++ Zh
      Xf ++ forkF1 p0 ++ Zf)) :
    let p1 := (p + 21).toNat
    let p0 := (p + 2).toNat
    let p2 := (p + 33).toNat
    let p3 := (p + 45).toNat
    let Xh := [hookPut p1, litTest pΛ c] ++ forkF1 p0
    let Yh := forkE p3 ++ [litTest pΛ a, hookPut p2, litTest pΛ b] ++ forkF p3
    let Zh2 := hookG' p1 ++ X.reverse ++ hookH' p1 ++ Zh
    let Xg := [litTest pΛ a, hookPut p2, litTest pΛ b]
    let Zg := hookG' p2 ++ Xh.reverse ++ hookH' p2 ++ Zh2
    let S1 := Xg ++ forkF1 p3 ++ Zg
    let S2 := Xg.reverse ++ forkF2 p3 ++ Zg
    LeadsTo (
      let Xf := [hookTake p2, hookPut p1, litTest pΛ c]
      let Zf :=
        hookG p2 ++ forkE p3 ++ [litTest pΛ a, hookPut p2, litTest pΛ b] ++
          forkF p3 ++ hookH p2 ++ hookG' p1 ++ X.reverse ++ hookH' p1 ++ Zh
      Xf ++ forkF1 p0 ++ Zf) {S1, S2} := by
  intro p1 p0 p2 p3 Xh Yh Zh2 Xg Zg S1 S2
  set Xf : List ℕ := [hookTake p2, hookPut p1, litTest pΛ c]
  set Zf : List ℕ :=
    hookG p2 ++ forkE p3 ++ [litTest pΛ a, hookPut p2, litTest pΛ b] ++
      forkF p3 ++ hookH p2 ++ hookG' p1 ++ X.reverse ++ hookH' p1 ++ Zh
  set S0 : List ℕ := Xf ++ forkF1 p0 ++ Zf
  have hS0' : IsStack S0 := by simpa [S0, Xf, Zf, p1, p0, p2, p3] using hS0
  -- S0 = take2 :: Xh ++ G2 ++ Yh ++ H2 ++ Zh2
  have hArr : S0 = hookTake p2 :: Xh ++ hookG p2 ++ Yh ++ hookH p2 ++ Zh2 := by
    simp [S0, Xf, Zf, Xh, Yh, Zh2, List.append_assoc, List.cons_append]
  rw [hArr] at hS0' ⊢
  have hHook : LeadsTo (hookTake p2 :: Xh ++ hookG p2 ++ Yh ++ hookH p2 ++ Zh2)
      {Yh ++ hookG' p2 ++ Xh.reverse ++ hookH' p2 ++ Zh2} :=
    (property_6 p2 Xh Yh Zh2).1 hS0'
  set T1 : List ℕ := Yh ++ hookG' p2 ++ Xh.reverse ++ hookH' p2 ++ Zh2
  have hStackT1 : IsStack T1 := IsStack_of_LeadsTo_singleton hS0' hHook
  have hT1eq : T1 = forkE p3 ++ Xg ++ forkF p3 ++ Zg := by
    simp [T1, Yh, Xg, Zg, Xh, Zh2, List.append_assoc]
  have hStackT1' : IsStack (forkE p3 ++ Xg ++ forkF p3 ++ Zg) := by
    rwa [← hT1eq]
  have hFork : LeadsTo (forkE p3 ++ Xg ++ forkF p3 ++ Zg)
      {Xg ++ forkF1 p3 ++ Zg, Xg.reverse ++ forkF2 p3 ++ Zg} :=
    (property_7 p3 Xg Zg).1 hStackT1'
  have hHook' : LeadsTo (hookTake p2 :: Xh ++ hookG p2 ++ Yh ++ hookH p2 ++ Zh2) {T1} := by
    simpa [T1] using hHook
  have hFork' : LeadsTo T1 {S1, S2} := by
    simpa [T1, hT1eq, S1, S2] using hFork
  exact LeadsTo.trans_singleton hHook' hFork'

/-! ### from PH10_branches.lean -/

lemma LeadsTo.of_set_eq {S : List ℕ} {𝕋₁ 𝕋₂ : Set (List ℕ)}
    (h : LeadsTo S 𝕋₁) (heq : 𝕋₁ = 𝕋₂) : LeadsTo S 𝕋₂ :=
  heq ▸ h

/-- S1 branch (head `test_a`). -/
lemma prop10_from_S1
    (pΛ m : ℕ) (p : ℤ) (a b c : ℕ) (O I : Finset ℕ) (X Y : List ℕ)
    (ha : a ∈ Finset.Icc 1 m)
    (hO : O ⊆ Finset.Icc 1 m) (hI : I ⊆ Finset.Icc 1 m) (hOI : Disjoint O I)
    (hS1 : IsStack (
      let p1 := (p + 21).toNat
      let p0 := (p + 2).toNat
      let p2 := (p + 33).toNat
      let p3 := (p + 45).toNat
      let Xh := [hookPut p1, litTest pΛ c] ++ forkF1 p0
      let Zh2 := hookG' p1 ++ X.reverse ++ hookH' p1 ++ Y ++ literals pΛ m O I
      let Xg := [litTest pΛ a, hookPut p2, litTest pΛ b]
      let Zg := hookG' p2 ++ Xh.reverse ++ hookH' p2 ++ Zh2
      Xg ++ forkF1 p3 ++ Zg)) :
    let p1 := (p + 21).toNat
    let p0 := (p + 2).toNat
    let p2 := (p + 33).toNat
    let p3 := (p + 45).toNat
    let Xh := [hookPut p1, litTest pΛ c] ++ forkF1 p0
    let Zh2 := hookG' p1 ++ X.reverse ++ hookH' p1 ++ Y ++ literals pΛ m O I
    let Xg := [litTest pΛ a, hookPut p2, litTest pΛ b]
    let Zg := hookG' p2 ++ Xh.reverse ++ hookH' p2 ++ Zh2
    let S1 := Xg ++ forkF1 p3 ++ Zg
    let Ta := X ++ clauseΓ1 pΛ b c p ++ Y ++ literals pΛ m (O.erase a) (insert a I)
    LeadsTo S1 {T | a ∈ O ∧ T = Ta} := by
  intro p1 p0 p2 p3 Xh Zh2 Xg Zg S1 Ta
  set mid : List ℕ :=
    [hookPut p2, litTest pΛ b] ++ forkF1 p3 ++ hookG' p2 ++ Xh.reverse ++ hookH' p2 ++
      hookG' p1 ++ X.reverse ++ hookH' p1 ++ Y
  have hS1eq : S1 = litTest pΛ a :: mid ++ literals pΛ m O I := by
    simp [S1, Xg, Zg, Zh2, mid, Xh, List.append_assoc, List.cons_append]
  have hS1' : IsStack (litTest pΛ a :: mid ++ literals pΛ m O I) := by
    simpa [← hS1eq, S1, Xg, Zg, Zh2, Xh, p1, p0, p2, p3] using hS1
  by_cases haO : a ∈ O
  · have hLit : LeadsTo (litTest pΛ a :: mid ++ literals pΛ m O I)
        {mid ++ literals pΛ m (O.erase a) (insert a I)} :=
      (property_8 pΛ m O I mid hO hI hOI).2.1 a haO hS1'
    have hStack2 : IsStack (mid ++ literals pΛ m (O.erase a) (insert a I)) :=
      IsStack_of_LeadsTo_singleton hS1' hLit
    set Λ' : List ℕ := literals pΛ m (O.erase a) (insert a I)
    set Xhook : List ℕ := [litTest pΛ b] ++ forkF1 p3
    have hArr : mid ++ Λ' =
        hookPut p2 :: Xhook ++ hookG' p2 ++ Xh.reverse ++ hookH' p2 ++
          (hookG' p1 ++ X.reverse ++ hookH' p1 ++ Y ++ Λ') := by
      simp [mid, Xhook, Λ', Xh, List.append_assoc, List.cons_append]
    have hStackPut : IsStack
        (hookPut p2 :: Xhook ++ hookG' p2 ++ Xh.reverse ++ hookH' p2 ++
          (hookG' p1 ++ X.reverse ++ hookH' p1 ++ Y ++ Λ')) := by
      rwa [← hArr]
    have hHook2 : LeadsTo
        (hookPut p2 :: Xhook ++ hookG' p2 ++ Xh.reverse ++ hookH' p2 ++
          (hookG' p1 ++ X.reverse ++ hookH' p1 ++ Y ++ Λ'))
        {Xh ++ hookG'' p2 ++ Xhook ++ hookH'' p2 ++
          (hookG' p1 ++ X.reverse ++ hookH' p1 ++ Y ++ Λ')} :=
      (property_6 p2 Xhook Xh (hookG' p1 ++ X.reverse ++ hookH' p1 ++ Y ++ Λ')).2.1 hStackPut
    set mid2 : List ℕ :=
      [litTest pΛ c] ++ forkF1 p0 ++ hookG'' p2 ++ Xhook ++ hookH'' p2
    have hArr2 :
        Xh ++ hookG'' p2 ++ Xhook ++ hookH'' p2 ++
            (hookG' p1 ++ X.reverse ++ hookH' p1 ++ Y ++ Λ') =
          hookPut p1 :: mid2 ++ hookG' p1 ++ X.reverse ++ hookH' p1 ++ (Y ++ Λ') := by
      simp [Xh, mid2, Xhook, List.append_assoc, List.cons_append]
    have hStack3 : IsStack
        (Xh ++ hookG'' p2 ++ Xhook ++ hookH'' p2 ++
          (hookG' p1 ++ X.reverse ++ hookH' p1 ++ Y ++ Λ')) :=
      IsStack_of_LeadsTo_singleton hStackPut hHook2
    have hStackPut1 : IsStack
        (hookPut p1 :: mid2 ++ hookG' p1 ++ X.reverse ++ hookH' p1 ++ (Y ++ Λ')) := by
      rwa [← hArr2]
    have hHook1 : LeadsTo
        (hookPut p1 :: mid2 ++ hookG' p1 ++ X.reverse ++ hookH' p1 ++ (Y ++ Λ'))
        {X ++ hookG'' p1 ++ mid2 ++ hookH'' p1 ++ (Y ++ Λ')} :=
      (property_6 p1 mid2 X (Y ++ Λ')).2.1 hStackPut1
    have hFinal :
        X ++ (hookG'' p1 ++ (mid2 ++ (hookH'' p1 ++ (Y ++ Λ')))) = Ta := by
      simp [Ta, mid2, Xhook, Λ', clauseΓ1_eq, p1, p0, p2, p3, List.append_assoc]
    have hLit' : LeadsTo S1 {mid ++ Λ'} := by
      simpa [hS1eq, Λ'] using hLit
    have hHook2' : LeadsTo (mid ++ Λ')
        {Xh ++ hookG'' p2 ++ Xhook ++ hookH'' p2 ++
          (hookG' p1 ++ X.reverse ++ hookH' p1 ++ Y ++ Λ')} := by
      simpa [hArr] using hHook2
    have hHook1' : LeadsTo
        (Xh ++ hookG'' p2 ++ Xhook ++ hookH'' p2 ++
          (hookG' p1 ++ X.reverse ++ hookH' p1 ++ Y ++ Λ'))
        {Ta} := by
      have h := hHook1
      rw [← hArr2] at h
      simpa [List.append_assoc, hFinal] using h
    have hAll : LeadsTo S1 {Ta} :=
      LeadsTo.trans_singleton (LeadsTo.trans_singleton hLit' hHook2') hHook1'
    have hset : ({Ta} : Set (List ℕ)) = {T | a ∈ O ∧ T = Ta} := by
      ext T; constructor
      · intro hT; exact ⟨haO, Set.mem_singleton_iff.mp hT⟩
      · intro ⟨_, hEq⟩; exact hEq ▸ Set.mem_singleton _
    exact LeadsTo.of_set_eq hAll hset
  · have hDead : IsDeadlock (litTest pΛ a :: mid ++ literals pΛ m O I) :=
      (property_8 pΛ m O I mid hO hI hOI).2.2 a ha haO hS1'
    have hEmpty : LeadsTo (litTest pΛ a :: mid ++ literals pΛ m O I) (∅ : Set (List ℕ)) :=
      LeadsTo.of_deadlock hDead
    have hEmpty' : LeadsTo S1 (∅ : Set (List ℕ)) := by
      simpa [hS1eq] using hEmpty
    have hset : (∅ : Set (List ℕ)) = {T | a ∈ O ∧ T = Ta} := by
      ext T; constructor
      · intro hT; cases hT
      · intro ⟨hmem, _⟩; exact (haO hmem).elim
    exact LeadsTo.of_set_eq hEmpty' hset

/-- S2 branch (head `test_b`). -/
lemma prop10_from_S2
    (pΛ m : ℕ) (p : ℤ) (a b c : ℕ) (O I : Finset ℕ) (X Y : List ℕ)
    (hb : b ∈ Finset.Icc 1 m)
    (hO : O ⊆ Finset.Icc 1 m) (hI : I ⊆ Finset.Icc 1 m) (hOI : Disjoint O I)
    (hS2 : IsStack (
      let p1 := (p + 21).toNat
      let p0 := (p + 2).toNat
      let p2 := (p + 33).toNat
      let p3 := (p + 45).toNat
      let Xh := [hookPut p1, litTest pΛ c] ++ forkF1 p0
      let Zh2 := hookG' p1 ++ X.reverse ++ hookH' p1 ++ Y ++ literals pΛ m O I
      let Xg := [litTest pΛ a, hookPut p2, litTest pΛ b]
      let Zg := hookG' p2 ++ Xh.reverse ++ hookH' p2 ++ Zh2
      Xg.reverse ++ forkF2 p3 ++ Zg)) :
    let p1 := (p + 21).toNat
    let p0 := (p + 2).toNat
    let p2 := (p + 33).toNat
    let p3 := (p + 45).toNat
    let Xh := [hookPut p1, litTest pΛ c] ++ forkF1 p0
    let Zh2 := hookG' p1 ++ X.reverse ++ hookH' p1 ++ Y ++ literals pΛ m O I
    let Xg := [litTest pΛ a, hookPut p2, litTest pΛ b]
    let Zg := hookG' p2 ++ Xh.reverse ++ hookH' p2 ++ Zh2
    let S2 := Xg.reverse ++ forkF2 p3 ++ Zg
    let Tb := X ++ clauseΓ2 pΛ a c p ++ Y ++ literals pΛ m (O.erase b) (insert b I)
    LeadsTo S2 {T | b ∈ O ∧ T = Tb} := by
  intro p1 p0 p2 p3 Xh Zh2 Xg Zg S2 Tb
  set mid : List ℕ :=
    [hookPut p2, litTest pΛ a] ++ forkF2 p3 ++ hookG' p2 ++ Xh.reverse ++ hookH' p2 ++
      hookG' p1 ++ X.reverse ++ hookH' p1 ++ Y
  have hS2eq : S2 = litTest pΛ b :: mid ++ literals pΛ m O I := by
    simp [S2, Xg, Zg, Zh2, mid, Xh, List.append_assoc, List.cons_append]
  have hS2' : IsStack (litTest pΛ b :: mid ++ literals pΛ m O I) := by
    simpa [← hS2eq, S2, Xg, Zg, Zh2, Xh, p1, p0, p2, p3] using hS2
  by_cases hbO : b ∈ O
  · have hLit : LeadsTo (litTest pΛ b :: mid ++ literals pΛ m O I)
        {mid ++ literals pΛ m (O.erase b) (insert b I)} :=
      (property_8 pΛ m O I mid hO hI hOI).2.1 b hbO hS2'
    have hStack2 : IsStack (mid ++ literals pΛ m (O.erase b) (insert b I)) :=
      IsStack_of_LeadsTo_singleton hS2' hLit
    set Λ' : List ℕ := literals pΛ m (O.erase b) (insert b I)
    set Xhook : List ℕ := [litTest pΛ a] ++ forkF2 p3
    have hArr : mid ++ Λ' =
        hookPut p2 :: Xhook ++ hookG' p2 ++ Xh.reverse ++ hookH' p2 ++
          (hookG' p1 ++ X.reverse ++ hookH' p1 ++ Y ++ Λ') := by
      simp [mid, Xhook, Λ', Xh, List.append_assoc, List.cons_append]
    have hStackPut : IsStack
        (hookPut p2 :: Xhook ++ hookG' p2 ++ Xh.reverse ++ hookH' p2 ++
          (hookG' p1 ++ X.reverse ++ hookH' p1 ++ Y ++ Λ')) := by
      rwa [← hArr]
    have hHook2 : LeadsTo
        (hookPut p2 :: Xhook ++ hookG' p2 ++ Xh.reverse ++ hookH' p2 ++
          (hookG' p1 ++ X.reverse ++ hookH' p1 ++ Y ++ Λ'))
        {Xh ++ hookG'' p2 ++ Xhook ++ hookH'' p2 ++
          (hookG' p1 ++ X.reverse ++ hookH' p1 ++ Y ++ Λ')} :=
      (property_6 p2 Xhook Xh (hookG' p1 ++ X.reverse ++ hookH' p1 ++ Y ++ Λ')).2.1 hStackPut
    set mid2 : List ℕ :=
      [litTest pΛ c] ++ forkF1 p0 ++ hookG'' p2 ++ Xhook ++ hookH'' p2
    have hArr2 :
        Xh ++ hookG'' p2 ++ Xhook ++ hookH'' p2 ++
            (hookG' p1 ++ X.reverse ++ hookH' p1 ++ Y ++ Λ') =
          hookPut p1 :: mid2 ++ hookG' p1 ++ X.reverse ++ hookH' p1 ++ (Y ++ Λ') := by
      simp [Xh, mid2, Xhook, List.append_assoc, List.cons_append]
    have hStack3 : IsStack
        (Xh ++ hookG'' p2 ++ Xhook ++ hookH'' p2 ++
          (hookG' p1 ++ X.reverse ++ hookH' p1 ++ Y ++ Λ')) :=
      IsStack_of_LeadsTo_singleton hStackPut hHook2
    have hStackPut1 : IsStack
        (hookPut p1 :: mid2 ++ hookG' p1 ++ X.reverse ++ hookH' p1 ++ (Y ++ Λ')) := by
      rwa [← hArr2]
    have hHook1 : LeadsTo
        (hookPut p1 :: mid2 ++ hookG' p1 ++ X.reverse ++ hookH' p1 ++ (Y ++ Λ'))
        {X ++ hookG'' p1 ++ mid2 ++ hookH'' p1 ++ (Y ++ Λ')} :=
      (property_6 p1 mid2 X (Y ++ Λ')).2.1 hStackPut1
    have hFinal :
        X ++ (hookG'' p1 ++ (mid2 ++ (hookH'' p1 ++ (Y ++ Λ')))) = Tb := by
      simp [Tb, mid2, Xhook, Λ', clauseΓ2_eq, p1, p0, p2, p3, List.append_assoc]
    have hLit' : LeadsTo S2 {mid ++ Λ'} := by
      simpa [hS2eq, Λ'] using hLit
    have hHook2' : LeadsTo (mid ++ Λ')
        {Xh ++ hookG'' p2 ++ Xhook ++ hookH'' p2 ++
          (hookG' p1 ++ X.reverse ++ hookH' p1 ++ Y ++ Λ')} := by
      simpa [hArr] using hHook2
    have hHook1' : LeadsTo
        (Xh ++ hookG'' p2 ++ Xhook ++ hookH'' p2 ++
          (hookG' p1 ++ X.reverse ++ hookH' p1 ++ Y ++ Λ'))
        {Tb} := by
      have h := hHook1
      rw [← hArr2] at h
      simpa [List.append_assoc, hFinal] using h
    have hAll : LeadsTo S2 {Tb} :=
      LeadsTo.trans_singleton (LeadsTo.trans_singleton hLit' hHook2') hHook1'
    have hset : ({Tb} : Set (List ℕ)) = {T | b ∈ O ∧ T = Tb} := by
      ext T; constructor
      · intro hT; exact ⟨hbO, Set.mem_singleton_iff.mp hT⟩
      · intro ⟨_, hEq⟩; exact hEq ▸ Set.mem_singleton _
    exact LeadsTo.of_set_eq hAll hset
  · have hDead : IsDeadlock (litTest pΛ b :: mid ++ literals pΛ m O I) :=
      (property_8 pΛ m O I mid hO hI hOI).2.2 b hb hbO hS2'
    have hEmpty : LeadsTo (litTest pΛ b :: mid ++ literals pΛ m O I) (∅ : Set (List ℕ)) :=
      LeadsTo.of_deadlock hDead
    have hEmpty' : LeadsTo S2 (∅ : Set (List ℕ)) := by
      simpa [hS2eq] using hEmpty
    have hset : (∅ : Set (List ℕ)) = {T | b ∈ O ∧ T = Tb} := by
      ext T; constructor
      · intro hT; cases hT
      · intro ⟨hmem, _⟩; exact (hbO hmem).elim
    exact LeadsTo.of_set_eq hEmpty' hset

/-- S3 branch (head `test_c`): Literals.b then one Hook.b → Γ³. -/
lemma prop10_from_S3
    (pΛ m : ℕ) (p : ℤ) (a b c : ℕ) (O I : Finset ℕ) (X Y : List ℕ)
    (hc : c ∈ Finset.Icc 1 m)
    (hO : O ⊆ Finset.Icc 1 m) (hI : I ⊆ Finset.Icc 1 m) (hOI : Disjoint O I)
    (hS3 : IsStack (
      let p1 := (p + 21).toNat
      let p0 := (p + 2).toNat
      let p2 := (p + 33).toNat
      let p3 := (p + 45).toNat
      let Xf := [hookTake p2, hookPut p1, litTest pΛ c]
      let Zf :=
        hookG p2 ++ forkE p3 ++ [litTest pΛ a, hookPut p2, litTest pΛ b] ++
          forkF p3 ++ hookH p2 ++ hookG' p1 ++ X.reverse ++ hookH' p1 ++
          Y ++ literals pΛ m O I
      Xf.reverse ++ forkF2 p0 ++ Zf)) :
    let p1 := (p + 21).toNat
    let p0 := (p + 2).toNat
    let p2 := (p + 33).toNat
    let p3 := (p + 45).toNat
    let Xf := [hookTake p2, hookPut p1, litTest pΛ c]
    let Zf :=
      hookG p2 ++ forkE p3 ++ [litTest pΛ a, hookPut p2, litTest pΛ b] ++
        forkF p3 ++ hookH p2 ++ hookG' p1 ++ X.reverse ++ hookH' p1 ++
        Y ++ literals pΛ m O I
    let S3 := Xf.reverse ++ forkF2 p0 ++ Zf
    let Tc := X ++ clauseΓ3 pΛ a b p ++ Y ++ literals pΛ m (O.erase c) (insert c I)
    LeadsTo S3 {T | c ∈ O ∧ T = Tc} := by
  intro p1 p0 p2 p3 Xf Zf S3 Tc
  set mid : List ℕ :=
    [hookPut p1, hookTake p2] ++ forkF2 p0 ++ hookG p2 ++ forkE p3 ++
      [litTest pΛ a, hookPut p2, litTest pΛ b] ++ forkF p3 ++ hookH p2 ++
      hookG' p1 ++ X.reverse ++ hookH' p1 ++ Y
  have hS3eq : S3 = litTest pΛ c :: mid ++ literals pΛ m O I := by
    simp [S3, Xf, Zf, mid, List.append_assoc, List.cons_append]
  have hS3' : IsStack (litTest pΛ c :: mid ++ literals pΛ m O I) := by
    simpa [← hS3eq, S3, Xf, Zf, p1, p0, p2, p3] using hS3
  by_cases hcO : c ∈ O
  · have hLit : LeadsTo (litTest pΛ c :: mid ++ literals pΛ m O I)
        {mid ++ literals pΛ m (O.erase c) (insert c I)} :=
      (property_8 pΛ m O I mid hO hI hOI).2.1 c hcO hS3'
    have hStack2 : IsStack (mid ++ literals pΛ m (O.erase c) (insert c I)) :=
      IsStack_of_LeadsTo_singleton hS3' hLit
    set Λ' : List ℕ := literals pΛ m (O.erase c) (insert c I)
    set Xhook : List ℕ :=
      [hookTake p2] ++ forkF2 p0 ++ hookG p2 ++ forkE p3 ++
        [litTest pΛ a, hookPut p2, litTest pΛ b] ++ forkF p3 ++ hookH p2
    have hArr : mid ++ Λ' =
        hookPut p1 :: Xhook ++ hookG' p1 ++ X.reverse ++ hookH' p1 ++ (Y ++ Λ') := by
      simp [mid, Xhook, Λ', List.append_assoc, List.cons_append]
    have hStackPut : IsStack
        (hookPut p1 :: Xhook ++ hookG' p1 ++ X.reverse ++ hookH' p1 ++ (Y ++ Λ')) := by
      rwa [← hArr]
    have hHook1 : LeadsTo
        (hookPut p1 :: Xhook ++ hookG' p1 ++ X.reverse ++ hookH' p1 ++ (Y ++ Λ'))
        {X ++ hookG'' p1 ++ Xhook ++ hookH'' p1 ++ (Y ++ Λ')} :=
      (property_6 p1 Xhook X (Y ++ Λ')).2.1 hStackPut
    have hFinal :
        X ++ (hookG'' p1 ++ (Xhook ++ (hookH'' p1 ++ (Y ++ Λ')))) = Tc := by
      simp [Tc, Xhook, Λ', clauseΓ3_eq, p1, p0, p2, p3, List.append_assoc]
    have hLit' : LeadsTo S3 {mid ++ Λ'} := by
      simpa [hS3eq, Λ'] using hLit
    have hHook1' : LeadsTo (mid ++ Λ') {Tc} := by
      have h := hHook1
      rw [← hArr] at h
      simpa [List.append_assoc, hFinal] using h
    have hAll : LeadsTo S3 {Tc} := LeadsTo.trans_singleton hLit' hHook1'
    have hset : ({Tc} : Set (List ℕ)) = {T | c ∈ O ∧ T = Tc} := by
      ext T; constructor
      · intro hT; exact ⟨hcO, Set.mem_singleton_iff.mp hT⟩
      · intro ⟨_, hEq⟩; exact hEq ▸ Set.mem_singleton _
    exact LeadsTo.of_set_eq hAll hset
  · have hDead : IsDeadlock (litTest pΛ c :: mid ++ literals pΛ m O I) :=
      (property_8 pΛ m O I mid hO hI hOI).2.2 c hc hcO hS3'
    have hEmpty : LeadsTo (litTest pΛ c :: mid ++ literals pΛ m O I) (∅ : Set (List ℕ)) :=
      LeadsTo.of_deadlock hDead
    have hEmpty' : LeadsTo S3 (∅ : Set (List ℕ)) := by
      simpa [hS3eq] using hEmpty
    have hset : (∅ : Set (List ℕ)) = {T | c ∈ O ∧ T = Tc} := by
      ext T; constructor
      · intro hT; cases hT
      · intro ⟨hmem, _⟩; exact (hcO hmem).elim
    exact LeadsTo.of_set_eq hEmpty' hset

/-! ### from PH10_full.lean -/

/-- Assemble Property 10 from the spine and three outcome branches. -/
theorem property_10_proof (pΛ m : ℕ) (p : ℤ) (_hp : -2 ≤ p) (a b c : ℕ) (O I : Finset ℕ)
    (X Y : List ℕ)
    (ha : a ∈ Finset.Icc 1 m) (hb : b ∈ Finset.Icc 1 m) (hc : c ∈ Finset.Icc 1 m)
    (_hab : a ≠ b) (_hac : a ≠ c) (_hbc : b ≠ c) (hO : O ⊆ Finset.Icc 1 m)
    (hI : I ⊆ Finset.Icc 1 m) (hOI : Disjoint O I)
    (hS : IsStack (clauseGamma p :: X ++ clauseΓ pΛ a b c p ++ Y ++ literals pΛ m O I)) :
    LeadsTo (clauseGamma p :: X ++ clauseΓ pΛ a b c p ++ Y ++ literals pΛ m O I)
      {T | (a ∈ O ∧ T = X ++ clauseΓ1 pΛ b c p ++ Y ++ literals pΛ m (O.erase a) (insert a I)) ∨
        (b ∈ O ∧ T = X ++ clauseΓ2 pΛ a c p ++ Y ++ literals pΛ m (O.erase b) (insert b I)) ∨
        (c ∈ O ∧ T = X ++ clauseΓ3 pΛ a b p ++ Y ++ literals pΛ m (O.erase c) (insert c I))} := by
  -- Name the intermediate stacks from the paper proof.
  let p1 := (p + 21).toNat
  let p0 := (p + 2).toNat
  let p2 := (p + 33).toNat
  let p3 := (p + 45).toNat
  let Zh := Y ++ literals pΛ m O I
  let Xf := [hookTake p2, hookPut p1, litTest pΛ c]
  let Zf :=
    hookG p2 ++ forkE p3 ++ [litTest pΛ a, hookPut p2, litTest pΛ b] ++
      forkF p3 ++ hookH p2 ++ hookG' p1 ++ X.reverse ++ hookH' p1 ++ Zh
  let S0 := Xf ++ forkF1 p0 ++ Zf
  let S3 := Xf.reverse ++ forkF2 p0 ++ Zf
  let Xh := [hookPut p1, litTest pΛ c] ++ forkF1 p0
  let Zh2 := hookG' p1 ++ X.reverse ++ hookH' p1 ++ Zh
  let Xg := [litTest pΛ a, hookPut p2, litTest pΛ b]
  let Zg := hookG' p2 ++ Xh.reverse ++ hookH' p2 ++ Zh2
  let S1 := Xg ++ forkF1 p3 ++ Zg
  let S2 := Xg.reverse ++ forkF2 p3 ++ Zg
  let Ta := X ++ clauseΓ1 pΛ b c p ++ Y ++ literals pΛ m (O.erase a) (insert a I)
  let Tb := X ++ clauseΓ2 pΛ a c p ++ Y ++ literals pΛ m (O.erase b) (insert b I)
  let Tc := X ++ clauseΓ3 pΛ a b p ++ Y ++ literals pΛ m (O.erase c) (insert c I)
  let 𝕋a : Set (List ℕ) := {T | a ∈ O ∧ T = Ta}
  let 𝕋b : Set (List ℕ) := {T | b ∈ O ∧ T = Tb}
  let 𝕋c : Set (List ℕ) := {T | c ∈ O ∧ T = Tc}

  have hStart : LeadsTo
      (clauseGamma p :: X ++ clauseΓ pΛ a b c p ++ Y ++ literals pΛ m O I) {S0, S3} := by
    simpa [p1, p0, p2, p3, Zh, Xf, Zf, S0, S3] using
      prop10_hook_fork1 pΛ m p _hp a b c O I X Y ha hb hc _hab _hac _hbc hO hI hOI hS

  have hStackS0 : IsStack S0 := by
    obtain ⟨π, hπ⟩ := hStart.1 S0 (by simp [S0])
    exact IsStack_of_IsEfficientPath π _ _ hS hπ
  have hStackS3 : IsStack S3 := by
    obtain ⟨π, hπ⟩ := hStart.1 S3 (by simp [S3])
    exact IsStack_of_IsEfficientPath π _ _ hS hπ

  have hS0to12 : LeadsTo S0 {S1, S2} := by
    have h := prop10_from_S0 pΛ p a b c X Zh (by
      change IsStack S0 at hStackS0
      -- prop10_from_S0 expects the let-expanded form equal to S0
      simpa [p1, p0, p2, p3, Xf, Zf, S0] using hStackS0)
    simpa [p1, p0, p2, p3, Xf, Zf, S0, Xh, Zh2, Xg, Zg, S1, S2] using h

  have hStackS1 : IsStack S1 := by
    obtain ⟨π, hπ⟩ := hS0to12.1 S1 (by simp [S1])
    exact IsStack_of_IsEfficientPath π _ _ hStackS0 hπ
  have hStackS2 : IsStack S2 := by
    obtain ⟨π, hπ⟩ := hS0to12.1 S2 (by simp [S2])
    exact IsStack_of_IsEfficientPath π _ _ hStackS0 hπ

  have hS1out : LeadsTo S1 𝕋a := by
    have h := prop10_from_S1 pΛ m p a b c O I X Y ha hO hI hOI (by
      simpa [p1, p0, p2, p3, Xh, Zh2, Xg, Zg, S1, Zh] using hStackS1)
    simpa [p1, p0, p2, p3, Xh, Zh2, Xg, Zg, S1, Ta, 𝕋a] using h

  have hS2out : LeadsTo S2 𝕋b := by
    have h := prop10_from_S2 pΛ m p a b c O I X Y hb hO hI hOI (by
      simpa [p1, p0, p2, p3, Xh, Zh2, Xg, Zg, S2, Zh] using hStackS2)
    simpa [p1, p0, p2, p3, Xh, Zh2, Xg, Zg, S2, Tb, 𝕋b] using h

  have hS3out : LeadsTo S3 𝕋c := by
    have h := prop10_from_S3 pΛ m p a b c O I X Y hc hO hI hOI (by
      simpa [p1, p0, p2, p3, Xf, Zf, S3, Zh] using hStackS3)
    simpa [p1, p0, p2, p3, Xf, Zf, S3, Tc, 𝕋c] using h

  have hS0out : LeadsTo S0 (𝕋a ∪ 𝕋b) :=
    LeadsTo.pair_union hS0to12 hS1out hS2out

  have hAll : LeadsTo
      (clauseGamma p :: X ++ clauseΓ pΛ a b c p ++ Y ++ literals pΛ m O I)
      (𝕋a ∪ 𝕋b ∪ 𝕋c) :=
    LeadsTo.pair_union hStart hS0out hS3out

  have hTarget :
      (𝕋a ∪ 𝕋b ∪ 𝕋c) =
        {T | (a ∈ O ∧ T = Ta) ∨ (b ∈ O ∧ T = Tb) ∨ (c ∈ O ∧ T = Tc)} := by
    ext T; simp [𝕋a, 𝕋b, 𝕋c]; tauto

  have hAll' := LeadsTo.of_set_eq hAll hTarget
  simpa [Ta, Tb, Tc] using hAll'

end PancakeHard

theorem solution (pΛ m : ℕ) (p : ℤ) (hp : -2 ≤ p) (a b c : ℕ) (O I : Finset ℕ) (X Y : List ℕ)
    (ha : a ∈ Finset.Icc 1 m) (hb : b ∈ Finset.Icc 1 m) (hc : c ∈ Finset.Icc 1 m)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hO : O ⊆ Finset.Icc 1 m)
    (hI : I ⊆ Finset.Icc 1 m) (hOI : Disjoint O I)
    (hS : PancakeHard.IsStack (PancakeHard.clauseGamma p :: X ++ PancakeHard.clauseΓ pΛ a b c p ++ Y ++
        PancakeHard.literals pΛ m O I)) :
    PancakeHard.LeadsTo (PancakeHard.clauseGamma p :: X ++ PancakeHard.clauseΓ pΛ a b c p ++ Y ++
        PancakeHard.literals pΛ m O I)
      {T | (a ∈ O ∧ T = X ++ PancakeHard.clauseΓ1 pΛ b c p ++ Y ++
          PancakeHard.literals pΛ m (O.erase a) (insert a I)) ∨
        (b ∈ O ∧ T = X ++ PancakeHard.clauseΓ2 pΛ a c p ++ Y ++
          PancakeHard.literals pΛ m (O.erase b) (insert b I)) ∨
        (c ∈ O ∧ T = X ++ PancakeHard.clauseΓ3 pΛ a b p ++ Y ++
          PancakeHard.literals pΛ m (O.erase c) (insert c I))} :=
  PancakeHard.property_10_proof pΛ m p hp a b c O I X Y ha hb hc hab hac hbc hO hI hOI hS
