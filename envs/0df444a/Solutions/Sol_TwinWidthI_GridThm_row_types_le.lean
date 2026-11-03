-- Prove2me | solution 1 for TwinWidthI.GridThm.row_types_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:28:15.889607+00:00
-- url     : https://prove2.me/submissions/e2577d60-44ea-40a3-bdba-04d1449451dd

import Mathlib
import Definitions.Def_TwinWidthI_GridThm_Setting

open Finset TwinWidthI.GridThm

namespace TwinWidthI.GridThm.RowTypesLeProof

open Classical in
/-- Given a row part `X` and column division `C` of `Fin m` (`1 ≤ m`), `repCol` selects the
largest column index in a nonempty column set (and `m - 1` on `∅`). -/
noncomputable def repCol {m : ℕ} (hm : 1 ≤ m) (Z : Finset (Fin m)) : Fin m :=
  if hZ : Z.Nonempty then Z.max' hZ else ⟨m - 1, Nat.sub_lt hm zero_lt_one⟩

open Classical in
/-- For a nonempty column set `Z`, `prevPart` returns the part of `C` containing `min(Z) - 1`. -/
noncomputable def prevPart {m : ℕ} (C : Finpartition (univ : Finset (Fin m)))
    (Z : Finset (Fin m)) : Finset (Fin m) :=
  if hZ : Z.Nonempty then
    C.part ⟨(Z.min' hZ : ℕ) - 1, by have := (Z.min' hZ).isLt; omega⟩
  else ∅

open Classical in
/-- The terminal subset `T` of column parts whose rightmost column values determine every
non-mixed, non-vertical column part of `C`. -/
noncomputable def terminalParts {A : Type*} {n m : ℕ} (hm : 1 ≤ m)
    (M : Matrix (Fin n) (Fin m) A) (X : Finset (Fin n))
    (C : Finpartition (univ : Finset (Fin m))) : Finset (Finset (Fin m)) :=
  let lastCol : Fin m := ⟨m - 1, Nat.sub_lt hm zero_lt_one⟩
  let CutSet := {Y ∈ C.parts | ∃ Y' ∈ C.parts, IsMixedCutCol M X Y Y'}
  let MixSet := {Y ∈ C.parts | IsMixed M X Y}
  insert (C.part lastCol) (CutSet ∪ MixSet.image (prevPart C))

open Classical in
lemma card_terminalParts_le {A : Type*} {n m : ℕ} (hm : 1 ≤ m)
    (M : Matrix (Fin n) (Fin m) A) (X : Finset (Fin n))
    (C : Finpartition (univ : Finset (Fin m))) :
    #(terminalParts hm M X C) ≤ mixedValueCol M X C + 1 := by
  dsimp [terminalParts, mixedValueCol]
  have h1 : #(insert (C.part ⟨m - 1, Nat.sub_lt hm zero_lt_one⟩)
      ({Y ∈ C.parts | ∃ Y' ∈ C.parts, IsMixedCutCol M X Y Y'} ∪
       ({Y ∈ C.parts | IsMixed M X Y}).image (prevPart C))) ≤
      #({Y ∈ C.parts | ∃ Y' ∈ C.parts, IsMixedCutCol M X Y Y'} ∪
        ({Y ∈ C.parts | IsMixed M X Y}).image (prevPart C)) + 1 :=
    card_insert_le _ _
  have h2 : #({Y ∈ C.parts | ∃ Y' ∈ C.parts, IsMixedCutCol M X Y Y'} ∪
      ({Y ∈ C.parts | IsMixed M X Y}).image (prevPart C)) ≤
      #{Y ∈ C.parts | ∃ Y' ∈ C.parts, IsMixedCutCol M X Y Y'} +
      #(({Y ∈ C.parts | IsMixed M X Y}).image (prevPart C)) :=
    card_union_le _ _
  have h3 : #(({Y ∈ C.parts | IsMixed M X Y}).image (prevPart C)) ≤
      #{Y ∈ C.parts | IsMixed M X Y} :=
    card_image_le
  omega

open Classical in
lemma step_of_not_mem_terminalParts {A : Type*} {n m : ℕ} (hm : 1 ≤ m)
    (M : Matrix (Fin n) (Fin m) A) (X : Finset (Fin n))
    (C : Finpartition (univ : Finset (Fin m))) (hC : IsDivision C)
    {Y : Finset (Fin m)} (hY_parts : Y ∈ C.parts)
    (hY_nmix : ¬ IsMixed M X Y) (hY_nvert : ¬ IsVertical M X Y)
    (hY_not_T : Y ∉ terminalParts hm M X C) :
    ∃ Y' ∈ C.parts, ¬ IsMixed M X Y' ∧ ¬ IsVertical M X Y' ∧
      (repCol hm Y : ℕ) < (repCol hm Y' : ℕ) ∧
      ∀ i ∈ X, M i (repCol hm Y) = M i (repCol hm Y') := by
  have hY_ne : Y.Nonempty := C.nonempty_of_mem_parts hY_parts
  have hY_horiz : IsHorizontal M X Y := by
    by_contra hnh
    exact hY_nmix ⟨hY_nvert, hnh⟩
  let y : Fin m := repCol hm Y
  have hy_eq : y = Y.max' hY_ne := by simp [y, repCol, hY_ne]
  have hy_mem : y ∈ Y := hy_eq ▸ max'_mem Y hY_ne
  have hy_max : ∀ x ∈ Y, x ≤ y := fun x hx => hy_eq ▸ le_max' Y x hx
  have h_not_last : Y ≠ C.part ⟨m - 1, Nat.sub_lt hm zero_lt_one⟩ :=
    fun h => hY_not_T (by simp [terminalParts, h])
  have h_not_cut : ¬ ∃ Y' ∈ C.parts, IsMixedCutCol M X Y Y' :=
    fun h => hY_not_T (by simp [terminalParts, hY_parts, h])
  have h_not_prev : ∀ Z ∈ C.parts, IsMixed M X Z → prevPart C Z ≠ Y := by
    intro Z hZ_parts hZ_mix hprev
    apply hY_not_T
    simp only [terminalParts, mem_insert, mem_union, mem_filter, mem_image]
    right; right
    exact ⟨Z, ⟨hZ_parts, hZ_mix⟩, hprev⟩
  have hy_lt : (y : ℕ) + 1 < m := by
    by_contra hge
    have hy_last : y = ⟨m - 1, Nat.sub_lt hm zero_lt_one⟩ := by
      apply Fin.ext
      change (y : ℕ) = m - 1
      have := y.isLt
      omega
    have hY_eq_part : C.part y = Y := C.part_eq_of_mem hY_parts hy_mem
    exact h_not_last (by rw [← hY_eq_part, hy_last])
  let y' : Fin m := ⟨(y : ℕ) + 1, hy_lt⟩
  let Y' : Finset (Fin m) := C.part y'
  have hY'_parts : Y' ∈ C.parts := C.part_mem.mpr (mem_univ y')
  have hy'_mem : y' ∈ Y' := C.mem_part (mem_univ y')
  have hY'_ne : Y'.Nonempty := ⟨y', hy'_mem⟩
  have hy'_min : ∀ z ∈ Y', y' ≤ z := by
    intro z hz
    by_contra hlt
    push Not at hlt
    have hz_le_y : z ≤ y := by
      rw [Fin.le_iff_val_le_val]
      rw [Fin.lt_def] at hlt
      change (z : ℕ) < (y : ℕ) + 1 at hlt
      omega
    have hy_le_y' : y ≤ y' := by
      rw [Fin.le_iff_val_le_val]
      change (y : ℕ) ≤ (y : ℕ) + 1
      omega
    have hy_in_Y' : y ∈ Y' := hC Y' hY'_parts z hz y' hy'_mem y hz_le_y hy_le_y'
    have hY_eq_Y' : Y = Y' := C.eq_of_mem_parts hY_parts hY'_parts hy_mem hy_in_Y'
    have hy'_le_y : y' ≤ y := hy_max y' (hY_eq_Y' ▸ hy'_mem)
    rw [Fin.le_iff_val_le_val] at hy'_le_y
    change (y : ℕ) + 1 ≤ (y : ℕ) at hy'_le_y
    omega
  have hy'_eq_min : Y'.min' hY'_ne = y' :=
    le_antisymm (min'_le Y' y' hy'_mem) (hy'_min _ (min'_mem Y' hY'_ne))
  have hprev_Y' : prevPart C Y' = Y := by
    dsimp [prevPart]
    rw [dif_pos hY'_ne]
    have h_idx : (⟨(Y'.min' hY'_ne : ℕ) - 1, by have := (Y'.min' hY'_ne).isLt; omega⟩ : Fin m) = y := by
      apply Fin.ext
      change (Y'.min' hY'_ne : ℕ) - 1 = (y : ℕ)
      rw [hy'_eq_min]
      change (y : ℕ) + 1 - 1 = (y : ℕ)
      omega
    rw [h_idx]
    exact C.part_eq_of_mem hY_parts hy_mem
  have h_pair_nvert : ¬ IsVertical M X {y, y'} := by
    intro hvert
    apply hY_nvert
    intro i₁ hi₁ i₂ hi₂ j hj
    have h1 : M i₁ j = M i₁ y := hY_horiz i₁ hi₁ j hj y hy_mem
    have h2 : M i₂ j = M i₂ y := hY_horiz i₂ hi₂ j hj y hy_mem
    have h3 : M i₁ y = M i₂ y := hvert i₁ hi₁ i₂ hi₂ y (mem_insert_self y {y'})
    rw [h1, h2, h3]
  have h_pair_horiz : IsHorizontal M X {y, y'} := by
    by_contra h_pair_nhoriz
    apply h_not_cut
    refine ⟨Y', hY'_parts, y, hy_mem, y', hy'_mem, hy_max, hy'_min, rfl, ⟨h_pair_nvert, h_pair_nhoriz⟩⟩
  have hY'_nmix : ¬ IsMixed M X Y' :=
    fun hmix => h_not_prev Y' hY'_parts hmix hprev_Y'
  have hY'_nvert : ¬ IsVertical M X Y' := by
    intro hvert'
    apply h_pair_nvert
    intro i₁ hi₁ i₂ hi₂ j hj
    have hy_eq_y' : ∀ i ∈ X, M i y = M i y' :=
      fun i hi => h_pair_horiz i hi y (mem_insert_self y {y'}) y' (mem_insert_of_mem (mem_singleton_self y'))
    have h12 : M i₁ y' = M i₂ y' := hvert' i₁ hi₁ i₂ hi₂ y' hy'_mem
    rcases mem_insert.mp hj with rfl | hj'
    · rw [hy_eq_y' i₁ hi₁, hy_eq_y' i₂ hi₂, h12]
    · rw [mem_singleton.mp hj']
      exact h12
  have hY'_horiz : IsHorizontal M X Y' := by
    by_contra hnh
    exact hY'_nmix ⟨hY'_nvert, hnh⟩
  have hrep_Y' : repCol hm Y' = Y'.max' hY'_ne := by simp [repCol, hY'_ne]
  have hrep_Y'_mem : repCol hm Y' ∈ Y' := hrep_Y' ▸ max'_mem Y' hY'_ne
  have hy'_le_rep : y' ≤ repCol hm Y' := hrep_Y' ▸ le_max' Y' y' hy'_mem
  refine ⟨Y', hY'_parts, hY'_nmix, hY'_nvert, ?_, ?_⟩
  · rw [Fin.le_iff_val_le_val] at hy'_le_rep
    change (y : ℕ) + 1 ≤ (repCol hm Y' : ℕ) at hy'_le_rep
    change (y : ℕ) < (repCol hm Y' : ℕ)
    omega
  · intro i hi
    have h1 : M i y = M i y' :=
      h_pair_horiz i hi y (mem_insert_self y {y'}) y' (mem_insert_of_mem (mem_singleton_self y'))
    have h2 : M i y' = M i (repCol hm Y') :=
      hY'_horiz i hi y' hy'_mem (repCol hm Y') hrep_Y'_mem
    exact h1.trans h2

open Classical in
lemma eq_on_repCol_of_eq_on_terminalParts {A : Type*} {n m : ℕ} (hm : 1 ≤ m)
    (M : Matrix (Fin n) (Fin m) A) (X : Finset (Fin n))
    (C : Finpartition (univ : Finset (Fin m))) (hC : IsDivision C)
    {i₁ i₂ : Fin n} (hi₁ : i₁ ∈ X) (hi₂ : i₂ ∈ X)
    (hT : ∀ Z ∈ terminalParts hm M X C, M i₁ (repCol hm Z) = M i₂ (repCol hm Z)) :
    ∀ k : ℕ, ∀ Y ∈ C.parts, ¬ IsMixed M X Y → ¬ IsVertical M X Y →
      m - (repCol hm Y : ℕ) ≤ k → M i₁ (repCol hm Y) = M i₂ (repCol hm Y) := by
  intro k
  induction k with
  | zero =>
    intro Y _ _ _ hk
    have := (repCol hm Y).isLt
    omega
  | succ k ih =>
    intro Y hY_parts hY_nmix hY_nvert hk
    by_cases hY_T : Y ∈ terminalParts hm M X C
    · exact hT Y hY_T
    · rcases step_of_not_mem_terminalParts hm M X C hC hY_parts hY_nmix hY_nvert hY_T with
        ⟨Y', hY'_parts, hY'_nmix, hY'_nvert, hlt, heq⟩
      have hk' : m - (repCol hm Y' : ℕ) ≤ k := by
        have := (repCol hm Y').isLt
        omega
      rw [heq i₁ hi₁, heq i₂ hi₂]
      exact ih Y' hY'_parts hY'_nmix hY'_nvert hk'

end TwinWidthI.GridThm.RowTypesLeProof

open TwinWidthI.GridThm.RowTypesLeProof

open Classical in
theorem solution {A : Type*} [Fintype A] {n m : ℕ} (hm : 1 ≤ m)
    (M : Matrix (Fin n) (Fin m) A)
    (R : Finpartition (Finset.univ : Finset (Fin n)))
    (C : Finpartition (Finset.univ : Finset (Fin m)))
    (hR : IsDivision R) (hC : IsDivision C) (t' : ℕ) (hmv : MixedValueLE M R C t')
    (X : Finset (Fin n)) (hX : X ∈ R.parts) :
    (X.image (fun i => fun j : {j : Fin m // ¬ IsMixed M X (C.part j)} => M i j)).card ≤
      Fintype.card A ^ (t' + 1) := by
  let _ := hR
  let T := terminalParts hm M X C
  let f : Fin n → {j : Fin m // ¬ IsMixed M X (C.part j)} → A :=
    fun i j => M i j.val
  let g : Fin n → T → A :=
    fun i Z => M i (repCol hm Z.val)
  have h_eq_f_of_eq_g : ∀ i₁ ∈ X, ∀ i₂ ∈ X, g i₁ = g i₂ → f i₁ = f i₂ := by
    intro i₁ hi₁ i₂ hi₂ hgeq
    funext ⟨j, hj_nmix⟩
    dsimp [f]
    let Y := C.part j
    have hY_parts : Y ∈ C.parts := C.part_mem.mpr (mem_univ j)
    have hj_mem : j ∈ Y := C.mem_part (mem_univ j)
    by_cases hY_vert : IsVertical M X Y
    · exact hY_vert i₁ hi₁ i₂ hi₂ j hj_mem
    · have hY_horiz : IsHorizontal M X Y := by
        by_contra hnh
        exact hj_nmix ⟨hY_vert, hnh⟩
      have hY_ne : Y.Nonempty := ⟨j, hj_mem⟩
      have hrep_mem : repCol hm Y ∈ Y := by
        simp only [repCol, hY_ne, ↓reduceDIte]
        exact max'_mem Y hY_ne
      have h1 : M i₁ j = M i₁ (repCol hm Y) := hY_horiz i₁ hi₁ j hj_mem (repCol hm Y) hrep_mem
      have h2 : M i₂ j = M i₂ (repCol hm Y) := hY_horiz i₂ hi₂ j hj_mem (repCol hm Y) hrep_mem
      have hT : ∀ Z ∈ T, M i₁ (repCol hm Z) = M i₂ (repCol hm Z) :=
        fun Z hZ => congr_fun hgeq ⟨Z, hZ⟩
      have h3 : M i₁ (repCol hm Y) = M i₂ (repCol hm Y) :=
        eq_on_repCol_of_eq_on_terminalParts hm M X C hC hi₁ hi₂ hT
          (m - (repCol hm Y : ℕ)) Y hY_parts hj_nmix hY_vert le_rfl
      rw [h1, h2, h3]
  have h_card_le_pow : (X.image f).card ≤ Fintype.card A ^ #T := by
    have h_orig : ∀ u : {y // y ∈ X.image f}, ∃ i ∈ X, f i = u.1 :=
      fun u => mem_image.mp u.2
    choose idx hidx_mem hidx_eq using h_orig
    have h_inj : Set.InjOn (fun u : {y // y ∈ X.image f} => g (idx u)) (X.image f).attach := by
      intro u₁ _ u₂ _ heq
      apply Subtype.ext
      rw [← hidx_eq u₁, ← hidx_eq u₂]
      exact h_eq_f_of_eq_g (idx u₁) (hidx_mem u₁) (idx u₂) (hidx_mem u₂) heq
    calc (X.image f).card
      _ = (X.image f).attach.card := (card_attach).symm
      _ ≤ (univ : Finset (T → A)).card :=
        card_le_card_of_injOn (fun u => g (idx u)) (fun _ _ => mem_univ _) h_inj
      _ = Fintype.card (T → A) := card_univ
      _ = Fintype.card A ^ Fintype.card T := Fintype.card_fun
      _ = Fintype.card A ^ #T := by rw [Fintype.card_coe]
  have hA_pos : 1 ≤ Fintype.card A := by
    rcases R.nonempty_of_mem_parts hX with ⟨i₀, _⟩
    have : Nonempty A := ⟨M i₀ ⟨0, hm⟩⟩
    exact Fintype.card_pos
  have hT_le : #T ≤ t' + 1 := by
    dsimp [T]
    have h1 := card_terminalParts_le hm M X C
    have h2 := hmv.2 X hX
    omega
  exact h_card_le_pow.trans (Nat.pow_le_pow_right hA_pos hT_le)
