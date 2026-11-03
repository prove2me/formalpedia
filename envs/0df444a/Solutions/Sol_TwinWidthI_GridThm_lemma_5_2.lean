-- Prove2me | solution 1 for TwinWidthI.GridThm.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:28:10.310775+00:00
-- url     : https://prove2.me/submissions/018e066a-d2a7-482a-9471-a78670b2079a

import Mathlib
import Definitions.Def_TwinWidthI_GridThm_Setting

open Finset TwinWidthI.GridThm TwinWidthI.BoolWidth

namespace TwinWidthI.GridThm.Lemma52Proof

lemma zoneConst_mono {A : Type*} {n m : ℕ} {M : Matrix (Fin n) (Fin m) A}
    {X₁ X₂ : Finset (Fin n)} {Y₁ Y₂ : Finset (Fin m)}
    (hX : X₁ ⊆ X₂) (hY : Y₁ ⊆ Y₂) (h : ZoneConst M X₂ Y₂) :
    ZoneConst M X₁ Y₁ :=
  fun i hi i' hi' j hj j' hj' => h i (hX hi) i' (hX hi') j (hY hj) j' (hY hj')

lemma kRefines_of_le {α : Type*} [DecidableEq α] {s : Finset α} {r : ℕ}
    {P P' P₂ : Finpartition s} (h1 : P ≤ P') (h2 : P' ≤ P₂) (href : KRefines r P P₂) :
    KRefines r P' P₂ := by
  refine ⟨fun X' hX' => h2 hX', fun Y hY => ?_⟩
  have hex : ∀ u : {X' // X' ∈ P'.parts}, ∃ X ∈ P.parts, X ⊆ u.1 :=
    fun u => Finpartition.exists_le_of_le h1 u.2
  choose g hg_mem hg_sub using hex
  let f : Finset α → Finset α := fun X' => if hX' : X' ∈ P'.parts then g ⟨X', hX'⟩ else ∅
  have hf_mem : ∀ X' ∈ P'.parts, f X' ∈ P.parts := by
    intro X' hX'
    dsimp [f]
    rw [dif_pos hX']
    exact hg_mem ⟨X', hX'⟩
  have hf_sub : ∀ X' ∈ P'.parts, f X' ⊆ X' := by
    intro X' hX'
    dsimp [f]
    rw [dif_pos hX']
    exact hg_sub ⟨X', hX'⟩
  let S : Finset (Finset α) := {X' ∈ P'.parts | X' ⊆ Y}
  have hf_maps : ∀ X' ∈ S, f X' ∈ {X ∈ P.parts | X ⊆ Y} := by
    intro X' hX'
    rcases mem_filter.mp hX' with ⟨hX'_mem, hX'_sub⟩
    exact mem_filter.mpr ⟨hf_mem X' hX'_mem, (hf_sub X' hX'_mem).trans hX'_sub⟩
  have hf_inj : Set.InjOn f S := by
    intro X₁ hX₁ X₂ hX₂ hfeq
    have h1_mem : X₁ ∈ P'.parts := (mem_filter.mp hX₁).1
    have h2_mem : X₂ ∈ P'.parts := (mem_filter.mp hX₂).1
    rcases P.nonempty_of_mem_parts (hf_mem X₁ h1_mem) with ⟨x, hx⟩
    exact P'.eq_of_mem_parts h1_mem h2_mem (hf_sub X₁ h1_mem hx) (hf_sub X₂ h2_mem (hfeq ▸ hx))
  have hcard : #S ≤ #{X ∈ P.parts | X ⊆ Y} :=
    card_le_card_of_injOn f hf_maps hf_inj
  exact hcard.trans (href.2 Y hY)

open Classical in
lemma card_bad_le_of_kRefines {A : Type*} {n m r t : ℕ}
    (M : Matrix (Fin n) (Fin m) A)
    {R' R₂ : Finpartition (univ : Finset (Fin n))}
    {C' C₂ : Finpartition (univ : Finset (Fin m))}
    (hrefR : KRefines r R' R₂) (hrefC : KRefines r C' C₂)
    (herr : ∀ X₂ ∈ R₂.parts, #{Y₂ ∈ C₂.parts | ¬ ZoneConst M X₂ Y₂} ≤ t)
    {X' : Finset (Fin n)} (hX' : X' ∈ R'.parts) :
    #{Y' ∈ C'.parts | ¬ ZoneConst M X' Y'} ≤ r * t := by
  rcases hrefR.1 X' hX' with ⟨X₂, hX₂_mem, hX'_sub⟩
  let badC₂ := {Y₂ ∈ C₂.parts | ¬ ZoneConst M X₂ Y₂}
  have hsub : {Y' ∈ C'.parts | ¬ ZoneConst M X' Y'} ⊆
      badC₂.biUnion (fun Y₂ => {Y' ∈ C'.parts | Y' ⊆ Y₂}) := by
    intro Y' hY'
    rw [mem_filter] at hY'
    rcases hrefC.1 Y' hY'.1 with ⟨Y₂, hY₂_mem, hY'_sub⟩
    rw [mem_biUnion]
    refine ⟨Y₂, mem_filter.mpr ⟨hY₂_mem, ?_⟩, mem_filter.mpr ⟨hY'.1, hY'_sub⟩⟩
    intro hconst
    exact hY'.2 (zoneConst_mono hX'_sub hY'_sub hconst)
  calc #{Y' ∈ C'.parts | ¬ ZoneConst M X' Y'}
    _ ≤ #(badC₂.biUnion (fun Y₂ => {Y' ∈ C'.parts | Y' ⊆ Y₂})) := card_le_card hsub
    _ ≤ ∑ Y₂ ∈ badC₂, #{Y' ∈ C'.parts | Y' ⊆ Y₂} := card_biUnion_le
    _ ≤ ∑ _Y₂ ∈ badC₂, r := sum_le_sum (fun Y₂ hY₂ => hrefC.2 Y₂ (mem_filter.mp hY₂).1)
    _ = #badC₂ * r := by rw [sum_const, smul_eq_mul]
    _ ≤ t * r := Nat.mul_le_mul_right r (herr X₂ hX₂_mem)
    _ = r * t := Nat.mul_comm t r

lemma zoneConst_transpose_iff {A : Type*} {n m : ℕ}
    (M : Matrix (Fin n) (Fin m) A) (X : Finset (Fin n)) (Y : Finset (Fin m)) :
    ZoneConst M.transpose Y X ↔ ZoneConst M X Y := by
  constructor
  · intro h i hi i' hi' j hj j' hj'
    exact h j hj j' hj' i hi i' hi'
  · intro h j hj j' hj' i hi i' hi'
    exact h i hi i' hi' j hj j' hj'

open Classical in
lemma errorLE_of_kRefines {A : Type*} {n m r t : ℕ}
    (M : Matrix (Fin n) (Fin m) A)
    {R' R₂ : Finpartition (univ : Finset (Fin n))}
    {C' C₂ : Finpartition (univ : Finset (Fin m))}
    (hrefR : KRefines r R' R₂) (hrefC : KRefines r C' C₂)
    (herr : ErrorLE M R₂ C₂ t) :
    ErrorLE M R' C' (r * t) := by
  refine ⟨fun X' hX' => card_bad_le_of_kRefines M hrefR hrefC herr.1 hX', fun Y' hY' => ?_⟩
  have herr_trans : ∀ Y₂ ∈ C₂.parts, #{X₂ ∈ R₂.parts | ¬ ZoneConst M.transpose Y₂ X₂} ≤ t := by
    intro Y₂ hY₂
    simp_rw [zoneConst_transpose_iff]
    exact herr.2 Y₂ hY₂
  have h := card_bad_le_of_kRefines M.transpose hrefC hrefR herr_trans hY'
  simp_rw [zoneConst_transpose_iff] at h
  exact h

open Classical in
lemma errorLE_bot {A : Type*} {n m : ℕ} (M : Matrix (Fin n) (Fin m) A) (d : ℕ) :
    ErrorLE M ⊥ ⊥ d := by
  have hconst : ∀ X ∈ (⊥ : Finpartition (univ : Finset (Fin n))).parts,
      ∀ Y ∈ (⊥ : Finpartition (univ : Finset (Fin m))).parts, ZoneConst M X Y := by
    intro X hX Y hY i hi i' hi' j hj j' hj'
    rw [Finpartition.mem_bot_iff] at hX hY
    rcases hX with ⟨x, _, rfl⟩
    rcases hY with ⟨y, _, rfl⟩
    rw [mem_singleton.mp hi, mem_singleton.mp hi', mem_singleton.mp hj, mem_singleton.mp hj']
  refine ⟨fun X hX => ?_, fun Y hY => ?_⟩
  · have h_empty : {Y ∈ (⊥ : Finpartition (univ : Finset (Fin m))).parts | ¬ ZoneConst M X Y} = ∅ := by
      rw [filter_eq_empty_iff]
      intro Y hY hnc
      exact hnc (hconst X hX Y hY)
    rw [h_empty, card_empty]
    exact Nat.zero_le d
  · have h_empty : {X ∈ (⊥ : Finpartition (univ : Finset (Fin n))).parts | ¬ ZoneConst M X Y} = ∅ := by
      rw [filter_eq_empty_iff]
      intro X hX hnc
      exact hnc (hconst X hX Y hY)
    rw [h_empty, card_empty]
    exact Nat.zero_le d

/-- Merge two distinct parts `X, Y ∈ P.parts` of a `Finpartition s`. -/
def mergeParts {α : Type*} [DecidableEq α] {s : Finset α}
    (P : Finpartition s) {X Y : Finset α} (hX : X ∈ P.parts) (hY : Y ∈ P.parts) (hne : X ≠ Y) :
    Finpartition s where
  parts := insert (X ∪ Y) ((P.parts.erase X).erase Y)
  supIndep := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    intro A hA B hB hAB
    simp only [mem_coe, mem_insert, mem_erase] at hA hB
    have hdisj : ∀ {U V}, U ∈ P.parts → V ∈ P.parts → U ≠ V → Disjoint U V :=
      fun hU hV hUV => P.disjoint hU hV hUV
    change Disjoint A B
    rcases hA with rfl | ⟨hAY, hAX, hA_mem⟩
    · rcases hB with rfl | ⟨hBY, hBX, hB_mem⟩
      · exact False.elim (hAB rfl)
      · exact disjoint_sup_left.mpr ⟨hdisj hX hB_mem (Ne.symm hBX),
          hdisj hY hB_mem (Ne.symm hBY)⟩
    · rcases hB with rfl | ⟨_, _, hB_mem⟩
      · exact disjoint_sup_right.mpr ⟨hdisj hA_mem hX hAX, hdisj hA_mem hY hAY⟩
      · exact hdisj hA_mem hB_mem hAB
  sup_parts := by
    refine Eq.trans ?_ P.sup_parts
    ext a
    simp only [mem_sup, id_eq, mem_insert, mem_erase]
    constructor
    · rintro ⟨Z, rfl | ⟨_, _, hZ⟩, ha⟩
      · rcases mem_union.mp ha with haX | haY
        · exact ⟨X, hX, haX⟩
        · exact ⟨Y, hY, haY⟩
      · exact ⟨Z, hZ, ha⟩
    · rintro ⟨Z, hZ, ha⟩
      by_cases hZX : Z = X
      · rw [hZX] at ha
        exact ⟨X ∪ Y, Or.inl rfl, mem_union_left Y ha⟩
      · by_cases hZY : Z = Y
        · rw [hZY] at ha
          exact ⟨X ∪ Y, Or.inl rfl, mem_union_right X ha⟩
        · exact ⟨Z, Or.inr ⟨hZY, hZX, hZ⟩, ha⟩
  bot_notMem := by
    intro hmem
    simp only [bot_eq_empty, mem_insert, mem_erase] at hmem
    rcases hmem with heq | ⟨_, _, hZ⟩
    · rcases P.nonempty_of_mem_parts hX with ⟨x, hx⟩
      exact Nonempty.ne_empty ⟨x, mem_union_left Y hx⟩ heq.symm
    · exact P.ne_bot hZ rfl

lemma exists_mergeStep_of_lt {α : Type*} [DecidableEq α] {s : Finset α}
    {P Q : Finpartition s} (hPQ : P ≤ Q) (hlt : #Q.parts < #P.parts) :
    ∃ P₁ : Finpartition s,
      IsMergeStep P P₁ ∧ P ≤ P₁ ∧ P₁ ≤ Q ∧ #P₁.parts + 1 = #P.parts := by
  have hex : ∀ u : {X // X ∈ P.parts}, ∃ Z ∈ Q.parts, u.1 ⊆ Z :=
    fun u => hPQ u.2
  choose g hg_mem hg_sub using hex
  let f : Finset α → Finset α := fun X => if hX : X ∈ P.parts then g ⟨X, hX⟩ else ∅
  have hf_mem : ∀ X ∈ P.parts, f X ∈ Q.parts := by
    intro X hX
    dsimp [f]
    rw [dif_pos hX]
    exact hg_mem ⟨X, hX⟩
  have hf_sub : ∀ X ∈ P.parts, X ⊆ f X := by
    intro X hX
    dsimp [f]
    rw [dif_pos hX]
    exact hg_sub ⟨X, hX⟩
  have hex_pair : ∃ X ∈ P.parts, ∃ Y ∈ P.parts, X ≠ Y ∧ f X = f Y := by
    by_contra! h_inj
    have hle : #P.parts ≤ #Q.parts :=
      card_le_card_of_injOn f (fun X hX => hf_mem X hX) (fun X hX Y hY hfeq => by
        by_contra hne
        exact h_inj X hX Y hY hne hfeq)
    omega
  rcases hex_pair with ⟨X, hX, Y, hY, hne, hfeq⟩
  let P₁ := mergeParts P hX hY hne
  have hstep : IsMergeStep P P₁ := ⟨X, hX, Y, hY, hne, rfl⟩
  have hP_le_P₁ : P ≤ P₁ := by
    intro Z hZ
    by_cases hZX : Z = X
    · rw [hZX]
      exact ⟨X ∪ Y, mem_insert_self _ _, subset_union_left⟩
    · by_cases hZY : Z = Y
      · rw [hZY]
        exact ⟨X ∪ Y, mem_insert_self _ _, subset_union_right⟩
      · exact ⟨Z, mem_insert_of_mem (mem_erase.mpr ⟨hZY, mem_erase.mpr ⟨hZX, hZ⟩⟩), Subset.rfl⟩
  have hP₁_le_Q : P₁ ≤ Q := by
    intro Z hZ
    change Z ∈ insert (X ∪ Y) ((P.parts.erase X).erase Y) at hZ
    rcases mem_insert.mp hZ with rfl | hZ'
    · refine ⟨f X, hf_mem X hX, union_subset (hf_sub X hX) ?_⟩
      rw [hfeq]
      exact hf_sub Y hY
    · have hZ_mem : Z ∈ P.parts := mem_of_mem_erase (mem_of_mem_erase hZ')
      exact hPQ hZ_mem
  have h_not_mem : X ∪ Y ∉ (P.parts.erase X).erase Y := by
    intro hmem
    have h_in_P : X ∪ Y ∈ P.parts := mem_of_mem_erase (mem_of_mem_erase hmem)
    have h_ne_X : X ∪ Y ≠ X := (mem_erase.mp (mem_of_mem_erase hmem)).1
    rcases P.nonempty_of_mem_parts hX with ⟨x, hx⟩
    exact h_ne_X (P.eq_of_mem_parts h_in_P hX (mem_union_left Y hx) hx)
  have hY_mem_erase : Y ∈ P.parts.erase X := mem_erase.mpr ⟨hne.symm, hY⟩
  have h1 : #(insert (X ∪ Y) ((P.parts.erase X).erase Y)) = #((P.parts.erase X).erase Y) + 1 :=
    card_insert_of_notMem h_not_mem
  have h2 : #((P.parts.erase X).erase Y) + 1 = #(P.parts.erase X) :=
    card_erase_add_one hY_mem_erase
  have h3 : #(P.parts.erase X) + 1 = #P.parts :=
    card_erase_add_one hX
  have hcard_P₁ : #P₁.parts + 1 = #P.parts := by
    change #(insert (X ∪ Y) ((P.parts.erase X).erase Y)) + 1 = #P.parts
    omega
  exact ⟨P₁, hstep, hP_le_P₁, hP₁_le_Q, hcard_P₁⟩

lemma eq_of_le_of_card_le {α : Type*} [DecidableEq α] {s : Finset α}
    {P Q : Finpartition s} (hPQ : P ≤ Q) (hcard : #P.parts ≤ #Q.parts) : P = Q := by
  have hex : ∀ u : {Y // Y ∈ Q.parts}, ∃ X ∈ P.parts, X ⊆ u.1 :=
    fun u => Finpartition.exists_le_of_le hPQ u.2
  choose g hg_mem hg_sub using hex
  let f : Finset α → Finset α := fun Y => if hY : Y ∈ Q.parts then g ⟨Y, hY⟩ else ∅
  have hf_mem : ∀ Y ∈ Q.parts, f Y ∈ P.parts := by
    intro Y hY
    dsimp [f]
    rw [dif_pos hY]
    exact hg_mem ⟨Y, hY⟩
  have hf_sub : ∀ Y ∈ Q.parts, f Y ⊆ Y := by
    intro Y hY
    dsimp [f]
    rw [dif_pos hY]
    exact hg_sub ⟨Y, hY⟩
  have hf_inj : Set.InjOn f Q.parts := by
    intro Y₁ hY₁ Y₂ hY₂ hfeq
    rcases P.nonempty_of_mem_parts (hf_mem Y₁ hY₁) with ⟨x, hx⟩
    exact Q.eq_of_mem_parts hY₁ hY₂ (hf_sub Y₁ hY₁ hx) (hf_sub Y₂ hY₂ (hfeq ▸ hx))
  have h_im_sub : Q.parts.image f ⊆ P.parts := by
    intro X hX
    rcases mem_image.mp hX with ⟨Y, hY, rfl⟩
    exact hf_mem Y hY
  have h_im_eq : Q.parts.image f = P.parts :=
    eq_of_subset_of_card_le h_im_sub (by rw [card_image_of_injOn hf_inj]; exact hcard)
  have hQP : Q ≤ P := by
    intro Y hY
    refine ⟨f Y, hf_mem Y hY, ?_⟩
    intro y hy
    rcases P.exists_mem (Q.le hY hy) with ⟨X, hX, hyX⟩
    rw [← h_im_eq, mem_image] at hX
    rcases hX with ⟨Y', hY', rfl⟩
    have hyY' : y ∈ Y' := hf_sub Y' hY' hyX
    have hYY' : Y' = Y := Q.eq_of_mem_parts hY' hY hyY' hy
    subst hYY'
    exact hyX
  exact le_antisymm hPQ hQP

/-- Inductive reachability via single row or column merge steps with error value at most `d`. -/
inductive Reaches {A : Type*} {n m : ℕ} (M : Matrix (Fin n) (Fin m) A) (d : ℕ) :
    Finpartition (univ : Finset (Fin n)) × Finpartition (univ : Finset (Fin m)) →
    Finpartition (univ : Finset (Fin n)) × Finpartition (univ : Finset (Fin m)) → Prop
  | refl (P Q) (herr : ErrorLE M P Q d) : Reaches M d (P, Q) (P, Q)
  | stepR {P₁ P₂ P₃ Q₁ Q₃} (hstep : IsMergeStep P₁ P₂) (herr : ErrorLE M P₁ Q₁ d)
      (hrest : Reaches M d (P₂, Q₁) (P₃, Q₃)) : Reaches M d (P₁, Q₁) (P₃, Q₃)
  | stepC {P₁ P₃ Q₁ Q₂ Q₃} (hstep : IsMergeStep Q₁ Q₂) (herr : ErrorLE M P₁ Q₁ d)
      (hrest : Reaches M d (P₁, Q₂) (P₃, Q₃)) : Reaches M d (P₁, Q₁) (P₃, Q₃)

lemma Reaches.trans {A : Type*} {n m d : ℕ} {M : Matrix (Fin n) (Fin m) A}
    {u v w : Finpartition (univ : Finset (Fin n)) × Finpartition (univ : Finset (Fin m))}
    (h1 : Reaches M d u v) (h2 : Reaches M d v w) : Reaches M d u w := by
  induction h1 with
  | refl _ _ _ => exact h2
  | stepR hstep herr _ ih => exact Reaches.stepR hstep herr (ih h2)
  | stepC hstep herr _ ih => exact Reaches.stepC hstep herr (ih h2)

lemma reaches_row_of_le {A : Type*} {n m d : ℕ} (M : Matrix (Fin n) (Fin m) A)
    (Q : Finpartition (univ : Finset (Fin m))) :
    ∀ (k : ℕ) (P₀ P P₂ : Finpartition (univ : Finset (Fin n))),
      P₀ ≤ P → P ≤ P₂ → #P.parts - #P₂.parts ≤ k →
      (∀ P', P₀ ≤ P' → P' ≤ P₂ → ErrorLE M P' Q d) →
      Reaches M d (P, Q) (P₂, Q) := by
  intro k
  induction k with
  | zero =>
    intro P₀ P P₂ hP₀P hPP₂ hk herr
    have hP_eq : P = P₂ := eq_of_le_of_card_le hPP₂ (by omega)
    subst hP_eq
    exact Reaches.refl P Q (herr P hP₀P hPP₂)
  | succ k ih =>
    intro P₀ P P₂ hP₀P hPP₂ hk herr
    by_cases hlt : #P₂.parts < #P.parts
    · rcases exists_mergeStep_of_lt hPP₂ hlt with ⟨P₁, hstep, hPP₁, hP₁P₂, hcard⟩
      refine Reaches.stepR hstep (herr P hP₀P hPP₂) ?_
      exact ih P₀ P₁ P₂ (hP₀P.trans hPP₁) hP₁P₂ (by omega) herr
    · exact ih P₀ P P₂ hP₀P hPP₂ (by omega) herr

lemma reaches_col_of_le {A : Type*} {n m d : ℕ} (M : Matrix (Fin n) (Fin m) A)
    (P : Finpartition (univ : Finset (Fin n))) :
    ∀ (k : ℕ) (Q₀ Q Q₂ : Finpartition (univ : Finset (Fin m))),
      Q₀ ≤ Q → Q ≤ Q₂ → #Q.parts - #Q₂.parts ≤ k →
      (∀ Q', Q₀ ≤ Q' → Q' ≤ Q₂ → ErrorLE M P Q' d) →
      Reaches M d (P, Q) (P, Q₂) := by
  intro k
  induction k with
  | zero =>
    intro Q₀ Q Q₂ hQ₀Q hQQ₂ hk herr
    have hQ_eq : Q = Q₂ := eq_of_le_of_card_le hQQ₂ (by omega)
    subst hQ_eq
    exact Reaches.refl P Q (herr Q hQ₀Q hQQ₂)
  | succ k ih =>
    intro Q₀ Q Q₂ hQ₀Q hQQ₂ hk herr
    by_cases hlt : #Q₂.parts < #Q.parts
    · rcases exists_mergeStep_of_lt hQQ₂ hlt with ⟨Q₁, hstep, hQQ₁, hQ₁Q₂, hcard⟩
      refine Reaches.stepC hstep (herr Q hQ₀Q hQQ₂) ?_
      exact ih Q₀ Q₁ Q₂ (hQ₀Q.trans hQQ₁) hQ₁Q₂ (by omega) herr
    · exact ih Q₀ Q Q₂ hQ₀Q hQQ₂ (by omega) herr

lemma exists_seq_of_reaches {A : Type*} {n m d : ℕ} {M : Matrix (Fin n) (Fin m) A}
    {u v : Finpartition (univ : Finset (Fin n)) × Finpartition (univ : Finset (Fin m))}
    (h : Reaches M d u v) :
    ∃ (K : ℕ) (R : Fin (K + 1) → Finpartition (univ : Finset (Fin n)))
      (C : Fin (K + 1) → Finpartition (univ : Finset (Fin m))),
      R 0 = u.1 ∧ C 0 = u.2 ∧ R (Fin.last K) = v.1 ∧ C (Fin.last K) = v.2 ∧
      (∀ i : Fin K, (IsMergeStep (R i.castSucc) (R i.succ) ∧ C i.succ = C i.castSucc) ∨
                    (R i.succ = R i.castSucc ∧ IsMergeStep (C i.castSucc) (C i.succ))) ∧
      ∀ i, ErrorLE M (R i) (C i) d := by
  induction h with
  | refl P Q herr =>
    refine ⟨0, fun _ => P, fun _ => Q, rfl, rfl, rfl, rfl, ?_, fun _ => herr⟩
    intro i
    exact Fin.elim0 i
  | @stepR P₁ P₂ P₃ Q₁ Q₃ hstep herr _ ih =>
    rcases ih with ⟨K, R, C, hR0, hC0, hRK, hCK, hsteps, herrs⟩
    refine ⟨K + 1, Fin.cons P₁ R, Fin.cons Q₁ C,
      rfl, rfl, ?_, ?_, ?_, ?_⟩
    · rw [← Fin.succ_last K, Fin.cons_succ, hRK]
    · rw [← Fin.succ_last K, Fin.cons_succ, hCK]
    · intro i
      refine Fin.cases ?_ ?_ i
      · left
        rw [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_zero, Fin.cons_succ, Fin.cons_succ, hR0, hC0]
        exact ⟨hstep, rfl⟩
      · intro j
        rw [Fin.castSucc_succ]
        simp only [Fin.cons_succ]
        exact hsteps j
    · intro i
      refine Fin.cases ?_ ?_ i
      · simp only [Fin.cons_zero]
        exact herr
      · intro j
        simp only [Fin.cons_succ]
        exact herrs j
  | @stepC P₁ P₃ Q₁ Q₂ Q₃ hstep herr _ ih =>
    rcases ih with ⟨K, R, C, hR0, hC0, hRK, hCK, hsteps, herrs⟩
    refine ⟨K + 1, Fin.cons P₁ R, Fin.cons Q₁ C,
      rfl, rfl, ?_, ?_, ?_, ?_⟩
    · rw [← Fin.succ_last K, Fin.cons_succ, hRK]
    · rw [← Fin.succ_last K, Fin.cons_succ, hCK]
    · intro i
      refine Fin.cases ?_ ?_ i
      · right
        rw [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_zero, Fin.cons_succ, Fin.cons_succ, hR0, hC0]
        exact ⟨rfl, hstep⟩
      · intro j
        rw [Fin.castSucc_succ]
        simp only [Fin.cons_succ]
        exact hsteps j
    · intro i
      refine Fin.cases ?_ ?_ i
      · simp only [Fin.cons_zero]
        exact herr
      · intro j
        simp only [Fin.cons_succ]
        exact herrs j

end TwinWidthI.GridThm.Lemma52Proof

open TwinWidthI.GridThm.Lemma52Proof

theorem solution {A : Type*} [Fintype A] {n m : ℕ} (M : Matrix (Fin n) (Fin m) A) (r t N : ℕ)
    (R : Fin (N + 1) → Finpartition (Finset.univ : Finset (Fin n)))
    (C : Fin (N + 1) → Finpartition (Finset.univ : Finset (Fin m)))
    (hR0 : R 0 = ⊥) (hC0 : C 0 = ⊥)
    (hRN : (R (Fin.last N)).parts.card ≤ 1) (hCN : (C (Fin.last N)).parts.card ≤ 1)
    (hrefR : ∀ i : Fin N, KRefines r (R i.castSucc) (R i.succ))
    (hrefC : ∀ i : Fin N, KRefines r (C i.castSucc) (C i.succ))
    (herr : ∀ i, ErrorLE M (R i) (C i) t) :
    MatTwinWidthLE M (r * t) := by
  have h_reaches : ∀ k (hk : k ≤ N),
      Reaches M (r * t) (R 0, C 0)
        (R ⟨k, Nat.lt_succ_of_le hk⟩, C ⟨k, Nat.lt_succ_of_le hk⟩) := by
    intro k
    induction k with
    | zero =>
      intro _
      change Reaches M (r * t) (R 0, C 0) (R 0, C 0)
      refine Reaches.refl (R 0) (C 0) ?_
      rw [hR0, hC0]
      exact errorLE_bot M (r * t)
    | succ k ih =>
      intro hk
      let idx : Fin N := ⟨k, hk⟩
      have h_prev : Reaches M (r * t) (R 0, C 0) (R idx.castSucc, C idx.castSucc) :=
        ih (Nat.le_of_succ_le hk)
      have hR_le : R idx.castSucc ≤ R idx.succ := (hrefR idx).1
      have hC_le : C idx.castSucc ≤ C idx.succ := (hrefC idx).1
      have h_row : Reaches M (r * t) (R idx.castSucc, C idx.castSucc)
          (R idx.succ, C idx.castSucc) :=
        reaches_row_of_le M (C idx.castSucc)
          (#(R idx.castSucc).parts - #(R idx.succ).parts)
          (R idx.castSucc) (R idx.castSucc) (R idx.succ) le_rfl hR_le le_rfl
          (fun R' h1 h2 => errorLE_of_kRefines M
            (kRefines_of_le h1 h2 (hrefR idx)) (hrefC idx) (herr idx.succ))
      have hrefR_self : KRefines r (R idx.succ) (R idx.succ) :=
        kRefines_of_le hR_le le_rfl (hrefR idx)
      have h_col : Reaches M (r * t) (R idx.succ, C idx.castSucc)
          (R idx.succ, C idx.succ) :=
        reaches_col_of_le M (R idx.succ)
          (#(C idx.castSucc).parts - #(C idx.succ).parts)
          (C idx.castSucc) (C idx.castSucc) (C idx.succ) le_rfl hC_le le_rfl
          (fun C' h1 h2 => errorLE_of_kRefines M
            hrefR_self (kRefines_of_le h1 h2 (hrefC idx)) (herr idx.succ))
      exact h_prev.trans (h_row.trans h_col)
  rcases exists_seq_of_reaches (h_reaches N le_rfl) with
    ⟨K, R', C', hR'0, hC'0, hR'K, hC'K, hsteps, herrs⟩
  refine ⟨K, R', C', ?_, ?_, ?_, ?_, hsteps, herrs⟩
  · rw [hR'0, hR0]
  · rw [hC'0, hC0]
  · rw [hR'K]
    exact hRN
  · rw [hC'K]
    exact hCN
