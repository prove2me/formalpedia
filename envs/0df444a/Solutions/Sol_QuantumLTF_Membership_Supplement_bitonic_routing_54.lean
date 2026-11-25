-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.bitonic_routing_54
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-25T01:55:01.515909+00:00
-- url     : https://prove2.me/submissions/63e25f34-5869-4d26-b3fc-92e5ca0fc2b0

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54

set_option autoImplicit false

namespace BitonicSol54

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement Thm49Primitives Thm410Router Cslib.BitonicSort

section Compat

private lemma fin_append_castAdd_natAdd {α : Type*} {n m : ℕ} {f : Fin (n + m) → α} :
    Fin.append (fun i => f (Fin.castAdd m i)) (fun i => f (Fin.natAdd n i)) = f := by
  funext i
  cases i using Fin.addCases with
  | left j => simp
  | right j => simp

private lemma fin_comp_append {α β : Type*} {n m : ℕ} (g : α → β)
    (u : Fin n → α) (v : Fin m → α) :
    g ∘ Fin.append u v = Fin.append (g ∘ u) (g ∘ v) := by
  funext i
  cases i using Fin.addCases with
  | left j => simp
  | right j => simp

end Compat

section Basic
variable {α κ : Type*}

private theorem source_involutive [LinearOrder κ] (key : α → κ) {n : ℕ}
    (ascending : Bool) (input : Fin (n + n) → α) :
    Function.Involutive (compareLayer.source key ascending input) := by
  intro index
  cases index using Fin.addCases <;>
    simp only [compareLayer.source, Fin.addCases_left, Fin.addCases_right] <;>
    split_ifs <;> simp_all [-Fin.natAdd_eq_addNat]

theorem compareLayer_perm [LinearOrder κ] (key : α → κ) {n : ℕ}
    (ascending : Bool) (input : Fin (n + n) → α) :
    (List.ofFn (compareLayer key ascending input)).Perm (List.ofFn input) :=
  (Function.Involutive.toPerm _ (source_involutive key ascending input)).ofFn_comp_perm input

private theorem perm_fin_append {m : ℕ} {f₁ f₂ : Fin m → α} {g : Fin (m + m) → α}
    (h1 : (List.ofFn f₁).Perm (List.ofFn (g ∘ Fin.castAdd m)))
    (h2 : (List.ofFn f₂).Perm (List.ofFn (g ∘ Fin.natAdd m))) :
    (List.ofFn (Fin.append f₁ f₂)).Perm (List.ofFn g) := by
  have h := h1.append h2
  have hsplit : Fin.append (g ∘ Fin.castAdd m) (g ∘ Fin.natAdd m) = g := fin_append_castAdd_natAdd
  rwa [← List.ofFn_fin_append, ← List.ofFn_fin_append, hsplit] at h

theorem merge_perm [LinearOrder κ] (key : α → κ) (depth : ℕ)
    (ascending : Bool) (input : Fin (arity depth) → α) :
    (List.ofFn (merge key depth ascending input)).Perm (List.ofFn input) := by
  induction depth generalizing ascending with
  | zero => exact List.Perm.refl _
  | succ depth ih =>
    let compared := compareLayer key (n := arity depth) ascending input
    exact (perm_fin_append (ih ascending (compared ∘ Fin.castAdd (arity depth)))
      (ih ascending (compared ∘ Fin.natAdd (arity depth)))).trans
      (compareLayer_perm key ascending input)

theorem sort_perm [LinearOrder κ] (key : α → κ) (depth : ℕ)
    (ascending : Bool) (input : Fin (arity depth) → α) :
    (List.ofFn (sort key depth ascending input)).Perm (List.ofFn input) := by
  induction depth generalizing ascending with
  | zero => exact List.Perm.refl _
  | succ depth ih =>
    exact (merge_perm key (depth + 1) ascending _).trans
      (perm_fin_append (ih true (input ∘ Fin.castAdd (arity depth)))
        (ih false (input ∘ Fin.natAdd (arity depth))))

end Basic
/-! ### ZeroOne -/

section ZeroOne
variable {α : Type*}

private def boolHalfMin (sequence : Fin 8 → Bool) : Fin 4 → Bool :=
  fun i => min (sequence (Fin.castAdd 4 i)) (sequence (Fin.natAdd 4 i))

private theorem bool_min_bitonic (input : Fin 8 → Bool) (h : IsBitonic input) :
    IsBitonic (boolHalfMin input) := by
  intro i j k l hij hjk hkl
  obtain ⟨rfl, rfl, rfl, rfl⟩ : i = 0 ∧ j = 1 ∧ k = 2 ∧ l = 3 := by
    refine ⟨Fin.ext ?_, Fin.ext ?_, Fin.ext ?_, Fin.ext ?_⟩ <;> omega
  have h0123 := h 0 1 2 3 (by decide) (by decide) (by decide)
  have h0127 := h 0 1 2 7 (by decide) (by decide) (by decide)
  have h0167 := h 0 1 6 7 (by decide) (by decide) (by decide)
  have h1234 := h 1 2 3 4 (by decide) (by decide) (by decide)
  have h2345 := h 2 3 4 5 (by decide) (by decide) (by decide)
  have h4567 := h 4 5 6 7 (by decide) (by decide) (by decide)
  change (min (min (input 0) (input 4)) (min (input 2) (input 6)) ≤
      max (min (input 1) (input 5)) (min (input 3) (input 7))) ∧
    (min (min (input 1) (input 5)) (min (input 3) (input 7)) ≤
      max (min (input 0) (input 4)) (min (input 2) (input 6)))
  revert h0123 h0127 h0167 h1234 h2345 h4567
  generalize input 0 = b0, input 1 = b1, input 2 = b2, input 3 = b3,
    input 4 = b4, input 5 = b5, input 6 = b6, input 7 = b7
  decide +revert

private def threshold [LinearOrder α] (pivot value : α) : Bool :=
  decide (pivot ≤ value)

private theorem threshold_mono [LinearOrder α] (pivot : α) :
    Monotone (threshold pivot) := by
  intro first second hle
  simp only [threshold, decide_eq_true_eq, Bool.le_iff_imp]
  exact fun hpivot => hpivot.trans hle

@[simp] private theorem threshold_min [LinearOrder α]
    (pivot first second : α) :
    threshold pivot (min first second) =
      min (threshold pivot first) (threshold pivot second) := by
  simp only [threshold, Bool.min_eq_and, Bool.decide_and, le_min_iff]

@[simp] private theorem threshold_max [LinearOrder α]
    (pivot first second : α) :
    threshold pivot (max first second) =
      max (threshold pivot first) (threshold pivot second) := by
  simp only [threshold, Bool.max_eq_or, Bool.decide_or, le_max_iff]

private theorem bitonic_threshold [LinearOrder α] {n : ℕ}
    {sequence : Fin n → α} (hsequence : IsBitonic sequence)
    (pivot : α) :
    IsBitonic (fun i => threshold pivot (sequence i)) := by
  intro i j k l hij hjk hkl
  have h := hsequence i j k l hij hjk hkl
  constructor
  · rw [← threshold_min, ← threshold_max]
    exact threshold_mono pivot h.1
  · rw [← threshold_min, ← threshold_max]
    exact threshold_mono pivot h.2

@[simp] private theorem finAppend_addNat_self {n : ℕ}
    (first second : Fin n → α) (i : Fin n) :
    Fin.append first second (i.addNat n) = second i := by
  simpa only [Fin.natAdd_eq_addNat] using Fin.append_right first second i

private def selectFour {n : ℕ} (i j k l : Fin n) : Fin 4 → Fin n :=
  ![i, j, k, l]

@[simp] private theorem selectFour_zero {n : ℕ} (i j k l : Fin n) :
    selectFour i j k l 0 = i := rfl

@[simp] private theorem selectFour_one {n : ℕ} (i j k l : Fin n) :
    selectFour i j k l 1 = j := rfl

@[simp] private theorem selectFour_two {n : ℕ} (i j k l : Fin n) :
    selectFour i j k l 2 = k := rfl

@[simp] private theorem selectFour_three {n : ℕ} (i j k l : Fin n) :
    selectFour i j k l 3 = l := rfl

private theorem selectFour_strictMono {n : ℕ} (i j k l : Fin n)
    (hij : i < j) (hjk : j < k) (hkl : k < l) :
    StrictMono (selectFour i j k l) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro index
  fin_cases index <;> assumption

private def embedEight {n : ℕ} (i j k l : Fin n) : Fin 8 → Fin (n + n) :=
  fun index =>
    if hleft : index.val < 4 then
      Fin.castAdd n (selectFour i j k l ⟨index.val, hleft⟩)
    else
      Fin.natAdd n
        (selectFour i j k l ⟨index.val - 4, by omega⟩)

private theorem embedEight_strictMono {n : ℕ} (i j k l : Fin n)
    (hij : i < j) (hjk : j < k) (hkl : k < l) :
    StrictMono (embedEight i j k l) := by
  intro first second hlt
  unfold embedEight
  split_ifs with hfirst hsecond
  · change
      (selectFour i j k l ⟨first.val, hfirst⟩).val <
        (selectFour i j k l ⟨second.val, hsecond⟩).val
    apply selectFour_strictMono i j k l hij hjk hkl
    exact hlt
  · change
      (selectFour i j k l ⟨first.val, hfirst⟩).val <
        n + (selectFour i j k l ⟨second.val - 4, by omega⟩).val
    have hbound := (selectFour i j k l ⟨first.val, hfirst⟩).isLt
    omega
  · exfalso
    omega
  · change
      n + (selectFour i j k l ⟨first.val - 4, by omega⟩).val <
        n + (selectFour i j k l ⟨second.val - 4, by omega⟩).val
    apply Nat.add_lt_add_left
    apply selectFour_strictMono i j k l hij hjk hkl
    simp only [Fin.mk_lt_mk]
    omega

private theorem IsBitonic.comp_strictMono
    [LinearOrder α] {n m : ℕ} {sequence : Fin n → α}
    (hsequence : IsBitonic sequence) {embed : Fin m → Fin n}
    (hembed : StrictMono embed) :
    IsBitonic (fun index => sequence (embed index)) := by
  intro i j k l hij hjk hkl
  exact hsequence _ _ _ _ (hembed hij) (hembed hjk) (hembed hkl)

private theorem localEight_bitonic [LinearOrder α] {n : ℕ}
    (first second : Fin n → α)
    (hsequence : IsBitonic (Fin.append first second))
    (i j k l : Fin n) (hij : i < j) (hjk : j < k) (hkl : k < l) :
    IsBitonic
      ![first i, first j, first k, first l,
        second i, second j, second k, second l] := by
  have hselected := IsBitonic.comp_strictMono hsequence
    (embedEight_strictMono i j k l hij hjk hkl)
  have hequal :
      (fun index => Fin.append first second (embedEight i j k l index)) =
        ![first i, first j, first k, first l,
          second i, second j, second k, second l] := by
    funext index
    fin_cases index <;>
      simp [embedEight, selectFour]
  rw [hequal] at hselected
  exact hselected

theorem IsBitonic.min_halves [LinearOrder α] {n : ℕ}
    (first second : Fin n → α)
    (hsequence : IsBitonic (Fin.append first second)) :
    IsBitonic (min first second) := by
  intro i j k l hij hjk hkl
  let localSequence : Fin 8 → α :=
    ![first i, first j, first k, first l,
      second i, second j, second k, second l]
  have hlocal : IsBitonic localSequence :=
    localEight_bitonic first second hsequence
      i j k l hij hjk hkl
  have hhalf (pivot : α) :
      boolHalfMin (fun index => threshold pivot (localSequence index)) =
        fun index => threshold pivot
          (min first second (selectFour i j k l index)) := by
    funext index
    fin_cases index <;>
      simp [boolHalfMin, localSequence, selectFour]
  have reflect (a b : α) (h : ∀ pivot, threshold pivot a ≤ threshold pivot b) : a ≤ b := by
    have htrue := Bool.le_iff_imp.mp (h a) (by simp [threshold])
    exact of_decide_eq_true htrue
  have hbool (pivot : α) := bool_min_bitonic _ (bitonic_threshold hlocal pivot)
  constructor
  · apply reflect
    intro pivot
    simpa only [hhalf, selectFour_zero, selectFour_one, selectFour_two, selectFour_three,
      threshold_min, threshold_max] using (hbool pivot 0 1 2 3 (by omega) (by omega) (by omega)).1
  · apply reflect
    intro pivot
    simpa only [hhalf, selectFour_zero, selectFour_one, selectFour_two, selectFour_three,
      threshold_min, threshold_max] using (hbool pivot 0 1 2 3 (by omega) (by omega) (by omega)).2

theorem IsBitonic.dual [LinearOrder α] {n : ℕ} {input : Fin n → α}
    (h : IsBitonic input) : IsBitonic (κ := OrderDual α) input := by
  intro i j k l hij hjk hkl
  exact (h i j k l hij hjk hkl).symm

theorem IsBitonic.max_halves [LinearOrder α] {n : ℕ} (first second : Fin n → α)
    (h : IsBitonic (Fin.append first second)) : IsBitonic (max first second) :=
  (by
    have hdual : IsBitonic (κ := OrderDual α) (Fin.append first second) := @IsBitonic.dual α _ _ _ h
    have hmin := IsBitonic.min_halves (α := OrderDual α) first second hdual
    intro i j k l hij hjk hkl
    exact (hmin i j k l hij hjk hkl).symm)

end ZeroOne

/-! ### Correctness -/

section Correctness
variable {α κ : Type*}

theorem IsBitonic.min_le_max_halves [LinearOrder κ] {n : ℕ} (first second : Fin n → κ)
    (h : IsBitonic (Fin.append first second)) (i j : Fin n) :
    min (first i) (second i) ≤ max (first j) (second j) := by
  rcases lt_trichotomy i j with hij | hij | hij
  · have h' := h (Fin.castAdd n i) (Fin.castAdd n j) (Fin.natAdd n i) (Fin.natAdd n j)
      hij (Fin.lt_def.mpr (by simp; omega)) (Fin.lt_def.mpr (by simp; exact hij))
    simpa only [Fin.append_left, Fin.append_right] using h'.1
  · subst j
    exact (min_le_left _ _).trans (le_max_left _ _)
  · have h' := h (Fin.castAdd n j) (Fin.castAdd n i) (Fin.natAdd n j) (Fin.natAdd n i)
      hij (Fin.lt_def.mpr (by simp; omega)) (Fin.lt_def.mpr (by simp; exact hij))
    simpa only [Fin.append_left, Fin.append_right] using h'.2

private theorem append_left_value {n m : ℕ} (first : Fin n → κ) (second : Fin m → κ)
    (i : Fin (n + m)) (hi : i.val < n) : Fin.append first second i = first ⟨i.val, hi⟩ :=
  Fin.append_left first second ⟨i.val, hi⟩

private theorem append_right_value {n m : ℕ} (first : Fin n → κ) (second : Fin m → κ)
    (i : Fin (n + m)) (hi : ¬i.val < n) :
    Fin.append first second i = second ⟨i.val - n, by omega⟩ := by
  have heq : i = Fin.natAdd n ⟨i.val - n, by omega⟩ := by ext; simp; omega
  exact (congrArg (Fin.append first second) heq).trans (Fin.append_right _ _ _)

theorem isBitonic_append [LinearOrder κ] {n m : ℕ} {first : Fin n → κ}
    {second : Fin m → κ} (hfirst : Monotone first) (hsecond : Antitone second) :
    IsBitonic (Fin.append first second) := by
  have hpeak (i j k : Fin (n + m)) (hij : i < j) (hjk : j < k) :
      min (Fin.append first second i) (Fin.append first second k) ≤
        Fin.append first second j := by
    by_cases hj : j.val < n
    · have hi : i.val < n := by omega
      apply (min_le_left _ _).trans
      rw [append_left_value first second i hi, append_left_value first second j hj]
      exact hfirst (le_of_lt hij)
    · have hk : ¬k.val < n := by omega
      apply (min_le_right _ _).trans
      rw [append_right_value first second k hk, append_right_value first second j hj]
      apply hsecond
      change j.val - n ≤ k.val - n
      omega
  intro i j k l hij hjk hkl
  exact ⟨(hpeak i j k hij hjk).trans (le_max_left _ _),
    (hpeak j k l hjk hkl).trans (le_max_right _ _)⟩

private theorem monotone_append [Preorder κ] {n m : ℕ} {first : Fin n → κ}
    {second : Fin m → κ} (hfirst : Monotone first) (hsecond : Monotone second)
    (hcross : ∀ i j, first i ≤ second j) : Monotone (Fin.append first second) := by
  intro i j hij
  cases i using Fin.addCases <;> cases j using Fin.addCases <;> rename_i i j
  · simpa only [Fin.append_left] using hfirst hij
  · simpa only [Fin.append_left, Fin.append_right] using hcross _ _
  · exfalso; exact absurd hij (not_le_of_gt (Fin.lt_def.mpr (by simp; omega)))
  · simpa only [Fin.append_right] using hsecond (Nat.le_of_add_le_add_left hij)

private theorem compareLayer_keys [LinearOrder κ] (key : α → κ) {n : ℕ} (ascending : Bool)
    (input : Fin (n + n) → α) :
    key ∘ compareLayer key ascending input =
      let first := key ∘ input ∘ Fin.castAdd n
      let second := key ∘ input ∘ Fin.natAdd n
      if ascending then Fin.append (min first second) (max first second)
      else Fin.append (max first second) (min first second) := by
  funext index
  dsimp only [compareLayer, Function.comp_def]
  cases ascending <;> cases index using Fin.addCases <;>
    dsimp only [compareLayer.source, Function.comp_def] <;>
    simp only [Bool.false_eq_true,
      ↓reduceIte, Fin.addCases_left, Fin.addCases_right, Fin.append_left, Fin.append_right] <;>
    split_ifs <;> simp_all [min_def, max_def, -Fin.natAdd_eq_addNat]

private theorem perm_cross [Preorder κ] (key : α → κ) {n m : ℕ}
    {first first' : Fin n → α} {second second' : Fin m → α}
    (hfirst : (List.ofFn first').Perm (List.ofFn first))
    (hsecond : (List.ofFn second').Perm (List.ofFn second))
    (hcross : ∀ i j, key (first i) ≤ key (second j)) (i : Fin n) (j : Fin m) :
    key (first' i) ≤ key (second' j) := by
  obtain ⟨p, hp⟩ := List.mem_ofFn.mp (hfirst.mem_iff.mp (List.mem_ofFn.mpr ⟨i, rfl⟩))
  obtain ⟨q, hq⟩ := List.mem_ofFn.mp (hsecond.mem_iff.mp (List.mem_ofFn.mpr ⟨j, rfl⟩))
  rw [← hp, ← hq]
  exact hcross p q

theorem merge_sorted [LinearOrder κ] (key : α → κ) (depth : ℕ) (ascending : Bool)
    (input : Fin (arity depth) → α) (hbitonic : IsBitonic (key ∘ input)) :
    if ascending then Monotone (key ∘ merge key depth ascending input)
    else Antitone (key ∘ merge key depth ascending input) := by
  induction depth generalizing ascending with
  | zero =>
    cases ascending <;> intro i j _ <;>
      have h : i = j := Subsingleton.elim (α := Fin 1) i j <;> simp [h]
  | succ depth ih =>
    change Fin (arity depth + arity depth) → α at input
    change IsBitonic (n := arity depth + arity depth) (key ∘ input) at hbitonic
    let left := key ∘ input ∘ Fin.castAdd (arity depth)
    let right := key ∘ input ∘ Fin.natAdd (arity depth)
    have hpairs : IsBitonic (Fin.append left right) := by
      have hsplit : Fin.append (input ∘ Fin.castAdd (arity depth))
          (input ∘ Fin.natAdd (arity depth)) = input := fin_append_castAdd_natAdd
      simpa only [left, right, ← fin_comp_append, hsplit] using hbitonic
    let compared := compareLayer key (n := arity depth) ascending input
    let first := compared ∘ Fin.castAdd (arity depth)
    let second := compared ∘ Fin.natAdd (arity depth)
    have hfirst : key ∘ first = if ascending then min left right else max left right := by
      funext i
      dsimp only [first, compared, left, right, Function.comp_def]
      have h := congrFun (compareLayer_keys key ascending input) (Fin.castAdd (arity depth) i)
      cases ascending <;>
        simpa only [Bool.false_eq_true, ↓reduceIte, Fin.append_left, Function.comp_def] using h
    have hsecond : key ∘ second = if ascending then max left right else min left right := by
      funext i
      dsimp only [second, compared, left, right, Function.comp_def]
      have h := congrFun (compareLayer_keys key ascending input) (Fin.natAdd (arity depth) i)
      cases ascending <;>
        simpa only [Bool.false_eq_true, ↓reduceIte, Fin.append_right, Function.comp_def] using h
    have hbfirst : IsBitonic (key ∘ first) := by
      rw [hfirst]
      cases ascending
      · exact IsBitonic.max_halves left right hpairs
      · exact IsBitonic.min_halves left right hpairs
    have hbsecond : IsBitonic (key ∘ second) := by
      rw [hsecond]
      cases ascending
      · exact IsBitonic.min_halves left right hpairs
      · exact IsBitonic.max_halves left right hpairs
    have hf := ih ascending first hbfirst
    have hs := ih ascending second hbsecond
    have hpf := merge_perm key depth ascending first
    have hps := merge_perm key depth ascending second
    change if ascending then Monotone (key ∘ Fin.append
      (merge key depth ascending first) (merge key depth ascending second)) else
      Antitone (key ∘ Fin.append
        (merge key depth ascending first) (merge key depth ascending second))
    rw [fin_comp_append]
    cases ascending with
    | false =>
      apply monotone_append (κ := OrderDual κ) hf hs
      apply perm_cross (κ := OrderDual κ) key hpf hps
      intro i j
      change (key ∘ second) j ≤ (key ∘ first) i
      rw [hfirst, hsecond]
      exact IsBitonic.min_le_max_halves left right hpairs j i
    | true =>
      apply monotone_append hf hs
      apply perm_cross key hpf hps
      intro i j
      change (key ∘ first) i ≤ (key ∘ second) j
      rw [hfirst, hsecond]
      exact IsBitonic.min_le_max_halves left right hpairs i j

theorem sort_sorted [LinearOrder κ] (key : α → κ) (depth : ℕ) (ascending : Bool)
    (input : Fin (arity depth) → α) :
    if ascending then Monotone (key ∘ sort key depth ascending input)
    else Antitone (key ∘ sort key depth ascending input) := by
  induction depth generalizing ascending with
  | zero =>
    cases ascending <;> intro i j _ <;>
      have h : i = j := Subsingleton.elim (α := Fin 1) i j <;> simp [h]
  | succ depth ih =>
    apply merge_sorted
    change IsBitonic (n := arity depth + arity depth) (key ∘ Fin.append
      (sort key depth true (input ∘ Fin.castAdd (arity depth)))
      (sort key depth false (input ∘ Fin.natAdd (arity depth))))
    rw [fin_comp_append]
    exact isBitonic_append (ih true _) (ih false _)

theorem monotone_sort [LinearOrder κ] (key : α → κ) (depth : ℕ)
    (input : Fin (arity depth) → α) : Monotone (key ∘ sort key depth true input) :=
  sort_sorted key depth true input

theorem antitone_sort [LinearOrder κ] (key : α → κ) (depth : ℕ)
    (input : Fin (arity depth) → α) : Antitone (key ∘ sort key depth false input) :=
  sort_sorted key depth false input

end Correctness

section Trace
variable {α β κ : Type*}

@[simp] theorem routeLayer_routeLayer {n : ℕ} (flags : Fin n → Bool)
    (x : Fin (n + n) → α) : routeLayer flags (routeLayer flags x) = x := by
  funext i
  cases i using Fin.addCases <;> simp only [routeLayer, Fin.append_left, Fin.append_right] <;>
    split_ifs <;> rfl

def layerFlags [LinearOrder κ] (key : α → κ) {n : ℕ} (ascending : Bool)
    (x : Fin (n + n) → α) : Fin n → Bool :=
  fun i => decide (if ascending then key (x (Fin.natAdd n i)) < key (x (Fin.castAdd n i))
    else ¬key (x (Fin.natAdd n i)) < key (x (Fin.castAdd n i)))

private theorem routeLayer_layerFlags [LinearOrder κ] (key : α → κ) {n : ℕ}
    (ascending : Bool) (x : Fin (n + n) → α) :
    routeLayer (layerFlags key ascending x) x = compareLayer key ascending x := by
  funext i
  cases i using Fin.addCases <;>
    simp only [routeLayer, layerFlags, compareLayer, compareLayer.source, Function.comp_apply,
      Fin.append_left, Fin.append_right, Fin.addCases_left, Fin.addCases_right, decide_eq_true_eq]
  all_goals split_ifs <;> rfl
@[simp] theorem unrouteMerge_routeMerge (d : ℕ) (flags : Fin (mergeTraceSize d) → Bool)
    (x : Fin (arity d) → α) : unrouteMerge d flags (routeMerge d flags x) = x := by
  induction d with
  | zero => rfl
  | succ d ih =>
    dsimp only [mergeTraceSize, arity] at flags x
    simp only [routeMerge, unrouteMerge, arity, mergeTraceSize]
    simp only [Function.comp_def, Fin.append_left, Fin.append_right, ih]
    rw [fin_append_castAdd_natAdd]
    exact routeLayer_routeLayer _ x

@[simp] theorem routeMerge_unrouteMerge (d : ℕ) (flags : Fin (mergeTraceSize d) → Bool)
    (x : Fin (arity d) → α) : routeMerge d flags (unrouteMerge d flags x) = x := by
  induction d with
  | zero => rfl
  | succ d ih =>
    dsimp only [mergeTraceSize, arity] at flags x
    simp only [routeMerge, unrouteMerge, arity, mergeTraceSize, routeLayer_routeLayer]
    simp only [Function.comp_def, Fin.append_left, Fin.append_right, ih]
    exact fin_append_castAdd_natAdd

@[simp] theorem unrouteSort_routeSort (d : ℕ) (flags : Fin (sortTraceSize d) → Bool)
    (x : Fin (arity d) → α) : unrouteSort d flags (routeSort d flags x) = x := by
  induction d with
  | zero => rfl
  | succ d ih =>
    dsimp only [sortTraceSize, arity] at flags x
    simp only [routeSort, unrouteSort, arity, sortTraceSize]
    erw [unrouteMerge_routeMerge]
    simp only [Function.comp_def, Fin.append_left, Fin.append_right, ih]
    exact fin_append_castAdd_natAdd

@[simp] theorem routeSort_unrouteSort (d : ℕ) (flags : Fin (sortTraceSize d) → Bool)
    (x : Fin (arity d) → α) : routeSort d flags (unrouteSort d flags x) = x := by
  induction d with
  | zero => rfl
  | succ d ih =>
    dsimp only [sortTraceSize, arity] at flags x
    simp only [routeSort, unrouteSort, arity, sortTraceSize]
    simp only [Function.comp_def, Fin.append_left, Fin.append_right, ih]
    erw [fin_append_castAdd_natAdd, routeMerge_unrouteMerge]

private theorem routeMerge_mergeTrace [LinearOrder κ] (key : α → κ) (d : ℕ)
    (ascending : Bool) (x : Fin (arity d) → α) :
    routeMerge d (mergeTrace key d ascending x) x = merge key d ascending x := by
  induction d with
  | zero => rfl
  | succ d ih =>
    dsimp only [arity] at x
    simp only [routeMerge, mergeTrace, arity, mergeTraceSize, merge]
    simp only [Function.comp_def, Fin.append_left, Fin.append_right]
    erw [routeLayer_layerFlags]
    simp only [ih]

theorem routeSort_sortTrace [LinearOrder κ] (key : α → κ) (d : ℕ)
    (ascending : Bool) (x : Fin (arity d) → α) :
    routeSort d (sortTrace key d ascending x) x = sort key d ascending x := by
  induction d generalizing ascending with
  | zero => rfl
  | succ d ih =>
    dsimp only [arity] at x
    simp only [routeSort, sortTrace, arity, sortTraceSize, sort]
    simp only [Function.comp_def, Fin.append_left, Fin.append_right, ih]
    exact routeMerge_mergeTrace _ _ _ _

private theorem unrouteSort_sort [LinearOrder κ] (key : α → κ) (d : ℕ)
    (ascending : Bool) (x : Fin (arity d) → α) :
    unrouteSort d (sortTrace key d ascending x) (sort key d ascending x) = x := by
  rw [← routeSort_sortTrace, unrouteSort_routeSort]

private theorem routeLayer_comp {n : ℕ} (flags : Fin n → Bool) (f : α → β)
    (x : Fin (n + n) → α) : routeLayer flags (f ∘ x) = f ∘ routeLayer flags x := by
  funext i
  cases i using Fin.addCases <;>
    simp only [routeLayer, Function.comp_apply, Fin.append_left, Fin.append_right] <;>
    split_ifs <;> rfl

private theorem routeMerge_comp (d : ℕ) (flags : Fin (mergeTraceSize d) → Bool) (f : α → β)
    (x : Fin (arity d) → α) : routeMerge d flags (f ∘ x) = f ∘ routeMerge d flags x := by
  induction d with
  | zero => rfl
  | succ d ih =>
    dsimp only [mergeTraceSize, arity] at flags x
    simp only [routeMerge, arity, mergeTraceSize, routeLayer_comp, fin_comp_append,
      Function.comp_assoc, ih]

theorem routeSort_comp (d : ℕ) (flags : Fin (sortTraceSize d) → Bool) (f : α → β)
    (x : Fin (arity d) → α) : routeSort d flags (f ∘ x) = f ∘ routeSort d flags x := by
  induction d with
  | zero => rfl
  | succ d ih =>
    dsimp only [sortTraceSize, arity] at flags x
    simp only [routeSort, arity, sortTraceSize, Function.comp_assoc, ih]
    erw [← fin_comp_append, routeMerge_comp]
    rfl

theorem unrouteSort_comp_sort [LinearOrder κ] (key : α → κ) (d : ℕ)
    (ascending : Bool) (f : α → β) (x : Fin (arity d) → α) :
    unrouteSort d (sortTrace key d ascending x) (f ∘ sort key d ascending x) = f ∘ x := by
  rw [← routeSort_sortTrace, ← routeSort_comp, unrouteSort_routeSort]

theorem unrouteSort_comp (d : ℕ) (flags : Fin (sortTraceSize d) → Bool) (f : α → β)
    (x : Fin (arity d) → α) : unrouteSort d flags (f ∘ x) = f ∘ unrouteSort d flags x := by
  apply Function.LeftInverse.injective (unrouteSort_routeSort d flags)
  rw [routeSort_unrouteSort, routeSort_comp, routeSort_unrouteSort]

theorem unrouteSort_apply (d : ℕ) (flags : Fin (sortTraceSize d) → Bool)
    (x : Fin (arity d) → α) (i : Fin (arity d)) :
    unrouteSort d flags x i = x (unrouteSort d flags id i) := by
  simpa only [Function.comp_id, Function.comp_apply] using
    congrFun (unrouteSort_comp d flags x id) i

theorem unrouteSort_rel (d : ℕ) (flags : Fin (sortTraceSize d) → Bool)
    (x : Fin (arity d) → α) (y : Fin (arity d) → β) (R : α → β → Prop)
    (h : ∀ i, R (x i) (y i)) (i : Fin (arity d)) :
    R (unrouteSort d flags x i) (unrouteSort d flags y i) := by
  rw [unrouteSort_apply d flags x i, unrouteSort_apply d flags y i]
  exact h _

theorem unrouteSort_rel_sort [LinearOrder κ] (key : α → κ) (d : ℕ)
    (ascending : Bool) (x : Fin (arity d) → α) (y : Fin (arity d) → β)
    (R : α → β → Prop) (h : ∀ i, R (sort key d ascending x i) (y i))
    (i : Fin (arity d)) :
    R (x i) (unrouteSort d (sortTrace key d ascending x) y i) := by
  simpa only [unrouteSort_sort] using
    unrouteSort_rel d (sortTrace key d ascending x) (sort key d ascending x) y R h i

theorem two_mul_mergeTraceSize (d : ℕ) : 2 * mergeTraceSize d = d * 2 ^ d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    calc
      2 * mergeTraceSize (d + 1) = 2 * 2 ^ d + 2 * (2 * mergeTraceSize d) := by
        rw [mergeTraceSize, arity_eq_two_pow]
        ring
      _ = (d + 1) * 2 ^ (d + 1) := by rw [ih, pow_succ]; ring

theorem four_mul_sortTraceSize (d : ℕ) :
    4 * sortTraceSize d = d * (d + 1) * 2 ^ d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    calc
      4 * sortTraceSize (d + 1) =
          2 * (4 * sortTraceSize d) + 2 * (2 * mergeTraceSize (d + 1)) := by
        rw [sortTraceSize]
        ring
      _ = (d + 1) * (d + 1 + 1) * 2 ^ (d + 1) := by
        rw [ih, two_mul_mergeTraceSize, pow_succ]
        ring

end Trace
/-! ### 1. `ltBitsCircuit` -/


private def prefixValLSB (w k : ℕ) (hk : k ≤ w) (x : Qubits w) : ℕ :=
  ∑ j : Fin k, if x ⟨w - 1 - j.1, by omega⟩ then 2 ^ j.1 else 0

private lemma prefixValLSB_lt (w k : ℕ) (hk : k ≤ w) (x : Qubits w) :
    prefixValLSB w k hk x < 2 ^ k := by
  induction k with
  | zero => simp [prefixValLSB]
  | succ k ih =>
    simp only [prefixValLSB, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
    have h1 : (∑ j : Fin k, if x ⟨w - 1 - j.1, by omega⟩ then 2 ^ j.1 else 0) =
        prefixValLSB w k (by omega) x := rfl
    have hlt := ih (by omega)
    have h2 : (if x ⟨w - 1 - k, by omega⟩ then 2 ^ k else 0) ≤ 2 ^ k := by split_ifs <;> omega
    rw [h1, pow_succ']
    omega

private lemma prefixValLSB_succ (w k : ℕ) (hk : k + 1 ≤ w) (x : Qubits w) :
    prefixValLSB w (k + 1) hk x =
      prefixValLSB w k (by omega) x + (if x ⟨w - 1 - k, by omega⟩ then 2 ^ k else 0) := by
  simp [prefixValLSB, Fin.sum_univ_castSucc]

private lemma prefixValLSB_full (w : ℕ) (x : Qubits w) :
    prefixValLSB w w le_rfl x = bitsToNat x := by
  dsimp only [prefixValLSB, bitsToNat]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun i => ?_
  have hi := i.isLt
  have heq : (⟨w - 1 - i.1, by omega⟩ : Fin w) = i.rev := Fin.ext (by simp [Fin.val_rev]; omega)
  rw [heq]
  simp only [Fin.revPerm_apply, Fin.val_rev]
  have he : w - 1 - (w - (i.1 + 1)) = i.1 := by omega
  rw [he]

private lemma lt_step_bool (w k : ℕ) (hk : k + 1 ≤ w) (a b : Qubits w) :
    let ax := a ⟨w - 1 - k, by omega⟩
    let by_ := b ⟨w - 1 - k, by omega⟩
    let br := decide (prefixValLSB w k (by omega) a < prefixValLSB w k (by omega) b)
    decide (prefixValLSB w (k + 1) hk a < prefixValLSB w (k + 1) hk b) =
      xor br ((xor by_ ax) && (xor br by_)) := by
  intro ax by_ br
  have ha := prefixValLSB_lt w k (by omega) a
  have hb := prefixValLSB_lt w k (by omega) b
  rw [prefixValLSB_succ, prefixValLSB_succ]
  change decide (_ + (if ax then 2 ^ k else 0) < _ + (if by_ then 2 ^ k else 0)) = _
  by_cases hax : ax <;> by_cases hby : by_ <;> by_cases hbr : br
  all_goals (dsimp only [ax, by_, br] at *; simp_all <;> omega)

private noncomputable def ltFwdStep (w : ℕ) : (k : ℕ) → k < w → LayeredCircuit ((w + w + 1) + w)
  | 0, hk =>
    let xa : Fin ((w + w + 1) + w) := ⟨w - 1 - 0, by omega⟩
    let yb : Fin ((w + w + 1) + w) := ⟨w + (w - 1 - 0), by omega⟩
    let brOut : Fin ((w + w + 1) + w) := ⟨w + w + 1 + 0, by omega⟩
    have hxy : xa ≠ yb := Fin.ne_of_val_ne (by dsimp [xa, yb]; omega)
    have hxo : xa ≠ brOut := Fin.ne_of_val_ne (by dsimp [xa, brOut]; omega)
    have hyo : yb ≠ brOut := Fin.ne_of_val_ne (by dsimp [yb, brOut]; omega)
    (pauliXGate xa).seq ((toffoliOn xa yb brOut hxy hxo hyo).seq (pauliXGate xa))
  | k' + 1, hk =>
    let xa : Fin ((w + w + 1) + w) := ⟨w - 1 - (k' + 1), by omega⟩
    let yb : Fin ((w + w + 1) + w) := ⟨w + (w - 1 - (k' + 1)), by omega⟩
    let brOut : Fin ((w + w + 1) + w) := ⟨w + w + 1 + (k' + 1), by omega⟩
    let brIn : Fin ((w + w + 1) + w) := ⟨w + w + 1 + k', by omega⟩
    have hio : brIn ≠ brOut := Fin.ne_of_val_ne (by dsimp [brIn, brOut]; omega)
    have hyi : yb ≠ brIn := Fin.ne_of_val_ne (by dsimp [yb, brIn]; omega)
    have hxy : xa ≠ yb := Fin.ne_of_val_ne (by dsimp [xa, yb]; omega)
    have hyo : yb ≠ brOut := Fin.ne_of_val_ne (by dsimp [yb, brOut]; omega)
    (cnotGate brIn brOut hio).seq
      ((cnotGate yb brIn hyi).seq
        ((cnotGate xa yb hxy).seq
          ((toffoliOn yb brIn brOut hyi hyo hio).seq
            ((cnotGate xa yb hxy).seq (cnotGate yb brIn hyi)))))

private lemma ltFwdStep_size (w k : ℕ) (hk : k < w) :
    (ltFwdStep w k hk).size ≤ 10 := by
  cases k <;> simp [ltFwdStep]

private lemma act_ltFwdStep_ket (w k : ℕ) (hk : k < w) (z : Qubits ((w + w + 1) + w))
    (hclean : z ⟨w + w + 1 + k, by omega⟩ = false) :
    let xa := z ⟨w - 1 - k, by omega⟩
    let yb := z ⟨w + (w - 1 - k), by omega⟩
    let brIn : Bool := if _h0 : k = 0 then false else z ⟨w + w + 1 + (k - 1), by omega⟩
    act (ltFwdStep w k hk).unitary (ket z) =
      ket (Function.update z ⟨w + w + 1 + k, by omega⟩
        (xor brIn ((xor yb xa) && (xor brIn yb)))) := by
  cases k with
  | zero =>
    intro xa yb brIn
    dsimp only [ltFwdStep]
    simp only [LayeredCircuit.seq_unitary, act_mul, act_pauliXGate_ket, act_toffoliOn_ket]
    congr 1; funext u
    have h1 : (⟨w + w + 1 + 0, by omega⟩ : Fin ((w + w + 1) + w)) ≠ ⟨w - 1 - 0, by omega⟩ :=
      Fin.ne_of_val_ne (by dsimp; omega)
    have h2 : (⟨w - 1 - 0, by omega⟩ : Fin ((w + w + 1) + w)) ≠ ⟨w + (w - 1 - 0), by omega⟩ :=
      Fin.ne_of_val_ne (by dsimp; omega)
    have h3 : (⟨w + w + 1 + 0, by omega⟩ : Fin ((w + w + 1) + w)) ≠ ⟨w + (w - 1 - 0), by omega⟩ :=
      Fin.ne_of_val_ne (by dsimp; omega)
    have hbr0 : brIn = false := dif_pos rfl
    by_cases hu : u = ⟨w + w + 1 + 0, by omega⟩
    · subst hu
      simp only [Function.update_self, Function.update_of_ne h1, Function.update_of_ne h1.symm,
        Function.update_of_ne h2.symm, hclean, hbr0]
      cases hxa : z ⟨w - 1 - 0, by omega⟩ <;> cases hyb : z ⟨w + (w - 1 - 0), by omega⟩ <;>
        simp [xa, yb, hxa, hyb]
    · by_cases hux : u = ⟨w - 1 - 0, by omega⟩
      · subst hux
        simp only [Function.update_self, Function.update_of_ne h1, Function.update_of_ne h1.symm]
        simp
      · simp only [Function.update_of_ne hux, Function.update_of_ne hu]
  | succ k' =>
    intro xa yb brIn
    dsimp only [ltFwdStep]
    simp only [LayeredCircuit.seq_unitary, act_mul, act_cnotGate_ket, act_toffoliOn_ket]
    congr 1; funext u
    have hXY : (⟨w - 1 - (k' + 1), by omega⟩ : Fin ((w + w + 1) + w)) ≠
        ⟨w + (w - 1 - (k' + 1)), by omega⟩ := Fin.ne_of_val_ne (by dsimp; omega)
    have hXI : (⟨w - 1 - (k' + 1), by omega⟩ : Fin ((w + w + 1) + w)) ≠
        ⟨w + w + 1 + k', by omega⟩ := Fin.ne_of_val_ne (by dsimp; omega)
    have hXO : (⟨w - 1 - (k' + 1), by omega⟩ : Fin ((w + w + 1) + w)) ≠
        ⟨w + w + 1 + (k' + 1), by omega⟩ := Fin.ne_of_val_ne (by dsimp; omega)
    have hYI : (⟨w + (w - 1 - (k' + 1)), by omega⟩ : Fin ((w + w + 1) + w)) ≠
        ⟨w + w + 1 + k', by omega⟩ := Fin.ne_of_val_ne (by dsimp; omega)
    have hYO : (⟨w + (w - 1 - (k' + 1)), by omega⟩ : Fin ((w + w + 1) + w)) ≠
        ⟨w + w + 1 + (k' + 1), by omega⟩ := Fin.ne_of_val_ne (by dsimp; omega)
    have hIO : (⟨w + w + 1 + k', by omega⟩ : Fin ((w + w + 1) + w)) ≠
        ⟨w + w + 1 + (k' + 1), by omega⟩ := Fin.ne_of_val_ne (by dsimp; omega)
    by_cases huO : u = ⟨w + w + 1 + (k' + 1), by omega⟩
    · rw [huO]
      have hbr : brIn = z ⟨w + w + 1 + k', by omega⟩ := dif_neg (Nat.succ_ne_zero k')
      dsimp only [xa, yb]
      simp only [Function.update_self,
        Function.update_of_ne hXY, Function.update_of_ne hXI,
        Function.update_of_ne hXO,
        Function.update_of_ne hYI, Function.update_of_ne hYI.symm,
        Function.update_of_ne hYO, Function.update_of_ne hYO.symm,
        Function.update_of_ne hIO, Function.update_of_ne hIO.symm,
        hclean, Bool.false_xor, hbr]
    · by_cases huI : u = ⟨w + w + 1 + k', by omega⟩
      · rw [huI]
        simp only [Function.update_self,
          Function.update_of_ne hXY, Function.update_of_ne hXI,
          Function.update_of_ne hXO,
          Function.update_of_ne hYI, Function.update_of_ne hYI.symm,
          Function.update_of_ne hYO, Function.update_of_ne hYO.symm,
          Function.update_of_ne hIO, Function.update_of_ne hIO.symm,
          Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
      · by_cases huY : u = ⟨w + (w - 1 - (k' + 1)), by omega⟩
        · rw [huY]
          simp only [Function.update_self,
            Function.update_of_ne hXY, Function.update_of_ne hXI,
            Function.update_of_ne hXO,
            Function.update_of_ne hYI, Function.update_of_ne hYI.symm,
            Function.update_of_ne hYO, Function.update_of_ne hYO.symm,
            Function.update_of_ne hIO, Function.update_of_ne hIO.symm,
            Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
        · simp only [Function.update_of_ne huO, Function.update_of_ne huI, Function.update_of_ne huY]

private noncomputable def ltFwdPrefix (w : ℕ) : (k : ℕ) → k ≤ w → LayeredCircuit ((w + w + 1) + w)
  | 0, _ => LayeredCircuit.id _
  | k + 1, hk => (ltFwdPrefix w k (by omega)).seq (ltFwdStep w k hk)

private lemma ltFwdPrefix_size (w k : ℕ) (hk : k ≤ w) :
    (ltFwdPrefix w k hk).size ≤ 10 * k := by
  induction k with
  | zero => simp [ltFwdPrefix]
  | succ k ih =>
    simp only [ltFwdPrefix, LayeredCircuit.seq_size]
    have h1 := ih (by omega)
    have h2 := ltFwdStep_size w k hk
    omega

private lemma ltFwdPrefix_usesOnly (w k : ℕ) (hk : k ≤ w) :
    (ltFwdPrefix w k hk).UsesOnly (Finset.univ.filter fun u => u.1 ≠ w + w) := by
  induction k with
  | zero => exact LayeredCircuit.id_usesOnly _
  | succ k ih =>
    refine LayeredCircuit.seq_usesOnly (ih (by omega)) ?_
    cases k with
    | zero =>
      dsimp only [ltFwdStep]
      refine LayeredCircuit.seq_usesOnly ((pauliXGate_usesOnly _).mono ?_)
        (LayeredCircuit.seq_usesOnly ((toffoliOn_usesOnly _ _ _ _ _ _).mono ?_)
          ((pauliXGate_usesOnly _).mono ?_)) <;>
        intro u hu <;> simp only [Finset.mem_insert, Finset.mem_singleton] at hu <;>
        rcases hu with rfl | rfl | rfl <;> simp <;> try omega
    | succ k' =>
      dsimp only [ltFwdStep]
      refine LayeredCircuit.seq_usesOnly ((cnotGate_usesOnly _ _ _).mono ?_)
        (LayeredCircuit.seq_usesOnly ((cnotGate_usesOnly _ _ _).mono ?_)
          (LayeredCircuit.seq_usesOnly ((cnotGate_usesOnly _ _ _).mono ?_)
            (LayeredCircuit.seq_usesOnly ((toffoliOn_usesOnly _ _ _ _ _ _).mono ?_)
              (LayeredCircuit.seq_usesOnly ((cnotGate_usesOnly _ _ _).mono ?_)
                ((cnotGate_usesOnly _ _ _).mono ?_))))) <;>
        intro u hu <;> simp only [Finset.mem_insert, Finset.mem_singleton] at hu <;>
        rcases hu with rfl | rfl | rfl <;> simp <;> try omega

private lemma act_ltFwdPrefix_ket (w : ℕ) (k : ℕ) (hk : k ≤ w) (x : Qubits (w + w + 1)) :
    let a : Qubits w := fun i => x ⟨i.1, by omega⟩
    let b : Qubits w := fun i => x ⟨w + i.1, by omega⟩
    ∃ z' : Qubits ((w + w + 1) + w),
      act (ltFwdPrefix w k hk).unitary (ket (padZero (w + w + 1) w x)) = ket z' ∧
      (∀ u : Fin ((w + w + 1) + w), u.1 ≤ w + w → z' u = padZero (w + w + 1) w x u) ∧
      (∀ m : Fin w, k ≤ m.1 → z' ⟨w + w + 1 + m.1, by omega⟩ = false) ∧
      (∀ hk1 : 1 ≤ k, z' ⟨w + w + 1 + (k - 1), by omega⟩ =
        decide (prefixValLSB w k hk a < prefixValLSB w k hk b)) := by
  intro a b
  induction k with
  | zero =>
    refine ⟨padZero (w + w + 1) w x, by simp [ltFwdPrefix, act_one], fun _ _ => rfl, ?_, fun h => by omega⟩
    intro m _
    have hnat : (⟨w + w + 1 + m.1, by omega⟩ : Fin ((w + w + 1) + w)) = Fin.natAdd (w + w + 1) m :=
      Fin.ext rfl
    rw [hnat, padZero_natAdd]
  | succ k ih =>
    rcases ih (by omega) with ⟨z1, hz1_act, hz1_low, hz1_clean, hz1_top⟩
    have hclean_k : z1 ⟨w + w + 1 + k, by omega⟩ = false := hz1_clean ⟨k, hk⟩ le_rfl
    have hstep := act_ltFwdStep_ket w k hk z1 hclean_k
    let brIn : Bool := if h0 : k = 0 then false else z1 ⟨w + w + 1 + (k - 1), by omega⟩
    let z2 := Function.update z1 ⟨w + w + 1 + k, by omega⟩
      (xor brIn ((xor (z1 ⟨w + (w - 1 - k), by omega⟩) (z1 ⟨w - 1 - k, by omega⟩)) &&
        (xor brIn (z1 ⟨w + (w - 1 - k), by omega⟩))))
    refine ⟨z2, ?_, ?_, ?_, ?_⟩
    · change act ((ltFwdPrefix w k (by omega)).seq (ltFwdStep w k hk)).unitary
          (ket (padZero (w + w + 1) w x)) = ket z2
      rw [LayeredCircuit.seq_unitary, act_mul, hz1_act]
      exact hstep
    · intro u hu
      have hne : u ≠ ⟨w + w + 1 + k, by omega⟩ := Fin.ne_of_val_ne (by dsimp; omega)
      dsimp only [z2]
      rw [Function.update_of_ne hne, hz1_low u hu]
    · intro m hm
      have hne : (⟨w + w + 1 + m.1, by omega⟩ : Fin ((w + w + 1) + w)) ≠ ⟨w + w + 1 + k, by omega⟩ :=
        Fin.ne_of_val_ne (by dsimp; omega)
      dsimp only [z2]
      rw [Function.update_of_ne hne]
      exact hz1_clean m (by omega)
    · intro _
      have hidx : (⟨w + w + 1 + (k + 1 - 1), by omega⟩ : Fin ((w + w + 1) + w)) =
          ⟨w + w + 1 + k, by omega⟩ := Fin.ext (by simp)
      rw [hidx]
      dsimp only [z2]
      rw [Function.update_self]
      have hxa : z1 ⟨w - 1 - k, by omega⟩ = a ⟨w - 1 - k, by omega⟩ := by
        rw [hz1_low _ (by dsimp; omega)]
        have hcast : (⟨w - 1 - k, by omega⟩ : Fin ((w + w + 1) + w)) =
            Fin.castAdd w ⟨w - 1 - k, by omega⟩ := Fin.ext rfl
        rw [hcast, padZero_castAdd]
      have hyb : z1 ⟨w + (w - 1 - k), by omega⟩ = b ⟨w - 1 - k, by omega⟩ := by
        rw [hz1_low _ (by dsimp; omega)]
        have hcast : (⟨w + (w - 1 - k), by omega⟩ : Fin ((w + w + 1) + w)) =
            Fin.castAdd w ⟨w + (w - 1 - k), by omega⟩ := Fin.ext rfl
        rw [hcast, padZero_castAdd]
      have hbr : brIn = decide (prefixValLSB w k (by omega) a < prefixValLSB w k (by omega) b) := by
        cases k with
        | zero => simp [brIn, prefixValLSB]
        | succ k' =>
          have htop1 := hz1_top (by omega)
          simpa [brIn] using htop1
      rw [hxa, hyb, hbr]
      exact (lt_step_bool w k hk a b).symm

noncomputable def ltBitsCircuit (w : ℕ) : LayeredCircuit ((w + w + 1) + w) :=
  if hw : 1 ≤ w then
    let fwd := ltFwdPrefix w w le_rfl
    let brLast : Fin ((w + w + 1) + w) := ⟨w + w + 1 + (w - 1), by omega⟩
    let tgt : Fin ((w + w + 1) + w) := ⟨w + w, by omega⟩
    have hne : brLast ≠ tgt := Fin.ne_of_val_ne (by dsimp [brLast, tgt]; omega)
    fwd.seq ((cnotGate brLast tgt hne).seq fwd.adj)
  else
    LayeredCircuit.id ((w + w + 1) + w)

lemma ltBitsCircuit_size (w : ℕ) : (ltBitsCircuit w).size ≤ 20 * w + 1 := by
  unfold ltBitsCircuit
  split_ifs with hw
  · simp only [LayeredCircuit.seq_size, LayeredCircuit.adj_size, cnotGate_size]
    have h := ltFwdPrefix_size w w le_rfl
    omega
  · simp

lemma ltBitsCircuit_implements (w : ℕ) :
    (ltBitsCircuit w).ImplementsOnClean (permMat (ltBitsFn54 w)) := by
  apply implementsOnClean_of_act_perm
  intro x
  by_cases hw : 1 ≤ w
  · simp only [ltBitsCircuit, dif_pos hw]
    let fwd := ltFwdPrefix w w le_rfl
    let brLast : Fin ((w + w + 1) + w) := ⟨w + w + 1 + (w - 1), by omega⟩
    let tgt : Fin ((w + w + 1) + w) := ⟨w + w, by omega⟩
    have hne : brLast ≠ tgt := Fin.ne_of_val_ne (by dsimp [brLast, tgt]; omega)
    rcases act_ltFwdPrefix_ket w w le_rfl x with ⟨z', hz'_act, hz'_low, _, hz'_top⟩
    have htgt_not : tgt ∉ Finset.univ.filter fun u : Fin ((w + w + 1) + w) => u.1 ≠ w + w := by
      simp [tgt]
    have hfwd_adj : ∀ b : Bool,
        act fwd.adj.unitary (ket (Function.update z' tgt b)) =
          ket (Function.update (padZero (w + w + 1) w x) tgt b) := fun b => by
      have hupd := act_ket_update_of_not_mem fwd (ltFwdPrefix_usesOnly w w le_rfl)
        tgt htgt_not hz'_act b
      rw [← hupd, ← act_mul, LayeredCircuit.adj_unitary,
        Matrix.mem_unitaryGroup_iff'.mp fwd.unitary_mem_unitaryGroup, act_one]
    have hz'_tgt : z' tgt = x ⟨w + w, by omega⟩ := by
      rw [hz'_low tgt (by simp [tgt])]
      have hcast : tgt = Fin.castAdd w ⟨w + w, by omega⟩ := Fin.ext rfl
      rw [hcast, padZero_castAdd]
    have htop := hz'_top hw
    rw [prefixValLSB_full, prefixValLSB_full] at htop
    simp only [LayeredCircuit.seq_unitary, act_mul]
    change act fwd.adj.unitary (act (cnotGate brLast tgt hne).unitary (act fwd.unitary (ket (padZero (w + w + 1) w x)))) = _
    rw [hz'_act, act_cnotGate_ket, hfwd_adj, hz'_tgt, htop]
    congr 1; funext u
    by_cases hut : u = tgt
    · subst hut
      have hcast : tgt = Fin.castAdd w ⟨w + w, by omega⟩ := Fin.ext rfl
      rw [Function.update_self, hcast, padZero_castAdd]
      simp [ltBitsFn54]
    · rw [Function.update_of_ne hut]
      cases u using Fin.addCases with
      | left i =>
        rw [padZero_castAdd, padZero_castAdd]
        have hi : i ≠ ⟨w + w, by omega⟩ := fun h => hut (Fin.ext (by simp [tgt, h]))
        simp [ltBitsFn54, Function.update_of_ne hi]
      | right j =>
        rw [padZero_natAdd, padZero_natAdd]
  · have hw0 : w = 0 := by omega
    subst hw0
    simp only [ltBitsCircuit, dif_neg hw, LayeredCircuit.id_unitary, act_one]
    congr 1; funext u
    have hu : u = Fin.castAdd 0 ⟨0, by omega⟩ := Fin.ext (by have := u.isLt; omega)
    rw [hu, padZero_castAdd, padZero_castAdd]
    simp [ltBitsFn54, bitsToNat]

/-! ### 2. `cswapRegCircuit` -/


private noncomputable def cswapStep (w : ℕ) (j : Fin w) : LayeredCircuit (1 + w + w) :=
  let c : Fin (1 + w + w) := ⟨0, by omega⟩
  let a : Fin (1 + w + w) := ⟨1 + j.1, by have := j.isLt; omega⟩
  let b : Fin (1 + w + w) := ⟨1 + w + j.1, by have := j.isLt; omega⟩
  have hca : c ≠ a := Fin.ne_of_val_ne (by dsimp [c, a]; omega)
  have hcb : c ≠ b := Fin.ne_of_val_ne (by dsimp [c, b]; omega)
  have hab : a ≠ b := Fin.ne_of_val_ne (by dsimp [a, b]; omega)
  (cnotGate b a hab.symm).seq ((toffoliOn c a b hca hcb hab).seq (cnotGate b a hab.symm))

private lemma cswapStep_size (w : ℕ) (j : Fin w) : (cswapStep w j).size = 7 := by
  simp [cswapStep]

private lemma act_cswapStep_ket (w : ℕ) (j : Fin w) (x : Qubits (1 + w + w)) :
    let a : Fin (1 + w + w) := ⟨1 + j.1, by have := j.isLt; omega⟩
    let b : Fin (1 + w + w) := ⟨1 + w + j.1, by have := j.isLt; omega⟩
    act (cswapStep w j).unitary (ket x) =
      ket (if x ⟨0, by omega⟩ then Function.update (Function.update x a (x b)) b (x a) else x) := by
  intro a b
  dsimp only [cswapStep]
  simp only [LayeredCircuit.seq_unitary, act_mul, act_cnotGate_ket, act_toffoliOn_ket]
  dsimp only [a, b]
  congr 1; funext k
  have hca : (⟨0, by omega⟩ : Fin (1 + w + w)) ≠ ⟨1 + j.1, by have := j.isLt; omega⟩ :=
    Fin.ne_of_val_ne (by dsimp; omega)
  have hcb : (⟨0, by omega⟩ : Fin (1 + w + w)) ≠ ⟨1 + w + j.1, by have := j.isLt; omega⟩ :=
    Fin.ne_of_val_ne (by dsimp; omega)
  have hab : (⟨1 + j.1, by have := j.isLt; omega⟩ : Fin (1 + w + w)) ≠
      ⟨1 + w + j.1, by have := j.isLt; omega⟩ := Fin.ne_of_val_ne (by dsimp; omega)
  cases hc : x ⟨0, by omega⟩
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hkb : k = ⟨1 + w + j.1, by have := j.isLt; omega⟩
    · rw [hkb]
      simp only [Function.update_self, Function.update_of_ne hca,
        Function.update_of_ne hab, Function.update_of_ne hab.symm, hc, Bool.false_and,
        Bool.xor_false]
    · by_cases hka : k = ⟨1 + j.1, by have := j.isLt; omega⟩
      · rw [hka]
        simp only [Function.update_self, Function.update_of_ne hca,
          Function.update_of_ne hab, Function.update_of_ne hab.symm, hc, Bool.false_and,
          Bool.xor_false, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
      · simp only [Function.update_of_ne hka, Function.update_of_ne hkb]
  · simp only [↓reduceIte]
    by_cases hkb : k = ⟨1 + w + j.1, by have := j.isLt; omega⟩
    · rw [hkb]
      simp only [Function.update_self, Function.update_of_ne hca,
        Function.update_of_ne hab, Function.update_of_ne hab.symm, hc, Bool.true_and]
      cases x ⟨1 + j.1, by have := j.isLt; omega⟩ <;>
        cases x ⟨1 + w + j.1, by have := j.isLt; omega⟩ <;> simp
    · by_cases hka : k = ⟨1 + j.1, by have := j.isLt; omega⟩
      · rw [hka]
        simp only [Function.update_self, Function.update_of_ne hca,
          Function.update_of_ne hab, Function.update_of_ne hab.symm, hc, Bool.true_and]
        cases x ⟨1 + j.1, by have := j.isLt; omega⟩ <;>
          cases x ⟨1 + w + j.1, by have := j.isLt; omega⟩ <;> simp
      · simp only [Function.update_of_ne hka, Function.update_of_ne hkb]

private noncomputable def cswapPrefix (w : ℕ) : (k : ℕ) → k ≤ w → LayeredCircuit (1 + w + w)
  | 0, _ => LayeredCircuit.id _
  | k + 1, hk => (cswapPrefix w k (by omega)).seq (cswapStep w ⟨k, hk⟩)

private lemma cswapPrefix_size (w k : ℕ) (hk : k ≤ w) : (cswapPrefix w k hk).size = 7 * k := by
  induction k with
  | zero => simp [cswapPrefix]
  | succ k ih =>
    simp only [cswapPrefix, LayeredCircuit.seq_size, cswapStep_size, ih]
    omega

private lemma act_cswapPrefix_ket (w k : ℕ) (hk : k ≤ w) (x : Qubits (1 + w + w)) :
    act (cswapPrefix w k hk).unitary (ket x) =
      ket (fun u =>
        if _h0 : u.1 = 0 then x u
        else if x ⟨0, by omega⟩ then
          if h1 : u.1 < 1 + k then x ⟨u.1 + w, by omega⟩
          else if h2 : 1 + w ≤ u.1 ∧ u.1 < 1 + w + k then x ⟨u.1 - w, by omega⟩
          else x u
        else x u) := by
  induction k with
  | zero =>
    simp only [cswapPrefix, LayeredCircuit.id_unitary, act_one]
    congr 1; funext u
    split_ifs <;> first | rfl | omega
  | succ k ih =>
    simp only [cswapPrefix, LayeredCircuit.seq_unitary, act_mul, ih (by omega), act_cswapStep_ket,
      dif_pos True.intro]
    congr 1; funext u
    cases hc : x ⟨0, by omega⟩
    · simp only [Bool.false_eq_true, ↓reduceIte]
    · simp only [↓reduceIte]
      let a : Fin (1 + w + w) := ⟨1 + k, by omega⟩
      let b : Fin (1 + w + w) := ⟨1 + w + k, by omega⟩
      by_cases hub : u = b
      · subst hub
        rw [Function.update_self]
        have ha1 : a.1 ≠ 0 := by dsimp [a]; omega
        have ha2 : ¬ a.1 < 1 + k := by dsimp [a]; omega
        have ha3 : ¬ (1 + w ≤ a.1 ∧ a.1 < 1 + w + k) := by dsimp [a]; omega
        have hb0 : b.1 ≠ 0 := by dsimp [b]; omega
        have hb1 : ¬ b.1 < 1 + (k + 1) := by dsimp [b]; omega
        have hb2 : 1 + w ≤ b.1 ∧ b.1 < 1 + w + (k + 1) := by dsimp [b]; omega
        rw [dif_neg hb0, dif_neg hb1, dif_pos hb2, dif_neg ha1, dif_neg ha2, dif_neg ha3]
        congr 1; apply Fin.ext; dsimp [a, b]; omega
      · rw [Function.update_of_ne hub]
        by_cases hua : u = a
        · subst hua
          rw [Function.update_self]
          have hb0 : b.1 ≠ 0 := by dsimp [b]; omega
          have hb2 : ¬ b.1 < 1 + k := by dsimp [b]; omega
          have hb3 : ¬ (1 + w ≤ b.1 ∧ b.1 < 1 + w + k) := by dsimp [b]; omega
          have ha0 : a.1 ≠ 0 := by dsimp [a]; omega
          have ha1 : a.1 < 1 + (k + 1) := by dsimp [a]; omega
          rw [dif_neg ha0, dif_pos ha1, dif_neg hb0, dif_neg hb2, dif_neg hb3]
          congr 1; apply Fin.ext; dsimp [a, b]; omega
        · rw [Function.update_of_ne hua]
          by_cases hu0 : u.1 = 0
          · simp [hu0]
          · rw [dif_neg hu0, dif_neg hu0]
            have hne_a : u.1 ≠ 1 + k := fun h => hua (Fin.ext h)
            have hne_b : u.1 ≠ 1 + w + k := fun h => hub (Fin.ext h)
            by_cases hu1 : u.1 < 1 + k
            · rw [dif_pos hu1, dif_pos (by omega : u.1 < 1 + (k + 1))]
            · rw [dif_neg hu1, dif_neg (by omega : ¬ u.1 < 1 + (k + 1))]
              by_cases hu2 : 1 + w ≤ u.1 ∧ u.1 < 1 + w + k
              · rw [dif_pos hu2, dif_pos (by omega : 1 + w ≤ u.1 ∧ u.1 < 1 + w + (k + 1))]
              · rw [dif_neg hu2, dif_neg (by omega : ¬ (1 + w ≤ u.1 ∧ u.1 < 1 + w + (k + 1)))]

noncomputable def cswapRegCircuit (w : ℕ) : LayeredCircuit ((1 + w + w) + 0) :=
  cswapPrefix w w le_rfl

lemma cswapRegCircuit_size (w : ℕ) : (cswapRegCircuit w).size = 7 * w :=
  cswapPrefix_size w w le_rfl

lemma cswapRegCircuit_implements (w : ℕ) :
    (cswapRegCircuit w).ImplementsOnClean (permMat (cswapRegFn54 w)) := by
  apply implementsOnClean_of_act_perm
  intro x
  have hpad : ∀ y : Qubits (1 + w + w), padZero (1 + w + w) 0 y = y := fun y => by
    funext u; exact padZero_castAdd (1 + w + w) 0 y u
  rw [hpad x, hpad (cswapRegFn54 w x), cswapRegCircuit, act_cswapPrefix_ket]
  congr 1; funext u
  dsimp only [cswapRegFn54]
  by_cases hu0 : u.1 = 0
  · simp [hu0]
  · rw [dif_neg hu0, dif_neg hu0]
    cases hc : x ⟨0, by omega⟩
    · simp
    · simp only [↓reduceIte]
      have hult := u.isLt
      by_cases huw : u.1 ≤ w
      · rw [dif_pos (by omega : u.1 < 1 + w), dif_pos huw]
      · rw [dif_neg (by omega : ¬ u.1 < 1 + w), dif_pos (by omega : 1 + w ≤ u.1 ∧ u.1 < 1 + w + w),
          dif_neg huw]

/-! ### 3. `routeLayerCircuit`, `routeMergeCircuit`, `routeSortCircuit`, `unrouteSortCircuit` -/

private lemma finProdFinEquiv_val {a b : ℕ} (i : Fin a) (j : Fin b) :
    (finProdFinEquiv (i, j)).1 = i.1 * b + j.1 := by
  simp [finProdFinEquiv]; ring

private lemma fin_prod_lt {a b : ℕ} (i : Fin a) (j : Fin b) : i.1 * b + j.1 < a * b := by
  rw [← finProdFinEquiv_val]; exact (finProdFinEquiv (i, j)).isLt

private def cswapLayerEmb (n w : ℕ) (i : Fin n) :
    Fin (1 + w + w) ↪ Fin ((n + n) * w + n) where
  toFun u :=
    if h0 : u.1 = 0 then ⟨(n + n) * w + i.1, by have := i.isLt; omega⟩
    else if h1 : u.1 < 1 + w then
      ⟨i.1 * w + (u.1 - 1), by
        have hlt := fin_prod_lt (Fin.castAdd n i) (⟨u.1 - 1, by omega⟩ : Fin w)
        change i.1 * w + (u.1 - 1) < (n + n) * w at hlt
        omega⟩
    else
      ⟨(n + i.1) * w + (u.1 - (1 + w)), by
        have hlt := fin_prod_lt (Fin.natAdd n i) (⟨u.1 - (1 + w), by have := u.isLt; omega⟩ : Fin w)
        change (n + i.1) * w + (u.1 - (1 + w)) < (n + n) * w at hlt
        omega⟩
  inj' a b hab := by
    have ha := a.isLt; have hb := b.isLt; have hi := i.isLt
    dsimp only at hab
    have hval := congrArg Fin.val hab
    have hni1 : i.1 * w + w ≤ (n + i.1) * w := by
      rw [Nat.add_mul]
      have : w ≤ n * w := Nat.le_mul_of_pos_left w (by omega)
      omega
    have hni2 : (n + i.1) * w + w ≤ (n + n) * w := by
      rw [Nat.add_mul, Nat.add_mul]
      have hle : i.1 * w + w ≤ n * w := by
        calc i.1 * w + w = (i.1 + 1) * w := by ring
          _ ≤ n * w := Nat.mul_le_mul_right w hi
      omega
    by_cases ha0 : a.1 = 0 <;> by_cases hb0 : b.1 = 0
    · exact Fin.ext (by omega)
    · exfalso
      by_cases hb1 : b.1 < 1 + w
      · rw [dif_pos ha0, dif_neg hb0, dif_pos hb1] at hval; simp only at hval; omega
      · rw [dif_pos ha0, dif_neg hb0, dif_neg hb1] at hval; simp only at hval; omega
    · exfalso
      by_cases ha1 : a.1 < 1 + w
      · rw [dif_neg ha0, dif_pos ha1, dif_pos hb0] at hval; simp only at hval; omega
      · rw [dif_neg ha0, dif_neg ha1, dif_pos hb0] at hval; simp only at hval; omega
    · by_cases ha1 : a.1 < 1 + w <;> by_cases hb1 : b.1 < 1 + w
      · rw [dif_neg ha0, dif_pos ha1, dif_neg hb0, dif_pos hb1] at hval
        simp only at hval; exact Fin.ext (by omega)
      · rw [dif_neg ha0, dif_pos ha1, dif_neg hb0, dif_neg hb1] at hval
        simp only at hval; omega
      · rw [dif_neg ha0, dif_neg ha1, dif_neg hb0, dif_pos hb1] at hval
        simp only at hval; omega
      · rw [dif_neg ha0, dif_neg ha1, dif_neg hb0, dif_neg hb1] at hval
        simp only at hval; exact Fin.ext (by omega)

private lemma cswapLayerEmb_apply (n w : ℕ) (i : Fin n) (u : Fin (1 + w + w)) :
    cswapLayerEmb n w i u =
      if h0 : u.1 = 0 then ⟨(n + n) * w + i.1, by have := i.isLt; omega⟩
      else if h1 : u.1 < 1 + w then
        ⟨i.1 * w + (u.1 - 1), by
          have hlt := fin_prod_lt (Fin.castAdd n i) (⟨u.1 - 1, by omega⟩ : Fin w)
          change i.1 * w + (u.1 - 1) < (n + n) * w at hlt
          omega⟩
      else
        ⟨(n + i.1) * w + (u.1 - (1 + w)), by
          have hlt := fin_prod_lt (Fin.natAdd n i) (⟨u.1 - (1 + w), by have := u.isLt; omega⟩ : Fin w)
          change (n + i.1) * w + (u.1 - (1 + w)) < (n + n) * w at hlt
          omega⟩ := rfl

private lemma cswapLayerEmb_zero (n w : ℕ) (i : Fin n) :
    cswapLayerEmb n w i ⟨0, by omega⟩ = ⟨(n + n) * w + i.1, by have := i.isLt; omega⟩ := by
  rw [cswapLayerEmb_apply, dif_pos rfl]

private lemma cswapLayerEmb_left (n w : ℕ) (i : Fin n) (j : Fin w) :
    cswapLayerEmb n w i ⟨1 + j.1, by have := j.isLt; omega⟩ =
      ⟨i.1 * w + j.1, by
        have hlt := fin_prod_lt (Fin.castAdd n i) j
        change i.1 * w + j.1 < (n + n) * w at hlt; omega⟩ := by
  rw [cswapLayerEmb_apply, dif_neg (by dsimp only; omega), dif_pos (by have := j.isLt; dsimp only; omega)]
  apply Fin.ext; dsimp only; omega

private lemma cswapLayerEmb_right (n w : ℕ) (i : Fin n) (j : Fin w) :
    cswapLayerEmb n w i ⟨1 + w + j.1, by have := j.isLt; omega⟩ =
      ⟨(n + i.1) * w + j.1, by
        have hlt := fin_prod_lt (Fin.natAdd n i) j
        change (n + i.1) * w + j.1 < (n + n) * w at hlt; omega⟩ := by
  rw [cswapLayerEmb_apply, dif_neg (by dsimp only; omega), dif_neg (by dsimp only; omega)]
  apply Fin.ext; dsimp only; omega

private noncomputable def routeLayerPrefix (n w : ℕ) :
    (k : ℕ) → k ≤ n → LayeredCircuit ((n + n) * w + n)
  | 0, _ => LayeredCircuit.id _
  | k + 1, hk =>
    (routeLayerPrefix n w k (by omega)).seq
      ((cswapRegCircuit w).mapWires (cswapLayerEmb n w ⟨k, hk⟩))

private lemma routeLayerPrefix_size (n w k : ℕ) (hk : k ≤ n) :
    (routeLayerPrefix n w k hk).size = 7 * w * k := by
  induction k with
  | zero => simp [routeLayerPrefix]
  | succ k ih =>
    simp only [routeLayerPrefix, LayeredCircuit.seq_size, LayeredCircuit.mapWires_size,
      cswapRegCircuit_size, ih]
    ring

private lemma act_routeLayerPrefix_ket (n w k : ℕ) (hk : k ≤ n)
    (x : Fin (n + n) → Qubits w) (flags : Fin n → Bool) :
    let x' : Fin (n + n) → Qubits w := fun idx =>
      Fin.addCases
        (fun i => if i.1 < k then (if flags i then x (Fin.natAdd n i) else x (Fin.castAdd n i)) else x (Fin.castAdd n i))
        (fun i => if i.1 < k then (if flags i then x (Fin.castAdd n i) else x (Fin.natAdd n i)) else x (Fin.natAdd n i))
        idx
    act (routeLayerPrefix n w k hk).unitary (ket (Fin.append (flatReg (n + n) w x) flags)) =
      ket (Fin.append (flatReg (n + n) w x') flags) := by
  induction k with
  | zero =>
    simp only [routeLayerPrefix, LayeredCircuit.id_unitary, act_one]
    refine congrArg ket (congrArg (fun arr => Fin.append (flatReg (n + n) w arr) flags) ?_)
    funext idx; cases idx using Fin.addCases with
    | left i => simp
    | right i => rw [Fin.addCases_right]; simp
  | succ k ih =>
    let x1 : Fin (n + n) → Qubits w := fun idx =>
      Fin.addCases
        (fun i => if i.1 < k then (if flags i then x (Fin.natAdd n i) else x (Fin.castAdd n i)) else x (Fin.castAdd n i))
        (fun i => if i.1 < k then (if flags i then x (Fin.castAdd n i) else x (Fin.natAdd n i)) else x (Fin.natAdd n i))
        idx
    let x2 : Fin (n + n) → Qubits w := fun idx =>
      Fin.addCases
        (fun i => if i.1 < k + 1 then (if flags i then x (Fin.natAdd n i) else x (Fin.castAdd n i)) else x (Fin.castAdd n i))
        (fun i => if i.1 < k + 1 then (if flags i then x (Fin.castAdd n i) else x (Fin.natAdd n i)) else x (Fin.natAdd n i))
        idx
    change act ((routeLayerPrefix n w k (by omega)).seq
        ((cswapRegCircuit w).mapWires (cswapLayerEmb n w ⟨k, hk⟩))).unitary
        (ket (Fin.append (flatReg (n + n) w x) flags)) = ket (Fin.append (flatReg (n + n) w x2) flags)
    rw [LayeredCircuit.seq_unitary, act_mul, ih (by omega)]
    let z1 := Fin.append (flatReg (n + n) w x1) flags
    let z2 := Fin.append (flatReg (n + n) w x2) flags
    let emb := cswapLayerEmb n w ⟨k, hk⟩
    have hact_cswap : act (cswapRegCircuit w).unitary (ket (z1 ∘ emb)) =
        ket (cswapRegFn54 w (z1 ∘ emb)) := by
      have h := act_ket_of_implementsOnClean_perm (cswapRegCircuit_implements w) (z1 ∘ emb)
      have hpad : ∀ v : Qubits (1 + w + w), padZero (1 + w + w) 0 v = v := fun v => by
        funext u; exact padZero_castAdd (1 + w + w) 0 v u
      simpa [hpad] using h
    have hz1_0 : (z1 ∘ emb) ⟨0, by omega⟩ = flags ⟨k, hk⟩ := by
      dsimp only [Function.comp_apply, emb]
      rw [cswapLayerEmb_zero]
      have heq : (⟨(n + n) * w + k, by omega⟩ : Fin ((n + n) * w + n)) =
          Fin.natAdd ((n + n) * w) ⟨k, hk⟩ := Fin.ext rfl
      dsimp only [z1]; rw [heq, Fin.append_right]
    have hz1_L : ∀ j : Fin w, (z1 ∘ emb) ⟨1 + j.1, by have := j.isLt; omega⟩ =
        x (Fin.castAdd n ⟨k, hk⟩) j := fun j => by
      dsimp only [Function.comp_apply, emb]
      rw [cswapLayerEmb_left]
      have heq : (⟨k * w + j.1, by
          have hlt := fin_prod_lt (Fin.castAdd n ⟨k, hk⟩) j
          simp only [Fin.val_castAdd] at hlt; omega⟩ :
          Fin ((n + n) * w + n)) =
          Fin.castAdd n (finProdFinEquiv (Fin.castAdd n ⟨k, hk⟩, j)) := by
        ext; simp only [Fin.val_castAdd, finProdFinEquiv_val]
      dsimp only [z1]
      rw [heq, Fin.append_left, flatReg, finProdFinEquiv.symm_apply_apply]
      simp only [x1, Fin.addCases_left, lt_irrefl, ↓reduceIte]
    have hz1_R : ∀ j : Fin w, (z1 ∘ emb) ⟨1 + w + j.1, by have := j.isLt; omega⟩ =
        x (Fin.natAdd n ⟨k, hk⟩) j := fun j => by
      dsimp only [Function.comp_apply, emb]
      rw [cswapLayerEmb_right]
      have heq : (⟨(n + k) * w + j.1, by
          have hlt := fin_prod_lt (Fin.natAdd n ⟨k, hk⟩) j
          simp only [Fin.val_natAdd] at hlt; omega⟩ :
          Fin ((n + n) * w + n)) =
          Fin.castAdd n (finProdFinEquiv (Fin.natAdd n ⟨k, hk⟩, j)) := by
        ext; simp only [Fin.val_castAdd, Fin.val_natAdd, finProdFinEquiv_val]
      dsimp only [z1]
      rw [heq, Fin.append_left, flatReg, finProdFinEquiv.symm_apply_apply]
      simp only [x1, Fin.addCases_right, lt_irrefl, ↓reduceIte]
    have hcomp_out : z2 ∘ emb = cswapRegFn54 w (z1 ∘ emb) := by
      funext u
      dsimp only [Function.comp_apply]
      by_cases hu0 : u.1 = 0
      · have hu_eq : u = ⟨0, by have := u.isLt; omega⟩ := Fin.ext hu0
        rw [hu_eq, cswapLayerEmb_zero]
        have heq : (⟨(n + n) * w + k, by omega⟩ : Fin ((n + n) * w + n)) =
            Fin.natAdd ((n + n) * w) ⟨k, hk⟩ := Fin.ext rfl
        dsimp only [z2, cswapRegFn54]; rw [heq, Fin.append_right, dif_pos rfl]
        exact hz1_0.symm
      · by_cases huw : u.1 ≤ w
        · let j : Fin w := ⟨u.1 - 1, by omega⟩
          have hu_eq : u = ⟨1 + j.1, by have := j.isLt; omega⟩ := Fin.ext (by simp [j]; omega)
          rw [hu_eq, cswapLayerEmb_left]
          have heq : (⟨k * w + j.1, by
              have hlt := fin_prod_lt (Fin.castAdd n ⟨k, hk⟩) j
              simp only [Fin.val_castAdd] at hlt; omega⟩ :
              Fin ((n + n) * w + n)) =
              Fin.castAdd n (finProdFinEquiv (Fin.castAdd n ⟨k, hk⟩, j)) := by
            ext; simp only [Fin.val_castAdd, finProdFinEquiv_val]
          dsimp only [z2, cswapRegFn54]
          rw [heq, Fin.append_left, flatReg, finProdFinEquiv.symm_apply_apply]
          simp only [x2, Fin.addCases_left, Nat.lt_add_one_iff.mpr le_rfl, ↓reduceIte]
          have hne0 : (⟨1 + j.1, by have := j.isLt; omega⟩ : Fin (1 + w + w)).1 ≠ 0 := by simp
          have hlew : (⟨1 + j.1, by have := j.isLt; omega⟩ : Fin (1 + w + w)).1 ≤ w := by simp; omega
          rw [dif_neg hne0, dif_pos hlew]
          have h0_eq : (⟨0, by omega⟩ : Fin (1 + w + w)) = ⟨0, by omega⟩ := rfl
          have h1 : (⟨(⟨1 + j.1, by have := j.isLt; omega⟩ : Fin (1 + w + w)).1 + w,
              by have := j.isLt; omega⟩ : Fin (1 + w + w)) =
              ⟨1 + w + j.1, by have := j.isLt; omega⟩ := Fin.ext (by simp; omega)
          rw [h0_eq, hz1_0]
          cases hfl : flags ⟨k, hk⟩
          · simp only [Bool.false_eq_true, ↓reduceIte]
            exact (hz1_L j).symm
          · simp only [↓reduceIte]
            rw [h1, hz1_R j]
        · let j : Fin w := ⟨u.1 - (1 + w), by have := u.isLt; omega⟩
          have hu_eq : u = ⟨1 + w + j.1, by have := j.isLt; omega⟩ := Fin.ext (by simp [j]; omega)
          rw [hu_eq, cswapLayerEmb_right]
          have heq : (⟨(n + k) * w + j.1, by
              have hlt := fin_prod_lt (Fin.natAdd n ⟨k, hk⟩) j
              simp only [Fin.val_natAdd] at hlt; omega⟩ :
              Fin ((n + n) * w + n)) =
              Fin.castAdd n (finProdFinEquiv (Fin.natAdd n ⟨k, hk⟩, j)) := by
            ext; simp only [Fin.val_castAdd, Fin.val_natAdd, finProdFinEquiv_val]
          dsimp only [z2, cswapRegFn54]
          rw [heq, Fin.append_left, flatReg, finProdFinEquiv.symm_apply_apply]
          simp only [x2, Fin.addCases_right, Nat.lt_add_one_iff.mpr le_rfl, ↓reduceIte]
          have hne0 : (⟨1 + w + j.1, by have := j.isLt; omega⟩ : Fin (1 + w + w)).1 ≠ 0 := by simp
          have hnlew : ¬ (⟨1 + w + j.1, by have := j.isLt; omega⟩ : Fin (1 + w + w)).1 ≤ w := by
            simp; omega
          rw [dif_neg hne0, dif_neg hnlew]
          have h0_eq : (⟨0, by omega⟩ : Fin (1 + w + w)) = ⟨0, by omega⟩ := rfl
          have h1 : (⟨(⟨1 + w + j.1, by have := j.isLt; omega⟩ : Fin (1 + w + w)).1 - w,
              by have := j.isLt; omega⟩ : Fin (1 + w + w)) =
              ⟨1 + j.1, by have := j.isLt; omega⟩ := Fin.ext (by simp; omega)
          rw [h0_eq, hz1_0]
          cases hfl : flags ⟨k, hk⟩
          · simp only [Bool.false_eq_true, ↓reduceIte]
            exact (hz1_R j).symm
          · simp only [↓reduceIte]
            rw [h1, hz1_L j]
    refine act_mapWires_ket (cswapRegCircuit w) emb z1 (cswapRegFn54 w (z1 ∘ emb)) hact_cswap z2
      hcomp_out ?_
    intro u hu
    cases u using Fin.addCases with
    | left a =>
      dsimp only [z2, z1]; rw [Fin.append_left, Fin.append_left]
      rcases hsym : finProdFinEquiv.symm a with ⟨idx, j⟩
      have ha_eq : a = finProdFinEquiv (idx, j) := by rw [← hsym, finProdFinEquiv.apply_symm_apply]
      have ha_flat : ∀ arr : Fin (n + n) → Qubits w,
          flatReg (n + n) w arr a = arr idx j := fun arr => by
        change arr (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2 = arr idx j
        rw [hsym]
      rw [ha_flat x2, ha_flat x1]
      cases idx using Fin.addCases with
      | left i =>
        have hne : i.1 ≠ k := by
          intro hik
          apply hu
          refine ⟨⟨1 + j.1, by have := j.isLt; omega⟩, ?_⟩
          rw [cswapLayerEmb_left]
          have ha_val : a.1 = i.1 * w + j.1 := by
            rw [ha_eq, finProdFinEquiv_val, Fin.val_castAdd]
          apply Fin.ext
          change k * w + j.1 = a.1
          rw [ha_val, hik]
        simp only [x2, x1, Fin.addCases_left]
        by_cases hlt : i.1 < k
        · rw [if_pos hlt, if_pos (by omega : i.1 < k + 1)]
        · rw [if_neg hlt, if_neg (by omega : ¬ i.1 < k + 1)]
      | right i =>
        have hne : i.1 ≠ k := by
          intro hik
          apply hu
          refine ⟨⟨1 + w + j.1, by have := j.isLt; omega⟩, ?_⟩
          rw [cswapLayerEmb_right]
          have ha_val : a.1 = (n + i.1) * w + j.1 := by
            rw [ha_eq, finProdFinEquiv_val, Fin.val_natAdd]
          apply Fin.ext
          change (n + k) * w + j.1 = a.1
          rw [ha_val, hik]
        simp only [x2, x1, Fin.addCases_right]
        by_cases hlt : i.1 < k
        · rw [if_pos hlt, if_pos (by omega : i.1 < k + 1)]
        · rw [if_neg hlt, if_neg (by omega : ¬ i.1 < k + 1)]
    | right b =>
      dsimp only [z2, z1]; rw [Fin.append_right, Fin.append_right]

noncomputable def routeLayerCircuit (n w : ℕ) : LayeredCircuit ((n + n) * w + n) :=
  routeLayerPrefix n w n le_rfl

lemma routeLayerCircuit_size (n w : ℕ) : (routeLayerCircuit n w).size = 7 * w * n :=
  routeLayerPrefix_size n w n le_rfl

lemma act_routeLayerCircuit_ket (n w : ℕ) (x : Fin (n + n) → Qubits w) (flags : Fin n → Bool) :
    act (routeLayerCircuit n w).unitary (ket (Fin.append (flatReg (n + n) w x) flags)) =
      ket (Fin.append (flatReg (n + n) w (routeLayer flags x)) flags) := by
  have h := act_routeLayerPrefix_ket n w n le_rfl x flags
  dsimp only at h
  have hx : (fun idx : Fin (n + n) => Fin.addCases
      (fun i => if i.1 < n then (if flags i then x (Fin.natAdd n i) else x (Fin.castAdd n i)) else x (Fin.castAdd n i))
      (fun i => if i.1 < n then (if flags i then x (Fin.castAdd n i) else x (Fin.natAdd n i)) else x (Fin.natAdd n i))
      idx) = routeLayer flags x := by
    funext idx
    cases idx using Fin.addCases with
    | left i => simp [routeLayer]
    | right i => dsimp only [routeLayer]; rw [Fin.addCases_right, Fin.append_right, if_pos i.isLt]
  rw [hx] at h
  exact h

/-! #### General Data-Trace-Ancilla Recursive Embeddings -/


private lemma packDTA_anc_zero {N w T : ℕ} (arr : Fin N → Qubits w) (tr : Qubits T) :
    packDTA54 N w T 0 arr tr = Fin.append (flatReg N w arr) tr := by
  funext u; exact padZero_castAdd (N * w + T) 0 _ u

private def embCast {a b c : ℕ} (e : Fin a ↪ Fin b) (h : b = c) : Fin a ↪ Fin c :=
  e.trans ⟨fun i => ⟨i.1, h ▸ i.isLt⟩, fun _ _ hab => Fin.ext (by
    have := congrArg Fin.val hab; exact this)⟩

private lemma act_embCast_ket {a b c : ℕ} (e : Fin a ↪ Fin b) (h : b = c)
    (lc : LayeredCircuit a) (x y : Qubits b) (x' y' : Qubits c)
    (hx : ∀ i : Fin c, x' i = x ⟨i.1, h.symm ▸ i.isLt⟩)
    (hy : ∀ i : Fin c, y' i = y ⟨i.1, h.symm ▸ i.isLt⟩)
    (hact : act (lc.mapWires e).unitary (ket x) = ket y) :
    act (lc.mapWires (embCast e h)).unitary (ket x') = ket y' := by
  subst h
  have hx_eq : x' = x := funext hx
  have hy_eq : y' = y := funext hy
  have he : embCast e rfl = e := by ext i; rfl
  rw [hx_eq, hy_eq, he]
  exact hact

private lemma packDTA_cast_eq {N₁ N₂ w T : ℕ} (hN : N₁ = N₂) (hM : ((N₁ * w + T) + 0) = N₂ * w + T)
    (arr₁ : Fin N₁ → Qubits w) (arr₂ : Fin N₂ → Qubits w)
    (harr : ∀ j : Fin N₁, arr₁ j = arr₂ ⟨j.1, hN ▸ j.isLt⟩)
    (tr : Qubits T) (i : Fin (N₂ * w + T)) :
    Fin.append (flatReg N₂ w arr₂) tr i = packDTA54 N₁ w T 0 arr₁ tr ⟨i.1, hM.symm ▸ i.isLt⟩ := by
  subst hN
  have h1 : arr₁ = arr₂ := funext harr
  subst h1; simp only [packDTA_anc_zero]; rfl

private lemma packDTA_split_arr {n₁ w T n₂ : ℕ} (hN : n₁ + n₁ = n₂)
    (hM : ((n₁ + n₁) * w + T) + 0 = n₂ * w + T)
    (arr : Fin n₂ → Qubits w) (arrSplit : Fin (n₁ + n₁) → Qubits w)
    (harr : ∀ j : Fin (n₁ + n₁), arrSplit j = arr ⟨j.1, hN ▸ j.isLt⟩)
    (tr : Qubits T) (i : Fin (n₂ * w + T)) :
    Fin.append (flatReg n₂ w arr) tr i =
      packDTA54 (n₁ + n₁) w T 0
        (Fin.append (fun j => arrSplit (Fin.castAdd n₁ j)) (fun j => arrSplit (Fin.natAdd n₁ j)))
        tr ⟨i.1, hM.symm ▸ i.isLt⟩ := by
  have happ : Fin.append (fun j => arrSplit (Fin.castAdd n₁ j)) (fun j => arrSplit (Fin.natAdd n₁ j)) =
      arrSplit := fin_append_castAdd_natAdd
  rw [happ]
  exact packDTA_cast_eq hN hM arrSplit arr harr tr i

private def subTraceDTAEmb (D T_skip T_sub T_tot anc : ℕ) (h : T_skip + T_sub ≤ T_tot) :
    Fin ((D + T_sub) + anc) ↪ Fin ((D + T_tot) + anc) where
  toFun u :=
    if h1 : u.1 < D then ⟨u.1, by omega⟩
    else if h2 : u.1 < D + T_sub then ⟨D + T_skip + (u.1 - D), by omega⟩
    else ⟨D + T_tot + (u.1 - (D + T_sub)), by have := u.isLt; omega⟩
  inj' a b hab := by
    have ha := a.isLt; have hb := b.isLt
    dsimp only at hab
    have hv := congrArg Fin.val hab
    split_ifs at hv <;> simp only at hv <;> exact Fin.ext (by omega)

private lemma subTraceDTAEmb_apply (D T_skip T_sub T_tot anc : ℕ) (h : T_skip + T_sub ≤ T_tot)
    (u : Fin ((D + T_sub) + anc)) :
    subTraceDTAEmb D T_skip T_sub T_tot anc h u =
      if h1 : u.1 < D then ⟨u.1, by omega⟩
      else if h2 : u.1 < D + T_sub then ⟨D + T_skip + (u.1 - D), by omega⟩
      else ⟨D + T_tot + (u.1 - (D + T_sub)), by have := u.isLt; omega⟩ := rfl

private def leftHalfDTAEmb (n w T_skip T_sub T_tot anc : ℕ) (h : T_skip + T_sub ≤ T_tot) :
    Fin ((n * w + T_sub) + anc) ↪ Fin (((n + n) * w + T_tot) + anc) where
  toFun u :=
    have hmul : n * w ≤ (n + n) * w := by rw [Nat.add_mul]; omega
    if h1 : u.1 < n * w then ⟨u.1, by omega⟩
    else if h2 : u.1 < n * w + T_sub then ⟨(n + n) * w + T_skip + (u.1 - n * w), by omega⟩
    else ⟨(n + n) * w + T_tot + (u.1 - (n * w + T_sub)), by have := u.isLt; omega⟩
  inj' a b hab := by
    have ha := a.isLt; have hb := b.isLt
    have hmul : n * w ≤ (n + n) * w := by rw [Nat.add_mul]; omega
    dsimp only at hab
    have hv := congrArg Fin.val hab
    split_ifs at hv <;> simp only at hv <;> exact Fin.ext (by omega)

private lemma leftHalfDTAEmb_apply (n w T_skip T_sub T_tot anc : ℕ) (h : T_skip + T_sub ≤ T_tot)
    (u : Fin ((n * w + T_sub) + anc)) :
    leftHalfDTAEmb n w T_skip T_sub T_tot anc h u =
      if h1 : u.1 < n * w then ⟨u.1, by have hmul : n * w ≤ (n + n) * w := (by rw [Nat.add_mul]; omega); omega⟩
      else if h2 : u.1 < n * w + T_sub then ⟨(n + n) * w + T_skip + (u.1 - n * w), by omega⟩
      else ⟨(n + n) * w + T_tot + (u.1 - (n * w + T_sub)), by have := u.isLt; omega⟩ := rfl

private def rightHalfDTAEmb (n w T_skip T_sub T_tot anc : ℕ) (h : T_skip + T_sub ≤ T_tot) :
    Fin ((n * w + T_sub) + anc) ↪ Fin (((n + n) * w + T_tot) + anc) where
  toFun u :=
    have hmul : n * w + n * w = (n + n) * w := (Nat.add_mul n n w).symm
    if h1 : u.1 < n * w then ⟨n * w + u.1, by omega⟩
    else if h2 : u.1 < n * w + T_sub then ⟨(n + n) * w + T_skip + (u.1 - n * w), by omega⟩
    else ⟨(n + n) * w + T_tot + (u.1 - (n * w + T_sub)), by have := u.isLt; omega⟩
  inj' a b hab := by
    have ha := a.isLt; have hb := b.isLt
    have hmul : n * w + n * w = (n + n) * w := (Nat.add_mul n n w).symm
    dsimp only at hab
    have hv := congrArg Fin.val hab
    split_ifs at hv <;> simp only at hv <;> exact Fin.ext (by omega)

private lemma rightHalfDTAEmb_apply (n w T_skip T_sub T_tot anc : ℕ) (h : T_skip + T_sub ≤ T_tot)
    (u : Fin ((n * w + T_sub) + anc)) :
    rightHalfDTAEmb n w T_skip T_sub T_tot anc h u =
      if h1 : u.1 < n * w then ⟨n * w + u.1, by have hmul : n * w + n * w = (n + n) * w := (Nat.add_mul n n w).symm; omega⟩
      else if h2 : u.1 < n * w + T_sub then ⟨(n + n) * w + T_skip + (u.1 - n * w), by omega⟩
      else ⟨(n + n) * w + T_tot + (u.1 - (n * w + T_sub)), by have := u.isLt; omega⟩ := rfl

private lemma flatReg_cast_left {n₁ n₂ w : ℕ} (x : Fin (n₁ + n₂) → Qubits w) (i : Fin (n₁ * w)) :
    flatReg (n₁ + n₂) w x ⟨i.1, by have := i.isLt; rw [Nat.add_mul]; omega⟩ =
      flatReg n₁ w (fun j => x (Fin.castAdd n₂ j)) i := by
  rcases hsym : finProdFinEquiv.symm i with ⟨a, b⟩
  have hi_eq : i = finProdFinEquiv (a, b) := by rw [← hsym, finProdFinEquiv.apply_symm_apply]
  have hi_val : i.1 = a.1 * w + b.1 := by rw [hi_eq]; exact finProdFinEquiv_val a b
  have hL : (⟨i.1, by have := i.isLt; rw [Nat.add_mul]; omega⟩ : Fin ((n₁ + n₂) * w)) =
      finProdFinEquiv (Fin.castAdd n₂ a, b) := by
    ext; rw [finProdFinEquiv_val]; simp [hi_val]
  rw [hL, flatReg, finProdFinEquiv.symm_apply_apply]
  simp only [flatReg, hsym]

private lemma flatReg_cast_right {n₁ n₂ w : ℕ} (x : Fin (n₁ + n₂) → Qubits w) (i : Fin (n₂ * w)) :
    flatReg (n₁ + n₂) w x ⟨n₁ * w + i.1, by have := i.isLt; rw [Nat.add_mul]; omega⟩ =
      flatReg n₂ w (fun j => x (Fin.natAdd n₁ j)) i := by
  rcases hsym : finProdFinEquiv.symm i with ⟨a, b⟩
  have hi_eq : i = finProdFinEquiv (a, b) := by rw [← hsym, finProdFinEquiv.apply_symm_apply]
  have hi_val : i.1 = a.1 * w + b.1 := by rw [hi_eq]; exact finProdFinEquiv_val a b
  have hR : (⟨n₁ * w + i.1, by have := i.isLt; rw [Nat.add_mul]; omega⟩ : Fin ((n₁ + n₂) * w)) =
      finProdFinEquiv (Fin.natAdd n₁ a, b) := by
    ext; rw [finProdFinEquiv_val]; simp [hi_val, Nat.add_mul]; omega
  rw [hR, flatReg, finProdFinEquiv.symm_apply_apply]
  simp only [flatReg, hsym]

private lemma act_subTraceDTAEmb_ket {N w T_skip T_sub T_tot anc : ℕ} (h : T_skip + T_sub ≤ T_tot)
    (lc : LayeredCircuit ((N * w + T_sub) + anc))
    (arr arr' : Fin N → Qubits w) (tr tr' : Qubits T_tot)
    (hact : act lc.unitary (ket (packDTA54 N w T_sub anc arr (fun j => tr ⟨T_skip + j.1, by omega⟩))) =
      ket (packDTA54 N w T_sub anc arr' (fun j => tr' ⟨T_skip + j.1, by omega⟩)))
    (htr_out : ∀ k : Fin T_tot, (k.1 < T_skip ∨ T_skip + T_sub ≤ k.1) → tr' k = tr k) :
    act (lc.mapWires (subTraceDTAEmb (N * w) T_skip T_sub T_tot anc h)).unitary
        (ket (packDTA54 N w T_tot anc arr tr)) =
      ket (packDTA54 N w T_tot anc arr' tr') := by
  let emb := subTraceDTAEmb (N * w) T_skip T_sub T_tot anc h
  have hcomp : ∀ (A : Fin N → Qubits w) (T : Qubits T_tot),
      packDTA54 N w T_tot anc A T ∘ emb =
        packDTA54 N w T_sub anc A (fun j => T ⟨T_skip + j.1, by omega⟩) := by
    intro A T; funext u
    dsimp only [Function.comp_apply, emb, packDTA54]
    rw [subTraceDTAEmb_apply]
    by_cases h1 : u.1 < N * w
    · rw [dif_pos h1]
      have hl : (⟨u.1, by omega⟩ : Fin ((N * w + T_tot) + anc)) =
          Fin.castAdd anc (Fin.castAdd T_tot ⟨u.1, h1⟩) := Fin.ext rfl
      have hr : u = Fin.castAdd anc (Fin.castAdd T_sub ⟨u.1, h1⟩) := Fin.ext rfl
      rw [hl, padZero_castAdd, Fin.append_left]; conv_rhs => rw [hr]
      rw [padZero_castAdd, Fin.append_left]
    · by_cases h2 : u.1 < N * w + T_sub
      · rw [dif_neg h1, dif_pos h2]
        have hl : (⟨N * w + T_skip + (u.1 - N * w), by omega⟩ : Fin ((N * w + T_tot) + anc)) =
            Fin.castAdd anc (Fin.natAdd (N * w) ⟨T_skip + (u.1 - N * w), by omega⟩) := by
          ext; simp; omega
        have hr : u = Fin.castAdd anc (Fin.natAdd (N * w) ⟨u.1 - N * w, by omega⟩) := by
          ext; simp; omega
        rw [hl, padZero_castAdd, Fin.append_right]; conv_rhs => rw [hr]
        rw [padZero_castAdd, Fin.append_right]
      · rw [dif_neg h1, dif_neg h2]
        have hl : (⟨N * w + T_tot + (u.1 - (N * w + T_sub)), by have := u.isLt; omega⟩ :
            Fin ((N * w + T_tot) + anc)) =
            Fin.natAdd (N * w + T_tot) ⟨u.1 - (N * w + T_sub), by have := u.isLt; omega⟩ :=
          Fin.ext rfl
        have hr : u = Fin.natAdd (N * w + T_sub) ⟨u.1 - (N * w + T_sub), by have := u.isLt; omega⟩ := by
          ext; simp; omega
        rw [hl, padZero_natAdd]; conv_rhs => rw [hr]
        rw [padZero_natAdd]
  refine act_mapWires_ket lc emb (packDTA54 N w T_tot anc arr tr)
    (packDTA54 N w T_sub anc arr' (fun j => tr' ⟨T_skip + j.1, by omega⟩))
    (by rw [hcomp arr tr]; exact hact) (packDTA54 N w T_tot anc arr' tr') (hcomp arr' tr') ?_
  intro u hu
  cases u using Fin.addCases with
  | left a =>
    cases a using Fin.addCases with
    | left d =>
      exfalso; apply hu
      refine ⟨Fin.castAdd anc (Fin.castAdd T_sub d), Fin.ext ?_⟩
      dsimp only [emb]; rw [subTraceDTAEmb_apply, dif_pos (by simp only [Fin.val_castAdd]; exact d.isLt)]
      rfl
    | right t =>
      have htout : t.1 < T_skip ∨ T_skip + T_sub ≤ t.1 := by
        by_contra hc
        apply hu
        refine ⟨Fin.castAdd anc (Fin.natAdd (N * w) ⟨t.1 - T_skip, by omega⟩), Fin.ext ?_⟩
        dsimp only [emb]; rw [subTraceDTAEmb_apply]
        rw [dif_neg (by simp only [Fin.val_castAdd, Fin.val_natAdd]; omega),
            dif_pos (by simp only [Fin.val_castAdd, Fin.val_natAdd]; omega)]
        simp only [Fin.val_castAdd, Fin.val_natAdd]; omega
      simp only [packDTA54, padZero_castAdd, Fin.append_right, htr_out t htout]
  | right b =>
    simp only [packDTA54, padZero_natAdd]

private lemma act_leftHalfDTAEmb_ket {n w T_skip T_sub T_tot anc : ℕ} (h : T_skip + T_sub ≤ T_tot)
    (lc : LayeredCircuit ((n * w + T_sub) + anc))
    (arrL arrL' : Fin n → Qubits w) (arrR : Fin n → Qubits w) (tr tr' : Qubits T_tot)
    (hact : act lc.unitary (ket (packDTA54 n w T_sub anc arrL (fun j => tr ⟨T_skip + j.1, by omega⟩))) =
      ket (packDTA54 n w T_sub anc arrL' (fun j => tr' ⟨T_skip + j.1, by omega⟩)))
    (htr_out : ∀ k : Fin T_tot, (k.1 < T_skip ∨ T_skip + T_sub ≤ k.1) → tr' k = tr k) :
    act (lc.mapWires (leftHalfDTAEmb n w T_skip T_sub T_tot anc h)).unitary
        (ket (packDTA54 (n + n) w T_tot anc (Fin.append arrL arrR) tr)) =
      ket (packDTA54 (n + n) w T_tot anc (Fin.append arrL' arrR) tr') := by
  let emb := leftHalfDTAEmb n w T_skip T_sub T_tot anc h
  have hcomp : ∀ (AL : Fin n → Qubits w) (T : Qubits T_tot),
      packDTA54 (n + n) w T_tot anc (Fin.append AL arrR) T ∘ emb =
        packDTA54 n w T_sub anc AL (fun j => T ⟨T_skip + j.1, by omega⟩) := by
    intro AL T; funext u
    dsimp only [Function.comp_apply, emb, packDTA54]
    rw [leftHalfDTAEmb_apply]
    by_cases h1 : u.1 < n * w
    · rw [dif_pos h1]
      have hl : (⟨u.1, by rw [Nat.add_mul]; omega⟩ : Fin (((n + n) * w + T_tot) + anc)) =
          Fin.castAdd anc (Fin.castAdd T_tot ⟨u.1, by rw [Nat.add_mul]; omega⟩) := Fin.ext rfl
      have hr : u = Fin.castAdd anc (Fin.castAdd T_sub ⟨u.1, h1⟩) := Fin.ext rfl
      rw [hl, padZero_castAdd, Fin.append_left, flatReg_cast_left (x := Fin.append AL arrR) ⟨u.1, h1⟩]
      conv_rhs => rw [hr]; rw [padZero_castAdd, Fin.append_left]
      have hsub : (fun j : Fin n => Fin.append AL arrR (Fin.castAdd n j)) = AL := by
        funext j; exact Fin.append_left AL arrR j
      rw [hsub]
    · by_cases h2 : u.1 < n * w + T_sub
      · rw [dif_neg h1, dif_pos h2]
        have hl : (⟨(n + n) * w + T_skip + (u.1 - n * w), by omega⟩ :
            Fin (((n + n) * w + T_tot) + anc)) =
            Fin.castAdd anc (Fin.natAdd ((n + n) * w) ⟨T_skip + (u.1 - n * w), by omega⟩) := by
          ext; simp; omega
        have hr : u = Fin.castAdd anc (Fin.natAdd (n * w) ⟨u.1 - n * w, by omega⟩) := by
          ext; simp; omega
        rw [hl, padZero_castAdd, Fin.append_right]; conv_rhs => rw [hr]
        rw [padZero_castAdd, Fin.append_right]
      · rw [dif_neg h1, dif_neg h2]
        have hl : (⟨(n + n) * w + T_tot + (u.1 - (n * w + T_sub)), by have := u.isLt; omega⟩ :
            Fin (((n + n) * w + T_tot) + anc)) =
            Fin.natAdd ((n + n) * w + T_tot) ⟨u.1 - (n * w + T_sub), by have := u.isLt; omega⟩ :=
          Fin.ext rfl
        have hr : u = Fin.natAdd (n * w + T_sub) ⟨u.1 - (n * w + T_sub), by have := u.isLt; omega⟩ := by
          ext; simp; omega
        rw [hl, padZero_natAdd]; conv_rhs => rw [hr]
        rw [padZero_natAdd]
  refine act_mapWires_ket lc emb (packDTA54 (n + n) w T_tot anc (Fin.append arrL arrR) tr)
    (packDTA54 n w T_sub anc arrL' (fun j => tr' ⟨T_skip + j.1, by omega⟩))
    (by rw [hcomp arrL tr]; exact hact)
    (packDTA54 (n + n) w T_tot anc (Fin.append arrL' arrR) tr') (hcomp arrL' tr') ?_
  intro u hu
  cases u using Fin.addCases with
  | left a =>
    cases a using Fin.addCases with
    | left d =>
      simp only [packDTA54, padZero_castAdd, Fin.append_left]
      rcases hsym : finProdFinEquiv.symm d with ⟨idx, j⟩
      have hd_eq : d = finProdFinEquiv (idx, j) := by rw [← hsym, finProdFinEquiv.apply_symm_apply]
      have hd_flat : ∀ arr : Fin (n + n) → Qubits w,
          flatReg (n + n) w arr d = arr idx j := fun arr => by
        change arr (finProdFinEquiv.symm d).1 (finProdFinEquiv.symm d).2 = arr idx j
        rw [hsym]
      rw [hd_flat, hd_flat]
      cases idx using Fin.addCases with
      | left i =>
        exfalso; apply hu
        have hlt : d.1 < n * w := by
          have := fin_prod_lt i j
          have hd_val : d.1 = i.1 * w + j.1 := by rw [hd_eq]; exact finProdFinEquiv_val _ _
          omega
        refine ⟨Fin.castAdd anc (Fin.castAdd T_sub ⟨d.1, hlt⟩), Fin.ext ?_⟩
        dsimp only [emb]; rw [leftHalfDTAEmb_apply, dif_pos (by simp only [Fin.val_castAdd]; exact hlt)]
        rfl
      | right i => rw [Fin.append_right, Fin.append_right]
    | right t =>
      have htout : t.1 < T_skip ∨ T_skip + T_sub ≤ t.1 := by
        by_contra hc
        apply hu
        refine ⟨Fin.castAdd anc (Fin.natAdd (n * w) ⟨t.1 - T_skip, by omega⟩), Fin.ext ?_⟩
        dsimp only [emb]; rw [leftHalfDTAEmb_apply]
        rw [dif_neg (by simp only [Fin.val_castAdd, Fin.val_natAdd]; omega),
            dif_pos (by simp only [Fin.val_castAdd, Fin.val_natAdd]; omega)]
        simp only [Fin.val_castAdd, Fin.val_natAdd]; omega
      simp only [packDTA54, padZero_castAdd, Fin.append_right, htr_out t htout]
  | right b =>
    simp only [packDTA54, padZero_natAdd]

private lemma act_rightHalfDTAEmb_ket {n w T_skip T_sub T_tot anc : ℕ} (h : T_skip + T_sub ≤ T_tot)
    (lc : LayeredCircuit ((n * w + T_sub) + anc))
    (arrL : Fin n → Qubits w) (arrR arrR' : Fin n → Qubits w) (tr tr' : Qubits T_tot)
    (hact : act lc.unitary (ket (packDTA54 n w T_sub anc arrR (fun j => tr ⟨T_skip + j.1, by omega⟩))) =
      ket (packDTA54 n w T_sub anc arrR' (fun j => tr' ⟨T_skip + j.1, by omega⟩)))
    (htr_out : ∀ k : Fin T_tot, (k.1 < T_skip ∨ T_skip + T_sub ≤ k.1) → tr' k = tr k) :
    act (lc.mapWires (rightHalfDTAEmb n w T_skip T_sub T_tot anc h)).unitary
        (ket (packDTA54 (n + n) w T_tot anc (Fin.append arrL arrR) tr)) =
      ket (packDTA54 (n + n) w T_tot anc (Fin.append arrL arrR') tr') := by
  let emb := rightHalfDTAEmb n w T_skip T_sub T_tot anc h
  have hcomp : ∀ (AR : Fin n → Qubits w) (T : Qubits T_tot),
      packDTA54 (n + n) w T_tot anc (Fin.append arrL AR) T ∘ emb =
        packDTA54 n w T_sub anc AR (fun j => T ⟨T_skip + j.1, by omega⟩) := by
    intro AR T; funext u
    dsimp only [Function.comp_apply, emb, packDTA54]
    rw [rightHalfDTAEmb_apply]
    by_cases h1 : u.1 < n * w
    · rw [dif_pos h1]
      have hl : (⟨n * w + u.1, by rw [Nat.add_mul]; omega⟩ : Fin (((n + n) * w + T_tot) + anc)) =
          Fin.castAdd anc (Fin.castAdd T_tot ⟨n * w + u.1, by rw [Nat.add_mul]; omega⟩) := Fin.ext rfl
      have hr : u = Fin.castAdd anc (Fin.castAdd T_sub ⟨u.1, h1⟩) := Fin.ext rfl
      rw [hl, padZero_castAdd, Fin.append_left, flatReg_cast_right (x := Fin.append arrL AR) ⟨u.1, h1⟩]
      conv_rhs => rw [hr]; rw [padZero_castAdd, Fin.append_left]
      have hsub : (fun j : Fin n => Fin.append arrL AR (Fin.natAdd n j)) = AR := by
        funext j; exact Fin.append_right arrL AR j
      rw [hsub]
    · by_cases h2 : u.1 < n * w + T_sub
      · rw [dif_neg h1, dif_pos h2]
        have hl : (⟨(n + n) * w + T_skip + (u.1 - n * w), by omega⟩ :
            Fin (((n + n) * w + T_tot) + anc)) =
            Fin.castAdd anc (Fin.natAdd ((n + n) * w) ⟨T_skip + (u.1 - n * w), by omega⟩) := by
          ext; simp; omega
        have hr : u = Fin.castAdd anc (Fin.natAdd (n * w) ⟨u.1 - n * w, by omega⟩) := by
          ext; simp; omega
        rw [hl, padZero_castAdd, Fin.append_right]; conv_rhs => rw [hr]
        rw [padZero_castAdd, Fin.append_right]
      · rw [dif_neg h1, dif_neg h2]
        have hl : (⟨(n + n) * w + T_tot + (u.1 - (n * w + T_sub)), by have := u.isLt; omega⟩ :
            Fin (((n + n) * w + T_tot) + anc)) =
            Fin.natAdd ((n + n) * w + T_tot) ⟨u.1 - (n * w + T_sub), by have := u.isLt; omega⟩ :=
          Fin.ext rfl
        have hr : u = Fin.natAdd (n * w + T_sub) ⟨u.1 - (n * w + T_sub), by have := u.isLt; omega⟩ := by
          ext; simp; omega
        rw [hl, padZero_natAdd]; conv_rhs => rw [hr]
        rw [padZero_natAdd]
  refine act_mapWires_ket lc emb (packDTA54 (n + n) w T_tot anc (Fin.append arrL arrR) tr)
    (packDTA54 n w T_sub anc arrR' (fun j => tr' ⟨T_skip + j.1, by omega⟩))
    (by rw [hcomp arrR tr]; exact hact)
    (packDTA54 (n + n) w T_tot anc (Fin.append arrL arrR') tr') (hcomp arrR' tr') ?_
  intro u hu
  cases u using Fin.addCases with
  | left a =>
    cases a using Fin.addCases with
    | left d =>
      simp only [packDTA54, padZero_castAdd, Fin.append_left]
      rcases hsym : finProdFinEquiv.symm d with ⟨idx, j⟩
      have hd_eq : d = finProdFinEquiv (idx, j) := by rw [← hsym, finProdFinEquiv.apply_symm_apply]
      have hd_flat : ∀ arr : Fin (n + n) → Qubits w,
          flatReg (n + n) w arr d = arr idx j := fun arr => by
        change arr (finProdFinEquiv.symm d).1 (finProdFinEquiv.symm d).2 = arr idx j
        rw [hsym]
      rw [hd_flat, hd_flat]
      cases idx using Fin.addCases with
      | left i => simp [Fin.append_left]
      | right i =>
        exfalso; apply hu
        have hlt : i.1 * w + j.1 < n * w := fin_prod_lt i j
        have hd_val : d.1 = n * w + (i.1 * w + j.1) := by
          rw [hd_eq]
          have hv := finProdFinEquiv_val (Fin.natAdd n i) j
          simp only [Fin.val_natAdd, Nat.add_mul] at hv
          linarith
        refine ⟨Fin.castAdd anc (Fin.castAdd T_sub ⟨i.1 * w + j.1, hlt⟩), Fin.ext ?_⟩
        dsimp only [emb]; rw [rightHalfDTAEmb_apply, dif_pos (by simp only [Fin.val_castAdd]; exact hlt)]
        simp only [Fin.val_castAdd, hd_val]
    | right t =>
      have htout : t.1 < T_skip ∨ T_skip + T_sub ≤ t.1 := by
        by_contra hc
        apply hu
        refine ⟨Fin.castAdd anc (Fin.natAdd (n * w) ⟨t.1 - T_skip, by omega⟩), Fin.ext ?_⟩
        dsimp only [emb]; rw [rightHalfDTAEmb_apply]
        rw [dif_neg (by simp only [Fin.val_castAdd, Fin.val_natAdd]; omega),
            dif_pos (by simp only [Fin.val_castAdd, Fin.val_natAdd]; omega)]
        simp only [Fin.val_castAdd, Fin.val_natAdd]; omega
      simp only [packDTA54, padZero_castAdd, Fin.append_right, htr_out t htout]
  | right b =>
    simp only [packDTA54, padZero_natAdd]

noncomputable def routeMergeCircuit : (d w : ℕ) → LayeredCircuit (arity d * w + mergeTraceSize d)
  | 0, _ => LayeredCircuit.id _
  | d + 1, w =>
    have hM : (((arity d + arity d) * w + mergeTraceSize (d + 1)) + 0) =
        arity (d + 1) * w + mergeTraceSize (d + 1) := by simp only [arity, Nat.add_zero]
    let step := (routeLayerCircuit (arity d) w).mapWires
      (embCast (subTraceDTAEmb ((arity d + arity d) * w) 0 (arity d) (mergeTraceSize (d + 1)) 0
        (by dsimp [mergeTraceSize]; omega)) hM)
    let left := (routeMergeCircuit d w).mapWires
      (embCast (leftHalfDTAEmb (arity d) w (arity d) (mergeTraceSize d) (mergeTraceSize (d + 1)) 0
        (by dsimp [mergeTraceSize]; omega)) hM)
    let right := (routeMergeCircuit d w).mapWires
      (embCast (rightHalfDTAEmb (arity d) w (arity d + mergeTraceSize d) (mergeTraceSize d)
        (mergeTraceSize (d + 1)) 0 (by dsimp [mergeTraceSize]; omega)) hM)
    step.seq (left.seq right)

lemma routeMergeCircuit_size (d w : ℕ) :
    (routeMergeCircuit d w).size = 7 * w * mergeTraceSize d := by
  induction d with
  | zero => simp [routeMergeCircuit, mergeTraceSize]
  | succ d ih =>
    dsimp only [routeMergeCircuit]
    simp only [LayeredCircuit.seq_size, LayeredCircuit.mapWires_size,
      routeLayerCircuit_size, ih, mergeTraceSize]
    ring

lemma act_routeMergeCircuit_ket (d w : ℕ) (x : Fin (arity d) → Qubits w)
    (flags : Fin (mergeTraceSize d) → Bool) :
    act (routeMergeCircuit d w).unitary (ket (Fin.append (flatReg (arity d) w x) flags)) =
      ket (Fin.append (flatReg (arity d) w (routeMerge d flags x)) flags) := by
  induction d with
  | zero => simp [routeMergeCircuit, routeMerge, LayeredCircuit.id_unitary, act_one]
  | succ d ih =>
    have hN : arity d + arity d = arity (d + 1) := rfl
    have hM : (((arity d + arity d) * w + mergeTraceSize (d + 1)) + 0) =
        arity (d + 1) * w + mergeTraceSize (d + 1) := by simp only [arity, Nat.add_zero]
    let fLayer : Fin (arity d) → Bool := flags ∘ Fin.castAdd (mergeTraceSize d + mergeTraceSize d)
    let fCh := flags ∘ Fin.natAdd (arity d)
    let fL := fCh ∘ Fin.castAdd (mergeTraceSize d)
    let fR := fCh ∘ Fin.natAdd (mergeTraceSize d)
    let x0 : Fin (arity d + arity d) → Qubits w := x
    let compared : Fin (arity d + arity d) → Qubits w := routeLayer fLayer x0
    let xL := routeMerge d fL (compared ∘ Fin.castAdd (arity d))
    let xR := routeMerge d fR (compared ∘ Fin.natAdd (arity d))
    let z0 : Qubits (arity (d + 1) * w + mergeTraceSize (d + 1)) :=
      Fin.append (flatReg (arity (d + 1)) w x) flags
    let z1 : Qubits (arity (d + 1) * w + mergeTraceSize (d + 1)) :=
      Fin.append (flatReg (arity (d + 1)) w compared) flags
    let z2 : Qubits (arity (d + 1) * w + mergeTraceSize (d + 1)) :=
      Fin.append (flatReg (arity (d + 1)) w (Fin.append xL (compared ∘ Fin.natAdd (arity d)))) flags
    let z3 : Qubits (arity (d + 1) * w + mergeTraceSize (d + 1)) :=
      Fin.append (flatReg (arity (d + 1)) w (Fin.append xL xR)) flags
    have hstep : act ((routeLayerCircuit (arity d) w).mapWires
        (embCast (subTraceDTAEmb ((arity d + arity d) * w) 0 (arity d) (mergeTraceSize (d + 1)) 0
          (by dsimp [mergeTraceSize]; omega)) hM)).unitary (ket z0) = ket z1 := by
      refine act_embCast_ket _ hM (routeLayerCircuit (arity d) w)
        (packDTA54 (arity d + arity d) w (mergeTraceSize (d + 1)) 0 x0 flags)
        (packDTA54 (arity d + arity d) w (mergeTraceSize (d + 1)) 0 compared flags)
        z0 z1 (packDTA_cast_eq hN hM x0 x (fun _ => rfl) flags)
        (packDTA_cast_eq hN hM compared compared (fun _ => rfl) flags) ?_
      refine act_subTraceDTAEmb_ket _ _ x0 compared flags flags ?_ (fun _ _ => rfl)
      simp only [packDTA_anc_zero]
      have hslice : (fun j : Fin (arity d) => flags ⟨0 + j.1, by dsimp [mergeTraceSize]; omega⟩) =
          fLayer := by funext j; apply congrArg flags; apply Fin.ext; simp
      rw [hslice]
      exact act_routeLayerCircuit_ket (arity d) w x0 fLayer
    have hleft : act ((routeMergeCircuit d w).mapWires
        (embCast (leftHalfDTAEmb (arity d) w (arity d) (mergeTraceSize d) (mergeTraceSize (d + 1)) 0
          (by dsimp [mergeTraceSize]; omega)) hM)).unitary (ket z1) = ket z2 := by
      refine act_embCast_ket _ hM (routeMergeCircuit d w)
        (packDTA54 (arity d + arity d) w (mergeTraceSize (d + 1)) 0
          (Fin.append (compared ∘ Fin.castAdd (arity d)) (compared ∘ Fin.natAdd (arity d))) flags)
        (packDTA54 (arity d + arity d) w (mergeTraceSize (d + 1)) 0
          (Fin.append xL (compared ∘ Fin.natAdd (arity d))) flags)
        z1 z2
        (packDTA_split_arr hN hM compared compared (fun _ => rfl) flags)
        (packDTA_cast_eq hN hM _ _ (fun _ => rfl) flags) ?_
      refine act_leftHalfDTAEmb_ket _ _ (compared ∘ Fin.castAdd (arity d)) xL
        (compared ∘ Fin.natAdd (arity d)) flags flags ?_ (fun _ _ => rfl)
      simp only [packDTA_anc_zero]
      exact ih (compared ∘ Fin.castAdd (arity d)) fL
    have hright : act ((routeMergeCircuit d w).mapWires
        (embCast (rightHalfDTAEmb (arity d) w (arity d + mergeTraceSize d) (mergeTraceSize d)
          (mergeTraceSize (d + 1)) 0 (by dsimp [mergeTraceSize]; omega)) hM)).unitary
        (ket z2) = ket z3 := by
      refine act_embCast_ket _ hM (routeMergeCircuit d w)
        (packDTA54 (arity d + arity d) w (mergeTraceSize (d + 1)) 0
          (Fin.append xL (compared ∘ Fin.natAdd (arity d))) flags)
        (packDTA54 (arity d + arity d) w (mergeTraceSize (d + 1)) 0 (Fin.append xL xR) flags)
        z2 z3
        (packDTA_cast_eq hN hM _ _ (fun _ => rfl) flags)
        (packDTA_cast_eq hN hM _ _ (fun _ => rfl) flags) ?_
      refine act_rightHalfDTAEmb_ket _ _ xL (compared ∘ Fin.natAdd (arity d)) xR flags flags ?_
        (fun _ _ => rfl)
      simp only [packDTA_anc_zero]
      have hslice : (fun j : Fin (mergeTraceSize d) =>
          flags ⟨arity d + mergeTraceSize d + j.1, by dsimp [mergeTraceSize]; omega⟩) = fR := by
        funext j; apply congrArg flags; apply Fin.ext
        change arity d + mergeTraceSize d + j.1 = arity d + (mergeTraceSize d + j.1); omega
      rw [hslice]
      exact ih (compared ∘ Fin.natAdd (arity d)) fR
    dsimp only [routeMergeCircuit]
    rw [LayeredCircuit.seq_unitary, LayeredCircuit.seq_unitary, act_mul, act_mul]
    change act _ (act _ (act _ (ket z0))) = ket z3
    rw [hstep, hleft, hright]

noncomputable def routeSortCircuit : (d w : ℕ) → LayeredCircuit (arity d * w + sortTraceSize d)
  | 0, _ => LayeredCircuit.id _
  | d + 1, w =>
    have hM : (((arity d + arity d) * w + sortTraceSize (d + 1)) + 0) =
        arity (d + 1) * w + sortTraceSize (d + 1) := by simp only [arity, Nat.add_zero]
    have hM2 : (arity (d + 1) * w + sortTraceSize (d + 1) + 0) =
        arity (d + 1) * w + sortTraceSize (d + 1) := by simp only [Nat.add_zero]
    let left := (routeSortCircuit d w).mapWires
      (embCast (leftHalfDTAEmb (arity d) w 0 (sortTraceSize d) (sortTraceSize (d + 1)) 0
        (by dsimp [sortTraceSize]; omega)) hM)
    let right := (routeSortCircuit d w).mapWires
      (embCast (rightHalfDTAEmb (arity d) w (sortTraceSize d) (sortTraceSize d) (sortTraceSize (d + 1)) 0
        (by dsimp [sortTraceSize]; omega)) hM)
    let merge := (routeMergeCircuit (d + 1) w).mapWires
      (embCast (subTraceDTAEmb (arity (d + 1) * w) (sortTraceSize d + sortTraceSize d)
        (mergeTraceSize (d + 1)) (sortTraceSize (d + 1)) 0
        (by dsimp [sortTraceSize]; omega)) hM2)
    left.seq (right.seq merge)

lemma routeSortCircuit_size (d w : ℕ) :
    (routeSortCircuit d w).size = 7 * w * sortTraceSize d := by
  induction d with
  | zero => simp [routeSortCircuit, sortTraceSize]
  | succ d ih =>
    dsimp only [routeSortCircuit]
    simp only [LayeredCircuit.seq_size, LayeredCircuit.mapWires_size,
      routeMergeCircuit_size, ih, sortTraceSize]
    ring

lemma act_routeSortCircuit_ket (d w : ℕ) (x : Fin (arity d) → Qubits w)
    (flags : Fin (sortTraceSize d) → Bool) :
    act (routeSortCircuit d w).unitary (ket (Fin.append (flatReg (arity d) w x) flags)) =
      ket (Fin.append (flatReg (arity d) w (routeSort d flags x)) flags) := by
  induction d with
  | zero => simp [routeSortCircuit, routeSort, LayeredCircuit.id_unitary, act_one]
  | succ d ih =>
    have hN : arity d + arity d = arity (d + 1) := rfl
    have hM : (((arity d + arity d) * w + sortTraceSize (d + 1)) + 0) =
        arity (d + 1) * w + sortTraceSize (d + 1) := by simp only [arity, Nat.add_zero]
    have hM2 : (arity (d + 1) * w + sortTraceSize (d + 1) + 0) =
        arity (d + 1) * w + sortTraceSize (d + 1) := by simp only [Nat.add_zero]
    let fCh := flags ∘ Fin.castAdd (mergeTraceSize (d + 1))
    let fL := fCh ∘ Fin.castAdd (sortTraceSize d)
    let fR := fCh ∘ Fin.natAdd (sortTraceSize d)
    let fM := flags ∘ Fin.natAdd (sortTraceSize d + sortTraceSize d)
    let xL := routeSort d fL (x ∘ Fin.castAdd (arity d))
    let xR := routeSort d fR (x ∘ Fin.natAdd (arity d))
    let xLR : Fin (arity (d + 1)) → Qubits w := Fin.append xL xR
    let z0 : Qubits (arity (d + 1) * w + sortTraceSize (d + 1)) :=
      Fin.append (flatReg (arity (d + 1)) w x) flags
    let z1 : Qubits (arity (d + 1) * w + sortTraceSize (d + 1)) :=
      Fin.append (flatReg (arity (d + 1)) w (Fin.append xL (x ∘ Fin.natAdd (arity d)))) flags
    let z2 : Qubits (arity (d + 1) * w + sortTraceSize (d + 1)) :=
      Fin.append (flatReg (arity (d + 1)) w xLR) flags
    let z3 : Qubits (arity (d + 1) * w + sortTraceSize (d + 1)) :=
      Fin.append (flatReg (arity (d + 1)) w (routeMerge (d + 1) fM xLR)) flags
    have hleft : act ((routeSortCircuit d w).mapWires
        (embCast (leftHalfDTAEmb (arity d) w 0 (sortTraceSize d) (sortTraceSize (d + 1)) 0
          (by dsimp [sortTraceSize]; omega)) hM)).unitary (ket z0) = ket z1 := by
      refine act_embCast_ket _ hM (routeSortCircuit d w)
        (packDTA54 (arity d + arity d) w (sortTraceSize (d + 1)) 0
          (Fin.append (x ∘ Fin.castAdd (arity d)) (x ∘ Fin.natAdd (arity d))) flags)
        (packDTA54 (arity d + arity d) w (sortTraceSize (d + 1)) 0
          (Fin.append xL (x ∘ Fin.natAdd (arity d))) flags)
        z0 z1
        (packDTA_split_arr hN hM x x (fun _ => rfl) flags)
        (packDTA_cast_eq hN hM _ _ (fun _ => rfl) flags) ?_
      refine act_leftHalfDTAEmb_ket _ _ (x ∘ Fin.castAdd (arity d)) xL
        (x ∘ Fin.natAdd (arity d)) flags flags ?_ (fun _ _ => rfl)
      simp only [packDTA_anc_zero]
      have hslice : (fun j : Fin (sortTraceSize d) =>
          flags ⟨0 + j.1, by dsimp [sortTraceSize]; omega⟩) = fL := by
        funext j; apply congrArg flags; apply Fin.ext; simp
      rw [hslice]
      exact ih (x ∘ Fin.castAdd (arity d)) fL
    have hright : act ((routeSortCircuit d w).mapWires
        (embCast (rightHalfDTAEmb (arity d) w (sortTraceSize d) (sortTraceSize d)
          (sortTraceSize (d + 1)) 0 (by dsimp [sortTraceSize]; omega)) hM)).unitary (ket z1) =
        ket z2 := by
      refine act_embCast_ket _ hM (routeSortCircuit d w)
        (packDTA54 (arity d + arity d) w (sortTraceSize (d + 1)) 0
          (Fin.append xL (x ∘ Fin.natAdd (arity d))) flags)
        (packDTA54 (arity d + arity d) w (sortTraceSize (d + 1)) 0 (Fin.append xL xR) flags)
        z1 z2
        (packDTA_cast_eq hN hM _ _ (fun _ => rfl) flags)
        (packDTA_cast_eq hN hM _ xLR (fun _ => rfl) flags) ?_
      refine act_rightHalfDTAEmb_ket _ _ xL (x ∘ Fin.natAdd (arity d)) xR flags flags ?_
        (fun _ _ => rfl)
      simp only [packDTA_anc_zero]
      exact ih (x ∘ Fin.natAdd (arity d)) fR
    have hmerge : act ((routeMergeCircuit (d + 1) w).mapWires
        (embCast (subTraceDTAEmb (arity (d + 1) * w) (sortTraceSize d + sortTraceSize d)
          (mergeTraceSize (d + 1)) (sortTraceSize (d + 1)) 0
          (by dsimp [sortTraceSize]; omega)) hM2)).unitary (ket z2) = ket z3 := by
      refine act_embCast_ket _ hM2 (routeMergeCircuit (d + 1) w)
        (packDTA54 (arity (d + 1)) w (sortTraceSize (d + 1)) 0 xLR flags)
        (packDTA54 (arity (d + 1)) w (sortTraceSize (d + 1)) 0 (routeMerge (d + 1) fM xLR) flags)
        z2 z3
        (packDTA_cast_eq rfl hM2 xLR xLR (fun _ => rfl) flags)
        (packDTA_cast_eq rfl hM2 _ _ (fun _ => rfl) flags) ?_
      refine act_subTraceDTAEmb_ket _ _ xLR (routeMerge (d + 1) fM xLR) flags flags ?_
        (fun _ _ => rfl)
      simp only [packDTA_anc_zero]
      have hslice : (fun j : Fin (mergeTraceSize (d + 1)) =>
          flags ⟨sortTraceSize d + sortTraceSize d + j.1, by dsimp [sortTraceSize]; omega⟩) = fM := by
        funext j; apply congrArg flags; apply Fin.ext; rfl
      rw [hslice]
      exact act_routeMergeCircuit_ket (d + 1) w xLR fM
    dsimp only [routeSortCircuit]
    rw [LayeredCircuit.seq_unitary, LayeredCircuit.seq_unitary, act_mul, act_mul]
    change act _ (act _ (act _ (ket z0))) = ket z3
    rw [hleft, hright, hmerge]

noncomputable def unrouteSortCircuit (d w : ℕ) : LayeredCircuit (arity d * w + sortTraceSize d) :=
  (routeSortCircuit d w).adj

lemma unrouteSortCircuit_size (d w : ℕ) :
    (unrouteSortCircuit d w).size = 7 * w * sortTraceSize d := by
  simp [unrouteSortCircuit, routeSortCircuit_size]

lemma act_unrouteSortCircuit_ket (d w : ℕ) (x : Fin (arity d) → Qubits w)
    (flags : Fin (sortTraceSize d) → Bool) :
    act (unrouteSortCircuit d w).unitary (ket (Fin.append (flatReg (arity d) w x) flags)) =
      ket (Fin.append (flatReg (arity d) w (unrouteSort d flags x)) flags) := by
  have hf := act_routeSortCircuit_ket d w (unrouteSort d flags x) flags
  rw [routeSort_unrouteSort] at hf
  rw [unrouteSortCircuit, ← hf, ← act_mul, LayeredCircuit.adj_unitary,
    Matrix.mem_unitaryGroup_iff'.mp (routeSortCircuit d w).unitary_mem_unitaryGroup, act_one]

private lemma fin_comp_append_54 {α β : Type} {n m : ℕ} (g : α → β)
    (u : Fin n → α) (v : Fin m → α) :
    g ∘ Fin.append u v = Fin.append (g ∘ u) (g ∘ v) := by
  funext i
  cases i using Fin.addCases with
  | left _ => simp
  | right _ => simp

private lemma layerFlags_comp_key {κ α β : Type} [LinearOrder κ] (key0 : β → κ) (f : α → β)
    {n : ℕ} (asc : Bool) (x : Fin (n + n) → α) :
    layerFlags (key0 ∘ f) asc x = layerFlags key0 asc (f ∘ x) := rfl

private lemma routeLayer_comp_54 {α β : Type} {n : ℕ} (flags : Fin n → Bool) (f : α → β)
    (x : Fin (n + n) → α) : routeLayer flags (f ∘ x) = f ∘ routeLayer flags x := by
  funext i
  cases i using Fin.addCases <;>
    simp only [routeLayer, Function.comp_apply, Fin.append_left, Fin.append_right] <;>
    split_ifs <;> rfl

private lemma compareLayer_comp_key {κ α β : Type} [LinearOrder κ] (key0 : β → κ) (f : α → β)
    {n : ℕ} (asc : Bool) (x : Fin (n + n) → α) :
    f ∘ compareLayer (key0 ∘ f) asc x = compareLayer key0 asc (f ∘ x) := by
  rw [← routeLayer_layerFlags, ← routeLayer_comp_54, layerFlags_comp_key, routeLayer_layerFlags]

private lemma mergeTrace_of_key_comp {κ α β : Type} [LinearOrder κ] (key0 : β → κ) (f : α → β)
    (d : ℕ) (asc : Bool) (x : Fin (arity d) → α) :
    mergeTrace (key0 ∘ f) d asc x = mergeTrace key0 d asc (f ∘ x) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    dsimp only [arity] at x
    have hc : f ∘ compareLayer (key0 ∘ f) asc x = compareLayer key0 asc (f ∘ x) :=
      compareLayer_comp_key key0 f asc x
    change Fin.append (layerFlags (key0 ∘ f) asc x)
        (Fin.append
          (mergeTrace (key0 ∘ f) d asc (compareLayer (key0 ∘ f) asc x ∘ Fin.castAdd (arity d)))
          (mergeTrace (key0 ∘ f) d asc (compareLayer (key0 ∘ f) asc x ∘ Fin.natAdd (arity d)))) =
      Fin.append (layerFlags key0 asc (f ∘ x))
        (Fin.append
          (mergeTrace key0 d asc (compareLayer key0 asc (f ∘ x) ∘ Fin.castAdd (arity d)))
          (mergeTrace key0 d asc (compareLayer key0 asc (f ∘ x) ∘ Fin.natAdd (arity d))))
    rw [layerFlags_comp_key, ih, ih, ← Function.comp_assoc, ← Function.comp_assoc, hc]

private lemma merge_of_key_comp {κ α β : Type} [LinearOrder κ] (key0 : β → κ) (f : α → β)
    (d : ℕ) (asc : Bool) (x : Fin (arity d) → α) :
    f ∘ merge (key0 ∘ f) d asc x = merge key0 d asc (f ∘ x) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    dsimp only [arity] at x
    have hc : f ∘ compareLayer (key0 ∘ f) asc x = compareLayer key0 asc (f ∘ x) :=
      compareLayer_comp_key key0 f asc x
    change f ∘ Fin.append
        (merge (key0 ∘ f) d asc (compareLayer (key0 ∘ f) asc x ∘ Fin.castAdd (arity d)))
        (merge (key0 ∘ f) d asc (compareLayer (key0 ∘ f) asc x ∘ Fin.natAdd (arity d))) =
      Fin.append
        (merge key0 d asc (compareLayer key0 asc (f ∘ x) ∘ Fin.castAdd (arity d)))
        (merge key0 d asc (compareLayer key0 asc (f ∘ x) ∘ Fin.natAdd (arity d)))
    rw [fin_comp_append_54, ih, ih, ← Function.comp_assoc, ← Function.comp_assoc, hc]

lemma sort_of_key_comp {κ α β : Type} [LinearOrder κ] (key0 : β → κ) (f : α → β)
    (d : ℕ) (asc : Bool) (x : Fin (arity d) → α) :
    f ∘ sort (key0 ∘ f) d asc x = sort key0 d asc (f ∘ x) := by
  induction d generalizing asc with
  | zero => rfl
  | succ d ih =>
    dsimp only [arity] at x
    change f ∘ merge (key0 ∘ f) (d + 1) asc
        (Fin.append
          (sort (key0 ∘ f) d true (x ∘ Fin.castAdd (arity d)))
          (sort (key0 ∘ f) d false (x ∘ Fin.natAdd (arity d)))) =
      merge key0 (d + 1) asc
        (Fin.append
          (sort key0 d true ((f ∘ x) ∘ Fin.castAdd (arity d)))
          (sort key0 d false ((f ∘ x) ∘ Fin.natAdd (arity d))))
    erw [merge_of_key_comp, fin_comp_append_54, ih true _, ih false _]
    rfl

lemma sortTrace_of_key_comp {κ α β : Type} [LinearOrder κ] (key0 : β → κ) (f : α → β)
    (d : ℕ) (asc : Bool) (x : Fin (arity d) → α) :
    sortTrace (key0 ∘ f) d asc x = sortTrace key0 d asc (f ∘ x) := by
  induction d generalizing asc with
  | zero => rfl
  | succ d ih =>
    dsimp only [arity] at x
    change Fin.append
        (Fin.append
          (sortTrace (key0 ∘ f) d true (x ∘ Fin.castAdd (arity d)))
          (sortTrace (key0 ∘ f) d false (x ∘ Fin.natAdd (arity d))))
        (mergeTrace (key0 ∘ f) (d + 1) asc
          (Fin.append
            (sort (key0 ∘ f) d true (x ∘ Fin.castAdd (arity d)))
            (sort (key0 ∘ f) d false (x ∘ Fin.natAdd (arity d))))) =
      Fin.append
        (Fin.append
          (sortTrace key0 d true ((f ∘ x) ∘ Fin.castAdd (arity d)))
          (sortTrace key0 d false ((f ∘ x) ∘ Fin.natAdd (arity d))))
        (mergeTrace key0 (d + 1) asc
          (Fin.append
            (sort key0 d true ((f ∘ x) ∘ Fin.castAdd (arity d)))
            (sort key0 d false ((f ∘ x) ∘ Fin.natAdd (arity d)))))
    have hsL := sort_of_key_comp key0 f d true (x ∘ Fin.castAdd (arity d))
    have hsR := sort_of_key_comp key0 f d false (x ∘ Fin.natAdd (arity d))
    erw [ih true _, ih false _, mergeTrace_of_key_comp, fin_comp_append_54, hsL, hsR]
    rfl

private lemma packDTA_cast_eq_gen {N₁ N₂ w T anc : ℕ} (hN : N₁ = N₂)
    (hM : ((N₁ * w + T) + anc) = (N₂ * w + T) + anc)
    (arr₁ : Fin N₁ → Qubits w) (arr₂ : Fin N₂ → Qubits w)
    (harr : ∀ j : Fin N₁, arr₁ j = arr₂ ⟨j.1, hN ▸ j.isLt⟩)
    (tr : Qubits T) (i : Fin ((N₂ * w + T) + anc)) :
    packDTA54 N₂ w T anc arr₂ tr i = packDTA54 N₁ w T anc arr₁ tr ⟨i.1, hM.symm ▸ i.isLt⟩ := by
  subst hN
  have h1 : arr₁ = arr₂ := funext harr
  subst h1; rfl

private lemma packDTA_split_arr_gen {n₁ w T anc n₂ : ℕ} (hN : n₁ + n₁ = n₂)
    (hM : ((n₁ + n₁) * w + T) + anc = (n₂ * w + T) + anc)
    (arr : Fin n₂ → Qubits w) (arrSplit : Fin (n₁ + n₁) → Qubits w)
    (harr : ∀ j : Fin (n₁ + n₁), arrSplit j = arr ⟨j.1, hN ▸ j.isLt⟩)
    (tr : Qubits T) (i : Fin ((n₂ * w + T) + anc)) :
    packDTA54 n₂ w T anc arr tr i =
      packDTA54 (n₁ + n₁) w T anc
        (Fin.append (fun j => arrSplit (Fin.castAdd n₁ j)) (fun j => arrSplit (Fin.natAdd n₁ j)))
        tr ⟨i.1, hM.symm ▸ i.isLt⟩ := by
  have happ : Fin.append (fun j => arrSplit (Fin.castAdd n₁ j)) (fun j => arrSplit (Fin.natAdd n₁ j)) =
      arrSplit := fin_append_castAdd_natAdd
  rw [happ]
  exact packDTA_cast_eq_gen hN hM arrSplit arr harr tr i

private def cmpLayerEmb (n w_r anc_cmp : ℕ) (i : Fin n) :
    Fin ((w_r + w_r + 1) + anc_cmp) ↪ Fin (((n + n) * w_r + n) + anc_cmp) where
  toFun u :=
    if h1 : u.1 < w_r then
      ⟨(n + i.1) * w_r + u.1, by
        have hlt := fin_prod_lt (Fin.natAdd n i) (⟨u.1, h1⟩ : Fin w_r)
        change (n + i.1) * w_r + u.1 < (n + n) * w_r at hlt; omega⟩
    else if h2 : u.1 < w_r + w_r then
      ⟨i.1 * w_r + (u.1 - w_r), by
        have hlt := fin_prod_lt (Fin.castAdd n i) (⟨u.1 - w_r, by omega⟩ : Fin w_r)
        change i.1 * w_r + (u.1 - w_r) < (n + n) * w_r at hlt; omega⟩
    else if h3 : u.1 = w_r + w_r then
      ⟨(n + n) * w_r + i.1, by have := i.isLt; omega⟩
    else
      ⟨(n + n) * w_r + n + (u.1 - (w_r + w_r + 1)), by have := u.isLt; omega⟩
  inj' a b hab := by
    have ha := a.isLt; have hb := b.isLt; have hi := i.isLt
    have hni1 : i.1 * w_r + w_r ≤ n * w_r := by
      have h1 : i.1 * w_r + w_r = (i.1 + 1) * w_r := by ring
      rw [h1]; exact Nat.mul_le_mul_right w_r hi
    have hni2 : n * w_r ≤ (n + i.1) * w_r := by rw [Nat.add_mul]; omega
    have hni3 : (n + i.1) * w_r + w_r ≤ (n + n) * w_r := by
      rw [Nat.add_mul, Nat.add_mul]
      have h1 : i.1 * w_r + w_r ≤ n * w_r := by
        have h2 : i.1 * w_r + w_r = (i.1 + 1) * w_r := by ring
        rw [h2]; exact Nat.mul_le_mul_right w_r hi
      omega
    have hv := congrArg Fin.val hab
    dsimp only at hv
    by_cases ha1 : a.1 < w_r <;> by_cases hb1 : b.1 < w_r
    · rw [dif_pos ha1, dif_pos hb1] at hv; simp only at hv; exact Fin.ext (by omega)
    · by_cases hb2 : b.1 < w_r + w_r
      · rw [dif_pos ha1, dif_neg hb1, dif_pos hb2] at hv; simp only at hv; omega
      · by_cases hb3 : b.1 = w_r + w_r
        · rw [dif_pos ha1, dif_neg hb1, dif_neg hb2, dif_pos hb3] at hv; simp only at hv; omega
        · rw [dif_pos ha1, dif_neg hb1, dif_neg hb2, dif_neg hb3] at hv; simp only at hv; omega
    · by_cases ha2 : a.1 < w_r + w_r
      · rw [dif_neg ha1, dif_pos ha2, dif_pos hb1] at hv; simp only at hv; omega
      · by_cases ha3 : a.1 = w_r + w_r
        · rw [dif_neg ha1, dif_neg ha2, dif_pos ha3, dif_pos hb1] at hv; simp only at hv; omega
        · rw [dif_neg ha1, dif_neg ha2, dif_neg ha3, dif_pos hb1] at hv; simp only at hv; omega
    · by_cases ha2 : a.1 < w_r + w_r <;> by_cases hb2 : b.1 < w_r + w_r
      · rw [dif_neg ha1, dif_pos ha2, dif_neg hb1, dif_pos hb2] at hv; simp only at hv; exact Fin.ext (by omega)
      · by_cases hb3 : b.1 = w_r + w_r
        · rw [dif_neg ha1, dif_pos ha2, dif_neg hb1, dif_neg hb2, dif_pos hb3] at hv; simp only at hv; omega
        · rw [dif_neg ha1, dif_pos ha2, dif_neg hb1, dif_neg hb2, dif_neg hb3] at hv; simp only at hv; omega
      · by_cases ha3 : a.1 = w_r + w_r
        · rw [dif_neg ha1, dif_neg ha2, dif_pos ha3, dif_neg hb1, dif_pos hb2] at hv; simp only at hv; omega
        · rw [dif_neg ha1, dif_neg ha2, dif_neg ha3, dif_neg hb1, dif_pos hb2] at hv; simp only at hv; omega
      · by_cases ha3 : a.1 = w_r + w_r <;> by_cases hb3 : b.1 = w_r + w_r
        · exact Fin.ext (by omega)
        · rw [dif_neg ha1, dif_neg ha2, dif_pos ha3, dif_neg hb1, dif_neg hb2, dif_neg hb3] at hv
          simp only at hv; omega
        · rw [dif_neg ha1, dif_neg ha2, dif_neg ha3, dif_neg hb1, dif_neg hb2, dif_pos hb3] at hv
          simp only at hv; omega
        · rw [dif_neg ha1, dif_neg ha2, dif_neg ha3, dif_neg hb1, dif_neg hb2, dif_neg hb3] at hv
          simp only at hv; exact Fin.ext (by omega)

private lemma cmpLayerEmb_apply (n w_r anc_cmp : ℕ) (i : Fin n)
    (u : Fin ((w_r + w_r + 1) + anc_cmp)) :
    cmpLayerEmb n w_r anc_cmp i u =
      if h1 : u.1 < w_r then
        ⟨(n + i.1) * w_r + u.1, by
          have hlt := fin_prod_lt (Fin.natAdd n i) (⟨u.1, h1⟩ : Fin w_r)
          change (n + i.1) * w_r + u.1 < (n + n) * w_r at hlt; omega⟩
      else if h2 : u.1 < w_r + w_r then
        ⟨i.1 * w_r + (u.1 - w_r), by
          have hlt := fin_prod_lt (Fin.castAdd n i) (⟨u.1 - w_r, by omega⟩ : Fin w_r)
          change i.1 * w_r + (u.1 - w_r) < (n + n) * w_r at hlt; omega⟩
      else if h3 : u.1 = w_r + w_r then
        ⟨(n + n) * w_r + i.1, by have := i.isLt; omega⟩
      else
        ⟨(n + n) * w_r + n + (u.1 - (w_r + w_r + 1)), by have := u.isLt; omega⟩ := rfl

private lemma cmpLayerEmb_left (n w_r anc_cmp : ℕ) (i : Fin n)
    (u : Fin ((w_r + w_r + 1) + anc_cmp)) (hu : u.1 < w_r) :
    cmpLayerEmb n w_r anc_cmp i u =
      ⟨(n + i.1) * w_r + u.1, by
        have hlt := fin_prod_lt (Fin.natAdd n i) (⟨u.1, hu⟩ : Fin w_r)
        change (n + i.1) * w_r + u.1 < (n + n) * w_r at hlt; omega⟩ := by
  rw [cmpLayerEmb_apply, dif_pos hu]

private lemma cmpLayerEmb_right (n w_r anc_cmp : ℕ) (i : Fin n)
    (u : Fin ((w_r + w_r + 1) + anc_cmp)) (hu1 : ¬ u.1 < w_r) (hu2 : u.1 < w_r + w_r) :
    cmpLayerEmb n w_r anc_cmp i u =
      ⟨i.1 * w_r + (u.1 - w_r), by
        have hlt := fin_prod_lt (Fin.castAdd n i) (⟨u.1 - w_r, by omega⟩ : Fin w_r)
        change i.1 * w_r + (u.1 - w_r) < (n + n) * w_r at hlt; omega⟩ := by
  rw [cmpLayerEmb_apply, dif_neg hu1, dif_pos hu2]

private lemma cmpLayerEmb_flag (n w_r anc_cmp : ℕ) (i : Fin n)
    (u : Fin ((w_r + w_r + 1) + anc_cmp)) (hu : u.1 = w_r + w_r) :
    cmpLayerEmb n w_r anc_cmp i u =
      ⟨(n + n) * w_r + i.1, by have := i.isLt; omega⟩ := by
  rw [cmpLayerEmb_apply, dif_neg (by omega), dif_neg (by omega), dif_pos hu]

private lemma cmpLayerEmb_anc (n w_r anc_cmp : ℕ) (i : Fin n)
    (u : Fin ((w_r + w_r + 1) + anc_cmp)) (hu : w_r + w_r + 1 ≤ u.1) :
    cmpLayerEmb n w_r anc_cmp i u =
      ⟨(n + n) * w_r + n + (u.1 - (w_r + w_r + 1)), by have := u.isLt; omega⟩ := by
  rw [cmpLayerEmb_apply, dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]

private noncomputable def cmpLayerPrefix (n w_r anc_cmp : ℕ)
    (cmp : LayeredCircuit ((w_r + w_r + 1) + anc_cmp)) (asc : Bool) :
    (k : ℕ) → k ≤ n → LayeredCircuit (((n + n) * w_r + n) + anc_cmp)
  | 0, _ => LayeredCircuit.id _
  | k + 1, hk =>
    let step0 := cmp.mapWires (cmpLayerEmb n w_r anc_cmp ⟨k, hk⟩)
    let step := if asc then step0
      else step0.seq (pauliXGate ⟨(n + n) * w_r + k, by omega⟩)
    (cmpLayerPrefix n w_r anc_cmp cmp asc k (by omega)).seq step

private lemma cmpLayerPrefix_size (n w_r anc_cmp : ℕ)
    (cmp : LayeredCircuit ((w_r + w_r + 1) + anc_cmp)) (asc : Bool) (k : ℕ) (hk : k ≤ n) :
    (cmpLayerPrefix n w_r anc_cmp cmp asc k hk).size ≤ k * (cmp.size + 1) := by
  induction k with
  | zero => simp [cmpLayerPrefix]
  | succ k ih =>
    dsimp only [cmpLayerPrefix]
    simp only [LayeredCircuit.seq_size]
    have hstep : (if asc then cmp.mapWires (cmpLayerEmb n w_r anc_cmp ⟨k, hk⟩)
        else (cmp.mapWires (cmpLayerEmb n w_r anc_cmp ⟨k, hk⟩)).seq
          (pauliXGate ⟨(n + n) * w_r + k, by omega⟩)).size ≤ cmp.size + 1 := by
      cases asc <;> simp [LayeredCircuit.mapWires_size]
    have hih := ih (by omega)
    nlinarith

private lemma act_cmpLayerPrefix_ket {κ : Type} [LinearOrder κ] (n w_r anc_cmp : ℕ)
    (key : Qubits w_r → κ) (cmp : LayeredCircuit ((w_r + w_r + 1) + anc_cmp))
    (hcmp : cmp.ImplementsOnClean (permMat (cmpLtFn54 w_r key)))
    (asc : Bool) (k : ℕ) (hk : k ≤ n) (x : Fin (n + n) → Qubits w_r) :
    let trK : Qubits n := fun j =>
      if j.1 < k then
        decide (if asc then key (x (Fin.natAdd n j)) < key (x (Fin.castAdd n j))
          else ¬ key (x (Fin.natAdd n j)) < key (x (Fin.castAdd n j)))
      else false
    act (cmpLayerPrefix n w_r anc_cmp cmp asc k hk).unitary
        (ket (packDTA54 (n + n) w_r n anc_cmp x (fun _ => false))) =
      ket (packDTA54 (n + n) w_r n anc_cmp x trK) := by
  induction k with
  | zero =>
    intro trK
    have htr : trK = fun _ => false := by funext j; simp [trK]
    rw [htr, cmpLayerPrefix, LayeredCircuit.id_unitary, act_one]
  | succ k ih =>
    intro trK
    let trPrev : Qubits n := fun j =>
      if j.1 < k then
        decide (if asc then key (x (Fin.natAdd n j)) < key (x (Fin.castAdd n j))
          else ¬ key (x (Fin.natAdd n j)) < key (x (Fin.castAdd n j)))
      else false
    let zPrev := packDTA54 (n + n) w_r n anc_cmp x trPrev
    let trMid : Qubits n := Function.update trPrev ⟨k, hk⟩
      (decide (key (x (Fin.natAdd n ⟨k, hk⟩)) < key (x (Fin.castAdd n ⟨k, hk⟩))))
    let zMid := packDTA54 (n + n) w_r n anc_cmp x trMid
    let zOut := packDTA54 (n + n) w_r n anc_cmp x trK
    let emb := cmpLayerEmb n w_r anc_cmp ⟨k, hk⟩
    let xPair : Qubits (w_r + w_r + 1) := fun u =>
      if h1 : u.1 < w_r then x (Fin.natAdd n ⟨k, hk⟩) ⟨u.1, h1⟩
      else if h2 : u.1 < w_r + w_r then x (Fin.castAdd n ⟨k, hk⟩) ⟨u.1 - w_r, by omega⟩
      else false
    have hcomp_in : zPrev ∘ emb = padZero (w_r + w_r + 1) anc_cmp xPair := by
      funext u
      dsimp only [Function.comp_apply, zPrev, emb, packDTA54, xPair]
      by_cases hu1 : u.1 < w_r
      · have hu_eq : u = Fin.castAdd anc_cmp ⟨u.1, by omega⟩ := Fin.ext rfl
        have hcomp_eq : emb u = Fin.castAdd anc_cmp (Fin.castAdd n
            (finProdFinEquiv (Fin.natAdd n ⟨k, hk⟩, (⟨u.1, hu1⟩ : Fin w_r)))) := by
          change cmpLayerEmb n w_r anc_cmp ⟨k, hk⟩ u = _
          rw [cmpLayerEmb_left n w_r anc_cmp ⟨k, hk⟩ u hu1]
          ext; simp; ring
        rw [hcomp_eq, padZero_castAdd, Fin.append_left, flatReg,
          finProdFinEquiv.symm_apply_apply]
        conv_rhs => rw [hu_eq, padZero_castAdd]
        dsimp only [xPair]; rw [dif_pos hu1]
      · by_cases hu2 : u.1 < w_r + w_r
        · have hu_eq : u = Fin.castAdd anc_cmp ⟨u.1, by omega⟩ := Fin.ext rfl
          have hcomp_eq : emb u = Fin.castAdd anc_cmp (Fin.castAdd n
                (finProdFinEquiv (Fin.castAdd n ⟨k, hk⟩, (⟨u.1 - w_r, by omega⟩ : Fin w_r)))) := by
            change cmpLayerEmb n w_r anc_cmp ⟨k, hk⟩ u = _
            rw [cmpLayerEmb_right n w_r anc_cmp ⟨k, hk⟩ u hu1 hu2]
            ext; simp; ring
          rw [hcomp_eq, padZero_castAdd, Fin.append_left, flatReg,
            finProdFinEquiv.symm_apply_apply]
          conv_rhs => rw [hu_eq, padZero_castAdd]
          dsimp only [xPair]; rw [dif_neg hu1, dif_pos hu2]
        · by_cases hu3 : u.1 = w_r + w_r
          · have hu_eq : u = Fin.castAdd anc_cmp ⟨u.1, by omega⟩ := Fin.ext rfl
            have hcomp_eq : emb u = Fin.castAdd anc_cmp (Fin.natAdd ((n + n) * w_r) ⟨k, hk⟩) := by
              change cmpLayerEmb n w_r anc_cmp ⟨k, hk⟩ u = _
              rw [cmpLayerEmb_flag n w_r anc_cmp ⟨k, hk⟩ u hu3]; rfl
            rw [hcomp_eq, padZero_castAdd, Fin.append_right]
            conv_rhs => rw [hu_eq, padZero_castAdd]
            dsimp only [xPair]; rw [dif_neg hu1, dif_neg hu2]
            simp [trPrev]
          · have hu4 : w_r + w_r + 1 ≤ u.1 := by omega
            have hcomp_eq : emb u =
                Fin.natAdd ((n + n) * w_r + n) ⟨u.1 - (w_r + w_r + 1), by have := u.isLt; omega⟩ := by
              change cmpLayerEmb n w_r anc_cmp ⟨k, hk⟩ u = _
              rw [cmpLayerEmb_anc n w_r anc_cmp ⟨k, hk⟩ u hu4]; rfl
            have hu_eq : u =
                Fin.natAdd (w_r + w_r + 1) ⟨u.1 - (w_r + w_r + 1), by have := u.isLt; omega⟩ := by
              ext; simp; omega
            rw [hcomp_eq, padZero_natAdd]
            conv_rhs => rw [hu_eq, padZero_natAdd]
    have hcomp_out : zMid ∘ emb = padZero (w_r + w_r + 1) anc_cmp (cmpLtFn54 w_r key xPair) := by
      funext u
      dsimp only [Function.comp_apply, zMid, emb, packDTA54, cmpLtFn54]
      by_cases hu1 : u.1 < w_r
      · have hcomp_eq : emb u = Fin.castAdd anc_cmp (Fin.castAdd n
            (finProdFinEquiv (Fin.natAdd n ⟨k, hk⟩, (⟨u.1, hu1⟩ : Fin w_r)))) := by
          change cmpLayerEmb n w_r anc_cmp ⟨k, hk⟩ u = _
          rw [cmpLayerEmb_left n w_r anc_cmp ⟨k, hk⟩ u hu1]; ext; simp; ring
        have hu_cast : u = Fin.castAdd anc_cmp ⟨u.1, by omega⟩ := Fin.ext rfl
        rw [hcomp_eq, padZero_castAdd, Fin.append_left, flatReg,
          finProdFinEquiv.symm_apply_apply]
        conv_rhs => rw [hu_cast, padZero_castAdd,
          Function.update_of_ne (Fin.ne_of_val_ne (by dsimp; omega))]
        dsimp only [xPair]; rw [dif_pos hu1]
      · by_cases hu2 : u.1 < w_r + w_r
        · have hcomp_eq : emb u = Fin.castAdd anc_cmp (Fin.castAdd n
                (finProdFinEquiv (Fin.castAdd n ⟨k, hk⟩, (⟨u.1 - w_r, by omega⟩ : Fin w_r)))) := by
            change cmpLayerEmb n w_r anc_cmp ⟨k, hk⟩ u = _
            rw [cmpLayerEmb_right n w_r anc_cmp ⟨k, hk⟩ u hu1 hu2]; ext; simp; ring
          have hu_cast : u = Fin.castAdd anc_cmp ⟨u.1, by omega⟩ := Fin.ext rfl
          rw [hcomp_eq, padZero_castAdd, Fin.append_left, flatReg,
            finProdFinEquiv.symm_apply_apply]
          conv_rhs => rw [hu_cast, padZero_castAdd,
            Function.update_of_ne (Fin.ne_of_val_ne (by dsimp; omega))]
          dsimp only [xPair]; rw [dif_neg hu1, dif_pos hu2]
        · by_cases hu3 : u.1 = w_r + w_r
          · have hcast : (⟨w_r + w_r, by omega⟩ : Fin ((w_r + w_r + 1) + anc_cmp)) =
                Fin.castAdd anc_cmp ⟨w_r + w_r, by omega⟩ := Fin.ext rfl
            have hu_eq : u = Fin.castAdd anc_cmp ⟨w_r + w_r, by omega⟩ := Fin.ext hu3
            have hcomp_eq : emb u =
                Fin.castAdd anc_cmp (Fin.natAdd ((n + n) * w_r) ⟨k, hk⟩) := by
              change cmpLayerEmb n w_r anc_cmp ⟨k, hk⟩ u = _
              rw [cmpLayerEmb_flag n w_r anc_cmp ⟨k, hk⟩ u hu3]; rfl
            rw [hcomp_eq, padZero_castAdd, Fin.append_right]
            conv_rhs => rw [hu_eq, padZero_castAdd, Function.update_self]
            dsimp only [trMid]; rw [Function.update_self]
            have hx0 : xPair ⟨w_r + w_r, by omega⟩ = false := by
              dsimp only [xPair]; rw [dif_neg (by omega), dif_neg (by omega)]
            have ha_eq : (fun i : Fin w_r => xPair ⟨i.1, by omega⟩) = x (Fin.natAdd n ⟨k, hk⟩) := by
              funext j; dsimp only [xPair]; rw [dif_pos j.isLt]
            have hb_eq : (fun i : Fin w_r => xPair ⟨w_r + i.1, by omega⟩) = x (Fin.castAdd n ⟨k, hk⟩) := by
              funext j; dsimp only [xPair]; rw [dif_neg (by omega), dif_pos (by have := j.isLt; omega)]
              congr 1; apply Fin.ext; simp
            rw [hx0, Bool.false_xor, ha_eq, hb_eq]
          · have hu4 : w_r + w_r + 1 ≤ u.1 := by omega
            have hu_eq : u = Fin.natAdd (w_r + w_r + 1)
                ⟨u.1 - (w_r + w_r + 1), by have := u.isLt; omega⟩ := by
              ext; simp; omega
            have hcomp_eq : emb u =
                Fin.natAdd ((n + n) * w_r + n) ⟨u.1 - (w_r + w_r + 1), by have := u.isLt; omega⟩ := by
              change cmpLayerEmb n w_r anc_cmp ⟨k, hk⟩ u = _
              rw [cmpLayerEmb_anc n w_r anc_cmp ⟨k, hk⟩ u hu4]; rfl
            rw [hcomp_eq, padZero_natAdd]
            conv_rhs => rw [hu_eq, padZero_natAdd]
    have hact_cmp0 : act cmp.unitary (ket (zPrev ∘ emb)) =
        ket (padZero (w_r + w_r + 1) anc_cmp (cmpLtFn54 w_r key xPair)) := by
      rw [hcomp_in]
      exact act_ket_of_implementsOnClean_perm hcmp xPair
    have hmap_cmp : act (cmp.mapWires emb).unitary (ket zPrev) = ket zMid := by
      refine act_mapWires_ket cmp emb zPrev _ hact_cmp0 zMid hcomp_out ?_
      intro u hu
      cases u using Fin.addCases with
      | left d =>
        cases d using Fin.addCases with
        | left p =>
          dsimp only [zMid, zPrev, packDTA54]; rw [padZero_castAdd, padZero_castAdd, Fin.append_left, Fin.append_left]
        | right t =>
          have hne : t ≠ ⟨k, hk⟩ := by
            intro htk; subst htk; apply hu
            refine ⟨⟨w_r + w_r, by omega⟩, Fin.ext ?_⟩
            change (cmpLayerEmb n w_r anc_cmp ⟨k, hk⟩ ⟨w_r + w_r, by omega⟩).1 = _
            rw [cmpLayerEmb_flag n w_r anc_cmp ⟨k, hk⟩ ⟨w_r + w_r, by omega⟩ rfl]; rfl
          dsimp only [zMid, zPrev, packDTA54, trMid]
          rw [padZero_castAdd, padZero_castAdd, Fin.append_right, Fin.append_right,
            Function.update_of_ne hne]
      | right a =>
        dsimp only [zMid, zPrev, packDTA54]; rw [padZero_natAdd, padZero_natAdd]
    have hstep_full : act ((if asc then cmp.mapWires emb
        else (cmp.mapWires emb).seq (pauliXGate ⟨(n + n) * w_r + k, by omega⟩))).unitary (ket zPrev) =
        ket zOut := by
      cases asc
      · simp only [Bool.false_eq_true, ↓reduceIte, LayeredCircuit.seq_unitary, act_mul, hmap_cmp,
          act_pauliXGate_ket]
        congr 1; funext u
        by_cases hu : u = ⟨(n + n) * w_r + k, by omega⟩
        · subst hu
          rw [Function.update_self]
          have heq : (⟨(n + n) * w_r + k, by omega⟩ : Fin (((n + n) * w_r + n) + anc_cmp)) =
              Fin.castAdd anc_cmp (Fin.natAdd ((n + n) * w_r) ⟨k, hk⟩) := Fin.ext rfl
          dsimp only [zMid, zOut, packDTA54, trMid, trK]
          rw [heq, padZero_castAdd, Fin.append_right, padZero_castAdd, Fin.append_right,
            Function.update_self]
          simp only [Bool.false_eq_true, ↓reduceIte, if_pos (by simp : k < k + 1)]
          rw [← decide_not]
        · rw [Function.update_of_ne hu]
          cases u using Fin.addCases with
          | left d =>
            cases d using Fin.addCases with
            | left p => dsimp only [zMid, zOut, packDTA54]; rw [padZero_castAdd, padZero_castAdd, Fin.append_left, Fin.append_left]
            | right t =>
              have htk : t ≠ ⟨k, hk⟩ := fun h => hu (Fin.ext (by
                change (Fin.castAdd anc_cmp (Fin.natAdd ((n + n) * w_r) t)).1 = (n + n) * w_r + k
                simp [h]))
              have hne_val : t.1 ≠ k := fun h => htk (Fin.ext h)
              dsimp only [zMid, zOut, packDTA54, trMid, trK, trPrev]
              rw [padZero_castAdd, padZero_castAdd, Fin.append_right, Fin.append_right,
                Function.update_of_ne htk]
              by_cases hlt : t.1 < k
              · rw [if_pos hlt, if_pos (by omega : t.1 < k + 1)]
              · rw [if_neg hlt, if_neg (by omega : ¬ t.1 < k + 1)]
          | right a => dsimp only [zMid, zOut, packDTA54]; rw [padZero_natAdd, padZero_natAdd]
      · simp only [↓reduceIte, hmap_cmp]
        congr 1; funext u
        cases u using Fin.addCases with
        | left d =>
          cases d using Fin.addCases with
          | left p => dsimp only [zMid, zOut, packDTA54]; rw [padZero_castAdd, padZero_castAdd, Fin.append_left, Fin.append_left]
          | right t =>
            dsimp only [zMid, zOut, packDTA54, trMid, trK, trPrev]
            rw [padZero_castAdd, padZero_castAdd, Fin.append_right, Fin.append_right]
            by_cases htk : t = ⟨k, hk⟩
            · subst htk; rw [Function.update_self, if_pos (by simp : k < k + 1)]; rfl
            · have hne_val : t.1 ≠ k := fun h => htk (Fin.ext h)
              rw [Function.update_of_ne htk]
              by_cases hlt : t.1 < k
              · rw [if_pos hlt, if_pos (by omega : t.1 < k + 1)]
              · rw [if_neg hlt, if_neg (by omega : ¬ t.1 < k + 1)]
        | right a => dsimp only [zMid, zOut, packDTA54]; rw [padZero_natAdd, padZero_natAdd]
    dsimp only [cmpLayerPrefix]
    rw [LayeredCircuit.seq_unitary, act_mul]
    change act _ (act (cmpLayerPrefix n w_r anc_cmp cmp asc k _).unitary _) = _
    rw [ih (by omega), hstep_full]

private def castAddAncEmb (m anc : ℕ) : Fin m ↪ Fin (m + anc) :=
  ⟨Fin.castAdd anc, Fin.castAdd_injective m anc⟩

private lemma act_routeLayerCircuit_anc_ket (n w_r anc_cmp : ℕ)
    (x : Fin (n + n) → Qubits w_r) (flags : Fin n → Bool) :
    act ((routeLayerCircuit n w_r).mapWires (castAddAncEmb ((n + n) * w_r + n) anc_cmp)).unitary
        (ket (packDTA54 (n + n) w_r n anc_cmp x flags)) =
      ket (packDTA54 (n + n) w_r n anc_cmp (routeLayer flags x) flags) := by
  let emb := castAddAncEmb ((n + n) * w_r + n) anc_cmp
  have hcomp : ∀ arr : Fin (n + n) → Qubits w_r,
      packDTA54 (n + n) w_r n anc_cmp arr flags ∘ emb = Fin.append (flatReg (n + n) w_r arr) flags := by
    intro arr; funext u
    exact padZero_castAdd ((n + n) * w_r + n) anc_cmp (Fin.append (flatReg (n + n) w_r arr) flags) u
  refine act_mapWires_ket (routeLayerCircuit n w_r) emb _ _ ?_ _ (hcomp (routeLayer flags x)) ?_
  · rw [hcomp x]; exact act_routeLayerCircuit_ket n w_r x flags
  · intro u hu
    cases u using Fin.addCases with
    | left a => exfalso; exact hu ⟨a, rfl⟩
    | right b => dsimp only [packDTA54]; rw [padZero_natAdd, padZero_natAdd]

noncomputable def compareLayerWithTrace (n w_r anc_cmp : ℕ)
    (cmp : LayeredCircuit ((w_r + w_r + 1) + anc_cmp)) (asc : Bool) :
    LayeredCircuit (((n + n) * w_r + n) + anc_cmp) :=
  (cmpLayerPrefix n w_r anc_cmp cmp asc n le_rfl).seq
    ((routeLayerCircuit n w_r).mapWires (castAddAncEmb ((n + n) * w_r + n) anc_cmp))

lemma compareLayerWithTrace_size (n w_r anc_cmp : ℕ)
    (cmp : LayeredCircuit ((w_r + w_r + 1) + anc_cmp)) (asc : Bool) :
    (compareLayerWithTrace n w_r anc_cmp cmp asc).size ≤ n * (cmp.size + 7 * w_r + 1) := by
  dsimp only [compareLayerWithTrace]
  simp only [LayeredCircuit.seq_size, LayeredCircuit.mapWires_size, routeLayerCircuit_size]
  have h1 := cmpLayerPrefix_size n w_r anc_cmp cmp asc n le_rfl
  nlinarith

lemma act_compareLayerWithTrace_ket {κ : Type} [LinearOrder κ] (n w_r anc_cmp : ℕ)
    (key : Qubits w_r → κ) (cmp : LayeredCircuit ((w_r + w_r + 1) + anc_cmp))
    (hcmp : cmp.ImplementsOnClean (permMat (cmpLtFn54 w_r key)))
    (asc : Bool) (x : Fin (n + n) → Qubits w_r) :
    act (compareLayerWithTrace n w_r anc_cmp cmp asc).unitary
        (ket (packDTA54 (n + n) w_r n anc_cmp x (fun _ => false))) =
      ket (packDTA54 (n + n) w_r n anc_cmp (compareLayer key asc x) (layerFlags key asc x)) := by
  dsimp only [compareLayerWithTrace]
  rw [LayeredCircuit.seq_unitary, act_mul, act_cmpLayerPrefix_ket n w_r anc_cmp key cmp hcmp asc n le_rfl x]
  have htr_eq : (fun j : Fin n =>
      if j.1 < n then
        decide (if asc then key (x (Fin.natAdd n j)) < key (x (Fin.castAdd n j))
          else ¬ key (x (Fin.natAdd n j)) < key (x (Fin.castAdd n j)))
      else false) = layerFlags key asc x := by
    funext j; simp [j.isLt, layerFlags]
  rw [htr_eq, act_routeLayerCircuit_anc_ket, routeLayer_layerFlags]

noncomputable def mergeWithTraceGen :
    (d w_r anc_cmp : ℕ) → LayeredCircuit ((w_r + w_r + 1) + anc_cmp) → Bool →
      LayeredCircuit ((arity d * w_r + mergeTraceSize d) + anc_cmp)
  | 0, _, _, _, _ => LayeredCircuit.id _
  | d + 1, w_r, anc_cmp, cmp, asc =>
    have hM : (((arity d + arity d) * w_r + mergeTraceSize (d + 1)) + anc_cmp) =
        (arity (d + 1) * w_r + mergeTraceSize (d + 1)) + anc_cmp := rfl
    let step := (compareLayerWithTrace (arity d) w_r anc_cmp cmp asc).mapWires
      (embCast (subTraceDTAEmb ((arity d + arity d) * w_r) 0 (arity d) (mergeTraceSize (d + 1)) anc_cmp
        (by dsimp [mergeTraceSize]; omega)) hM)
    let left := (mergeWithTraceGen d w_r anc_cmp cmp asc).mapWires
      (embCast (leftHalfDTAEmb (arity d) w_r (arity d) (mergeTraceSize d) (mergeTraceSize (d + 1)) anc_cmp
        (by dsimp [mergeTraceSize]; omega)) hM)
    let right := (mergeWithTraceGen d w_r anc_cmp cmp asc).mapWires
      (embCast (rightHalfDTAEmb (arity d) w_r (arity d + mergeTraceSize d) (mergeTraceSize d)
        (mergeTraceSize (d + 1)) anc_cmp (by dsimp [mergeTraceSize]; omega)) hM)
    step.seq (left.seq right)

lemma mergeWithTraceGen_size (d w_r anc_cmp : ℕ)
    (cmp : LayeredCircuit ((w_r + w_r + 1) + anc_cmp)) (asc : Bool) :
    (mergeWithTraceGen d w_r anc_cmp cmp asc).size ≤ mergeTraceSize d * (cmp.size + 7 * w_r + 1) := by
  induction d with
  | zero => simp [mergeWithTraceGen, mergeTraceSize]
  | succ d ih =>
    dsimp only [mergeWithTraceGen]
    simp only [LayeredCircuit.seq_size, LayeredCircuit.mapWires_size]
    have hs := compareLayerWithTrace_size (arity d) w_r anc_cmp cmp asc
    rw [mergeTraceSize]
    nlinarith

lemma act_mergeWithTraceGen_ket {κ : Type} [LinearOrder κ] (d w_r anc_cmp : ℕ)
    (key : Qubits w_r → κ) (cmp : LayeredCircuit ((w_r + w_r + 1) + anc_cmp))
    (hcmp : cmp.ImplementsOnClean (permMat (cmpLtFn54 w_r key)))
    (asc : Bool) (x : Fin (arity d) → Qubits w_r) :
    act (mergeWithTraceGen d w_r anc_cmp cmp asc).unitary
        (ket (packDTA54 (arity d) w_r (mergeTraceSize d) anc_cmp x (fun _ => false))) =
      ket (packDTA54 (arity d) w_r (mergeTraceSize d) anc_cmp (merge key d asc x) (mergeTrace key d asc x)) := by
  induction d with
  | zero =>
    have h0 : (fun _ : Fin (mergeTraceSize 0) => false) = mergeTrace key 0 asc x := funext fun j => Fin.elim0 j
    rw [h0]; simp [mergeWithTraceGen, merge, LayeredCircuit.id_unitary, act_one]
  | succ d ih =>
    have hN : arity d + arity d = arity (d + 1) := rfl
    have hM : (((arity d + arity d) * w_r + mergeTraceSize (d + 1)) + anc_cmp) =
        (arity (d + 1) * w_r + mergeTraceSize (d + 1)) + anc_cmp := rfl
    let x0 : Fin (arity d + arity d) → Qubits w_r := x
    let compared : Fin (arity d + arity d) → Qubits w_r := compareLayer key asc x0
    let xL := merge key d asc (compared ∘ Fin.castAdd (arity d))
    let xR := merge key d asc (compared ∘ Fin.natAdd (arity d))
    let fStep : Fin (arity d) → Bool := layerFlags key asc x0
    let fL : Fin (mergeTraceSize d) → Bool := mergeTrace key d asc (compared ∘ Fin.castAdd (arity d))
    let fR : Fin (mergeTraceSize d) → Bool := mergeTrace key d asc (compared ∘ Fin.natAdd (arity d))
    let tr1 : Qubits (mergeTraceSize (d + 1)) := Fin.append fStep (fun _ => false)
    let tr2 : Qubits (mergeTraceSize (d + 1)) := Fin.append fStep (Fin.append fL (fun _ => false))
    let tr3 : Qubits (mergeTraceSize (d + 1)) := Fin.append fStep (Fin.append fL fR)
    let z0 := packDTA54 (arity (d + 1)) w_r (mergeTraceSize (d + 1)) anc_cmp x (fun _ => false)
    let z1 := packDTA54 (arity (d + 1)) w_r (mergeTraceSize (d + 1)) anc_cmp compared tr1
    let z2 := packDTA54 (arity (d + 1)) w_r (mergeTraceSize (d + 1)) anc_cmp (Fin.append xL (compared ∘ Fin.natAdd (arity d))) tr2
    let z3 := packDTA54 (arity (d + 1)) w_r (mergeTraceSize (d + 1)) anc_cmp (Fin.append xL xR) tr3
    have hstep : act ((compareLayerWithTrace (arity d) w_r anc_cmp cmp asc).mapWires
        (embCast (subTraceDTAEmb ((arity d + arity d) * w_r) 0 (arity d) (mergeTraceSize (d + 1)) anc_cmp
          (by dsimp [mergeTraceSize]; omega)) hM)).unitary (ket z0) = ket z1 := by
      refine act_embCast_ket _ hM (compareLayerWithTrace (arity d) w_r anc_cmp cmp asc)
        (packDTA54 (arity d + arity d) w_r (mergeTraceSize (d + 1)) anc_cmp x0 (fun _ => false))
        (packDTA54 (arity d + arity d) w_r (mergeTraceSize (d + 1)) anc_cmp compared tr1)
        z0 z1 (packDTA_cast_eq_gen hN hM x0 x (fun _ => rfl) _)
        (packDTA_cast_eq_gen hN hM compared compared (fun _ => rfl) _) ?_
      refine act_subTraceDTAEmb_ket _ _ x0 compared (fun _ => false) tr1 ?_ (fun k hk => by
        dsimp only [tr1]
        have hgt : arity d ≤ k.1 := by omega
        have hlt := k.isLt; simp only [mergeTraceSize, arity_eq_two_pow] at *; have heq : k = Fin.natAdd (arity d) ⟨k.1 - arity d, by omega⟩ := by
          ext; simp; omega
        rw [heq, Fin.append_right])
      have hslice_out : (fun j : Fin (arity d) => tr1 ⟨0 + j.1, by dsimp [mergeTraceSize]; omega⟩) = fStep := by
        funext j
        have heq : (⟨0 + j.1, by dsimp [mergeTraceSize]; omega⟩ : Fin (mergeTraceSize (d + 1))) =
            Fin.castAdd (mergeTraceSize d + mergeTraceSize d) j := Fin.ext (by simp)
        dsimp only [tr1]; rw [heq, Fin.append_left]
      rw [hslice_out]
      exact act_compareLayerWithTrace_ket (arity d) w_r anc_cmp key cmp hcmp asc x0
    have hleft : act ((mergeWithTraceGen d w_r anc_cmp cmp asc).mapWires
        (embCast (leftHalfDTAEmb (arity d) w_r (arity d) (mergeTraceSize d) (mergeTraceSize (d + 1)) anc_cmp
          (by dsimp [mergeTraceSize]; omega)) hM)).unitary (ket z1) = ket z2 := by
      refine act_embCast_ket _ hM (mergeWithTraceGen d w_r anc_cmp cmp asc)
        (packDTA54 (arity d + arity d) w_r (mergeTraceSize (d + 1)) anc_cmp
          (Fin.append (compared ∘ Fin.castAdd (arity d)) (compared ∘ Fin.natAdd (arity d))) tr1)
        (packDTA54 (arity d + arity d) w_r (mergeTraceSize (d + 1)) anc_cmp
          (Fin.append xL (compared ∘ Fin.natAdd (arity d))) tr2)
        z1 z2 (packDTA_split_arr_gen hN hM compared compared (fun _ => rfl) tr1)
        (packDTA_cast_eq_gen hN hM _ _ (fun _ => rfl) tr2) ?_
      refine act_leftHalfDTAEmb_ket _ _ (compared ∘ Fin.castAdd (arity d)) xL
        (compared ∘ Fin.natAdd (arity d)) tr1 tr2 ?_ (fun k hk => by
          dsimp only [tr1, tr2]
          by_cases hlt : k.1 < arity d
          · have heq : k = Fin.castAdd (mergeTraceSize d + mergeTraceSize d) ⟨k.1, hlt⟩ := Fin.ext rfl
            rw [heq, Fin.append_left, Fin.append_left]
          · have hgt : arity d + mergeTraceSize d ≤ k.1 := by omega
            have hlt2 := k.isLt; simp only [mergeTraceSize, arity_eq_two_pow] at *
            let k' : Fin (mergeTraceSize d) := ⟨k.1 - (arity d + mergeTraceSize d), by omega⟩
            have heq : k = Fin.natAdd (arity d) (Fin.natAdd (mergeTraceSize d) k') := by
              ext; simp [k']; omega
            rw [heq, Fin.append_right, Fin.append_right, Fin.append_right])
      have hslice_in : (fun j : Fin (mergeTraceSize d) => tr1 ⟨arity d + j.1, by dsimp [mergeTraceSize]; omega⟩) =
          fun _ => false := by
        funext j
        have heq : (⟨arity d + j.1, by dsimp [mergeTraceSize]; omega⟩ : Fin (mergeTraceSize (d + 1))) =
            Fin.natAdd (arity d) (Fin.castAdd (mergeTraceSize d) j) := Fin.ext rfl
        dsimp only [tr1]; rw [heq, Fin.append_right]
      have hslice_out : (fun j : Fin (mergeTraceSize d) => tr2 ⟨arity d + j.1, by dsimp [mergeTraceSize]; omega⟩) =
          fL := by
        funext j
        have heq : (⟨arity d + j.1, by dsimp [mergeTraceSize]; omega⟩ : Fin (mergeTraceSize (d + 1))) =
            Fin.natAdd (arity d) (Fin.castAdd (mergeTraceSize d) j) := Fin.ext rfl
        dsimp only [tr2]; rw [heq, Fin.append_right, Fin.append_left]
      rw [hslice_in, hslice_out]
      exact ih (compared ∘ Fin.castAdd (arity d))
    have hright : act ((mergeWithTraceGen d w_r anc_cmp cmp asc).mapWires
        (embCast (rightHalfDTAEmb (arity d) w_r (arity d + mergeTraceSize d) (mergeTraceSize d)
          (mergeTraceSize (d + 1)) anc_cmp (by dsimp [mergeTraceSize]; omega)) hM)).unitary
        (ket z2) = ket z3 := by
      refine act_embCast_ket _ hM (mergeWithTraceGen d w_r anc_cmp cmp asc)
        (packDTA54 (arity d + arity d) w_r (mergeTraceSize (d + 1)) anc_cmp
          (Fin.append xL (compared ∘ Fin.natAdd (arity d))) tr2)
        (packDTA54 (arity d + arity d) w_r (mergeTraceSize (d + 1)) anc_cmp (Fin.append xL xR) tr3)
        z2 z3 (packDTA_cast_eq_gen hN hM _ _ (fun _ => rfl) tr2)
        (packDTA_cast_eq_gen hN hM _ _ (fun _ => rfl) tr3) ?_
      refine act_rightHalfDTAEmb_ket _ _ xL (compared ∘ Fin.natAdd (arity d)) xR tr2 tr3 ?_ (fun k hk => by
        dsimp only [tr2, tr3]
        by_cases hlt : k.1 < arity d
        · have heq : k = Fin.castAdd (mergeTraceSize d + mergeTraceSize d) ⟨k.1, hlt⟩ := Fin.ext rfl
          rw [heq, Fin.append_left, Fin.append_left]
        · have hlt2 : k.1 - arity d < mergeTraceSize d := by
            have := k.isLt; simp only [mergeTraceSize, arity_eq_two_pow] at *; omega
          have heq : k = Fin.natAdd (arity d) (Fin.castAdd (mergeTraceSize d) ⟨k.1 - arity d, hlt2⟩) := by
            ext; dsimp only [Fin.val_natAdd, Fin.val_castAdd]; omega
          rw [heq, Fin.append_right, Fin.append_right, Fin.append_left, Fin.append_left])
      have hslice_in : (fun j : Fin (mergeTraceSize d) =>
          tr2 ⟨arity d + mergeTraceSize d + j.1, by dsimp [mergeTraceSize]; omega⟩) = fun _ => false := by
        funext j
        have heq : (⟨arity d + mergeTraceSize d + j.1, by dsimp [mergeTraceSize]; omega⟩ : Fin (mergeTraceSize (d + 1))) =
            Fin.natAdd (arity d) (Fin.natAdd (mergeTraceSize d) j) := by
          ext; dsimp only [Fin.val_natAdd]; omega
        dsimp only [tr2]; rw [heq, Fin.append_right, Fin.append_right]
      have hslice_out : (fun j : Fin (mergeTraceSize d) =>
          tr3 ⟨arity d + mergeTraceSize d + j.1, by dsimp [mergeTraceSize]; omega⟩) = fR := by
        funext j
        have heq : (⟨arity d + mergeTraceSize d + j.1, by dsimp [mergeTraceSize]; omega⟩ : Fin (mergeTraceSize (d + 1))) =
            Fin.natAdd (arity d) (Fin.natAdd (mergeTraceSize d) j) := by
          ext; dsimp only [Fin.val_natAdd]; omega
        dsimp only [tr3]; rw [heq, Fin.append_right, Fin.append_right]
      rw [hslice_in, hslice_out]
      exact ih (compared ∘ Fin.natAdd (arity d))
    dsimp only [mergeWithTraceGen]
    rw [LayeredCircuit.seq_unitary, LayeredCircuit.seq_unitary, act_mul, act_mul]
    change act _ (act _ (act _ (ket z0))) = _
    rw [hstep, hleft, hright]
    rfl

noncomputable def sortWithTraceGen :
    (d w_r anc_cmp : ℕ) → LayeredCircuit ((w_r + w_r + 1) + anc_cmp) → Bool →
      LayeredCircuit ((arity d * w_r + sortTraceSize d) + anc_cmp)
  | 0, _, _, _, _ => LayeredCircuit.id _
  | d + 1, w_r, anc_cmp, cmp, asc =>
    have hM : (((arity d + arity d) * w_r + sortTraceSize (d + 1)) + anc_cmp) =
        (arity (d + 1) * w_r + sortTraceSize (d + 1)) + anc_cmp := rfl
    let left := (sortWithTraceGen d w_r anc_cmp cmp true).mapWires
      (embCast (leftHalfDTAEmb (arity d) w_r 0 (sortTraceSize d) (sortTraceSize (d + 1)) anc_cmp
        (by dsimp [sortTraceSize]; omega)) hM)
    let right := (sortWithTraceGen d w_r anc_cmp cmp false).mapWires
      (embCast (rightHalfDTAEmb (arity d) w_r (sortTraceSize d) (sortTraceSize d) (sortTraceSize (d + 1)) anc_cmp
        (by dsimp [sortTraceSize]; omega)) hM)
    let merge := (mergeWithTraceGen (d + 1) w_r anc_cmp cmp asc).mapWires
      (subTraceDTAEmb (arity (d + 1) * w_r) (sortTraceSize d + sortTraceSize d)
        (mergeTraceSize (d + 1)) (sortTraceSize (d + 1)) anc_cmp (by dsimp [sortTraceSize]; omega))
    left.seq (right.seq merge)

lemma sortWithTraceGen_size (d w_r anc_cmp : ℕ)
    (cmp : LayeredCircuit ((w_r + w_r + 1) + anc_cmp)) (asc : Bool) :
    (sortWithTraceGen d w_r anc_cmp cmp asc).size ≤ sortTraceSize d * (cmp.size + 7 * w_r + 1) := by
  induction d generalizing asc with
  | zero => simp [sortWithTraceGen, sortTraceSize]
  | succ d ih =>
    dsimp only [sortWithTraceGen]
    simp only [LayeredCircuit.seq_size, LayeredCircuit.mapWires_size]
    have hL := ih true
    have hR := ih false
    have hM := mergeWithTraceGen_size (d + 1) w_r anc_cmp cmp asc
    rw [sortTraceSize]
    nlinarith

lemma act_sortWithTraceGen_ket {κ : Type} [LinearOrder κ] (d w_r anc_cmp : ℕ)
    (key : Qubits w_r → κ) (cmp : LayeredCircuit ((w_r + w_r + 1) + anc_cmp))
    (hcmp : cmp.ImplementsOnClean (permMat (cmpLtFn54 w_r key)))
    (asc : Bool) (x : Fin (arity d) → Qubits w_r) :
    act (sortWithTraceGen d w_r anc_cmp cmp asc).unitary
        (ket (packDTA54 (arity d) w_r (sortTraceSize d) anc_cmp x (fun _ => false))) =
      ket (packDTA54 (arity d) w_r (sortTraceSize d) anc_cmp (sort key d asc x) (sortTrace key d asc x)) := by
  induction d generalizing asc with
  | zero =>
    have h0 : (fun _ : Fin (sortTraceSize 0) => false) = sortTrace key 0 asc x := funext fun j => Fin.elim0 j
    rw [h0]; simp [sortWithTraceGen, sort, LayeredCircuit.id_unitary, act_one]
  | succ d ih =>
    have hN : arity d + arity d = arity (d + 1) := rfl
    have hM : (((arity d + arity d) * w_r + sortTraceSize (d + 1)) + anc_cmp) =
        (arity (d + 1) * w_r + sortTraceSize (d + 1)) + anc_cmp := rfl
    let xL := sort key d true (x ∘ Fin.castAdd (arity d))
    let xR := sort key d false (x ∘ Fin.natAdd (arity d))
    let xLR : Fin (arity (d + 1)) → Qubits w_r := Fin.append xL xR
    let fL : Qubits (sortTraceSize d) := sortTrace key d true (x ∘ Fin.castAdd (arity d))
    let fR : Qubits (sortTraceSize d) := sortTrace key d false (x ∘ Fin.natAdd (arity d))
    let fM : Qubits (mergeTraceSize (d + 1)) := mergeTrace key (d + 1) asc xLR
    let tr1 : Qubits (sortTraceSize (d + 1)) := Fin.append (Fin.append fL (fun _ => false)) (fun _ => false)
    let tr2 : Qubits (sortTraceSize (d + 1)) := Fin.append (Fin.append fL fR) (fun _ => false)
    let tr3 : Qubits (sortTraceSize (d + 1)) := Fin.append (Fin.append fL fR) fM
    let z0 := packDTA54 (arity (d + 1)) w_r (sortTraceSize (d + 1)) anc_cmp x (fun _ => false)
    let z1 := packDTA54 (arity (d + 1)) w_r (sortTraceSize (d + 1)) anc_cmp
      (Fin.append xL (x ∘ Fin.natAdd (arity d))) tr1
    let z2 := packDTA54 (arity (d + 1)) w_r (sortTraceSize (d + 1)) anc_cmp xLR tr2
    let z3 := packDTA54 (arity (d + 1)) w_r (sortTraceSize (d + 1)) anc_cmp
      (merge key (d + 1) asc xLR) tr3
    have hleft : act ((sortWithTraceGen d w_r anc_cmp cmp true).mapWires
        (embCast (leftHalfDTAEmb (arity d) w_r 0 (sortTraceSize d) (sortTraceSize (d + 1)) anc_cmp
          (by dsimp [sortTraceSize]; omega)) hM)).unitary (ket z0) = ket z1 := by
      refine act_embCast_ket _ hM (sortWithTraceGen d w_r anc_cmp cmp true)
        (packDTA54 (arity d + arity d) w_r (sortTraceSize (d + 1)) anc_cmp
          (Fin.append (x ∘ Fin.castAdd (arity d)) (x ∘ Fin.natAdd (arity d))) (fun _ => false))
        (packDTA54 (arity d + arity d) w_r (sortTraceSize (d + 1)) anc_cmp
          (Fin.append xL (x ∘ Fin.natAdd (arity d))) tr1)
        z0 z1 (packDTA_split_arr_gen hN hM x x (fun _ => rfl) (fun _ => false))
        (packDTA_cast_eq_gen hN hM _ _ (fun _ => rfl) tr1) ?_
      refine act_leftHalfDTAEmb_ket _ _ (x ∘ Fin.castAdd (arity d)) xL (x ∘ Fin.natAdd (arity d))
        (fun _ => false) tr1 ?_ (fun k hk => by
          dsimp only [tr1]
          have hge : sortTraceSize d ≤ k.1 := by omega
          by_cases h1 : k.1 < sortTraceSize d + sortTraceSize d
          · have heq : k = Fin.castAdd (mergeTraceSize (d + 1))
                (Fin.natAdd (sortTraceSize d) ⟨k.1 - sortTraceSize d, by omega⟩) := by
              ext; simp; omega
            rw [heq, Fin.append_left, Fin.append_right]
          · have heq : k = Fin.natAdd (sortTraceSize d + sortTraceSize d)
                ⟨k.1 - (sortTraceSize d + sortTraceSize d), by
                  have := k.isLt; dsimp [sortTraceSize] at *; omega⟩ := by
              ext; simp; omega
            rw [heq, Fin.append_right])
      have hslice_out : (fun j : Fin (sortTraceSize d) =>
          tr1 ⟨0 + j.1, by dsimp [sortTraceSize]; omega⟩) = fL := by
        funext j
        have heq : (⟨0 + j.1, by dsimp [sortTraceSize]; omega⟩ : Fin (sortTraceSize (d + 1))) =
            Fin.castAdd (mergeTraceSize (d + 1)) (Fin.castAdd (sortTraceSize d) j) := Fin.ext (by simp)
        dsimp only [tr1]; rw [heq, Fin.append_left, Fin.append_left]
      rw [hslice_out]
      exact ih true (x ∘ Fin.castAdd (arity d))
    have hright : act ((sortWithTraceGen d w_r anc_cmp cmp false).mapWires
        (embCast (rightHalfDTAEmb (arity d) w_r (sortTraceSize d) (sortTraceSize d)
          (sortTraceSize (d + 1)) anc_cmp (by dsimp [sortTraceSize]; omega)) hM)).unitary
        (ket z1) = ket z2 := by
      refine act_embCast_ket _ hM (sortWithTraceGen d w_r anc_cmp cmp false)
        (packDTA54 (arity d + arity d) w_r (sortTraceSize (d + 1)) anc_cmp
          (Fin.append xL (x ∘ Fin.natAdd (arity d))) tr1)
        (packDTA54 (arity d + arity d) w_r (sortTraceSize (d + 1)) anc_cmp xLR tr2)
        z1 z2 (packDTA_cast_eq_gen hN hM _ _ (fun _ => rfl) tr1)
        (packDTA_cast_eq_gen hN hM _ xLR (fun _ => rfl) tr2) ?_
      refine act_rightHalfDTAEmb_ket _ _ xL (x ∘ Fin.natAdd (arity d)) xR tr1 tr2 ?_ (fun k hk => by
        dsimp only [tr1, tr2]
        by_cases h1 : k.1 < sortTraceSize d
        · have heq : k = Fin.castAdd (mergeTraceSize (d + 1))
              (Fin.castAdd (sortTraceSize d) ⟨k.1, h1⟩) := Fin.ext rfl
          rw [heq, Fin.append_left, Fin.append_left, Fin.append_left, Fin.append_left]
        · have hge : sortTraceSize d + sortTraceSize d ≤ k.1 := by omega
          have heq : k = Fin.natAdd (sortTraceSize d + sortTraceSize d)
              ⟨k.1 - (sortTraceSize d + sortTraceSize d), by
                have := k.isLt; dsimp [sortTraceSize] at *; omega⟩ := by
            ext; simp; omega
          rw [heq, Fin.append_right, Fin.append_right])
      have hslice_in : (fun j : Fin (sortTraceSize d) =>
          tr1 ⟨sortTraceSize d + j.1, by dsimp [sortTraceSize]; omega⟩) = fun _ => false := by
        funext j
        have heq : (⟨sortTraceSize d + j.1, by dsimp [sortTraceSize]; omega⟩ : Fin (sortTraceSize (d + 1))) =
            Fin.castAdd (mergeTraceSize (d + 1)) (Fin.natAdd (sortTraceSize d) j) := Fin.ext rfl
        dsimp only [tr1]; rw [heq, Fin.append_left, Fin.append_right]
      have hslice_out : (fun j : Fin (sortTraceSize d) =>
          tr2 ⟨sortTraceSize d + j.1, by dsimp [sortTraceSize]; omega⟩) = fR := by
        funext j
        have heq : (⟨sortTraceSize d + j.1, by dsimp [sortTraceSize]; omega⟩ : Fin (sortTraceSize (d + 1))) =
            Fin.castAdd (mergeTraceSize (d + 1)) (Fin.natAdd (sortTraceSize d) j) := Fin.ext rfl
        dsimp only [tr2]; rw [heq, Fin.append_left, Fin.append_right]
      rw [hslice_in, hslice_out]
      exact ih false (x ∘ Fin.natAdd (arity d))
    have hmerge : act ((mergeWithTraceGen (d + 1) w_r anc_cmp cmp asc).mapWires
        (subTraceDTAEmb (arity (d + 1) * w_r) (sortTraceSize d + sortTraceSize d)
          (mergeTraceSize (d + 1)) (sortTraceSize (d + 1)) anc_cmp
          (by dsimp [sortTraceSize]; omega))).unitary (ket z2) = ket z3 := by
      refine act_subTraceDTAEmb_ket _ _ xLR (merge key (d + 1) asc xLR) tr2 tr3 ?_ (fun k hk => by
        dsimp only [tr2, tr3]
        have h1 : k.1 < sortTraceSize d + sortTraceSize d := by
          have := k.isLt; dsimp [sortTraceSize] at *; omega
        have heq : k = Fin.castAdd (mergeTraceSize (d + 1)) ⟨k.1, h1⟩ := Fin.ext rfl
        rw [heq, Fin.append_left, Fin.append_left])
      have hslice_in : (fun j : Fin (mergeTraceSize (d + 1)) =>
          tr2 ⟨sortTraceSize d + sortTraceSize d + j.1, by dsimp [sortTraceSize]; omega⟩) =
          fun _ => false := by
        funext j
        have heq : (⟨sortTraceSize d + sortTraceSize d + j.1, by dsimp [sortTraceSize]; omega⟩ :
            Fin (sortTraceSize (d + 1))) = Fin.natAdd (sortTraceSize d + sortTraceSize d) j :=
          Fin.ext rfl
        dsimp only [tr2]; rw [heq, Fin.append_right]
      have hslice_out : (fun j : Fin (mergeTraceSize (d + 1)) =>
          tr3 ⟨sortTraceSize d + sortTraceSize d + j.1, by dsimp [sortTraceSize]; omega⟩) = fM := by
        funext j
        have heq : (⟨sortTraceSize d + sortTraceSize d + j.1, by dsimp [sortTraceSize]; omega⟩ :
            Fin (sortTraceSize (d + 1))) = Fin.natAdd (sortTraceSize d + sortTraceSize d) j :=
          Fin.ext rfl
        dsimp only [tr3]; rw [heq, Fin.append_right]
      rw [hslice_in, hslice_out]
      exact act_mergeWithTraceGen_ket (d + 1) w_r anc_cmp key cmp hcmp asc xLR
    dsimp only [sortWithTraceGen]
    rw [LayeredCircuit.seq_unitary, LayeredCircuit.seq_unitary, act_mul, act_mul]
    change act _ (act _ (act _ (ket z0))) = _
    rw [hleft, hright, hmerge]
    rfl

lemma sortWithTraceGen_adj_unroute {κ : Type} [LinearOrder κ] (d w_k w_p anc_cmp : ℕ)
    (key0 : Qubits w_k → κ)
    (cmp : LayeredCircuit (((w_k + w_p) + (w_k + w_p) + 1) + anc_cmp))
    (hcmp : cmp.ImplementsOnClean (permMat (cmpLtFn54 (w_k + w_p) (key0 ∘ recKey54))))
    (asc : Bool) (k_in : Fin (arity d) → Qubits w_k) (y_p : Fin (arity d) → Qubits w_p) :
    act (sortWithTraceGen d (w_k + w_p) anc_cmp cmp asc).adj.unitary
        (ket (packDTA54 (arity d) (w_k + w_p) (sortTraceSize d) anc_cmp
          (fun i => Fin.append (sort key0 d asc k_in i) (y_p i))
          (sortTrace key0 d asc k_in))) =
      ket (packDTA54 (arity d) (w_k + w_p) (sortTraceSize d) anc_cmp
        (fun i => Fin.append (k_in i) (unrouteSort d (sortTrace key0 d asc k_in) y_p i))
        (fun _ => false)) := by
  let tr := sortTrace key0 d asc k_in
  let x_in : Fin (arity d) → Qubits (w_k + w_p) := fun i => Fin.append (k_in i) (unrouteSort d tr y_p i)
  have hrecK : recKey54 ∘ x_in = k_in := by
    funext i j; exact Fin.append_left _ _ j
  have hrecP : recPay54 ∘ x_in = unrouteSort d tr y_p := by
    funext i j; exact Fin.append_right _ _ j
  have htrace : sortTrace (key0 ∘ recKey54) d asc x_in = tr := by
    rw [sortTrace_of_key_comp, hrecK]
  have hsortK : recKey54 ∘ sort (key0 ∘ recKey54) d asc x_in = sort key0 d asc k_in := by
    rw [sort_of_key_comp, hrecK]
  have hsortP : recPay54 ∘ sort (key0 ∘ recKey54) d asc x_in = y_p := by
    rw [← routeSort_sortTrace (key0 ∘ recKey54) d asc x_in, ← routeSort_comp, htrace, hrecP,
      routeSort_unrouteSort]
  have hsort : sort (key0 ∘ recKey54) d asc x_in =
      fun i => Fin.append (sort key0 d asc k_in i) (y_p i) := by
    funext i
    have hrec_app : Fin.append (recKey54 (sort (key0 ∘ recKey54) d asc x_in i))
        (recPay54 (sort (key0 ∘ recKey54) d asc x_in i)) = sort (key0 ∘ recKey54) d asc x_in i :=
      fin_append_castAdd_natAdd
    rw [← hrec_app]
    have hk_i := congrFun hsortK i
    have hp_i := congrFun hsortP i
    change Fin.append ((recKey54 ∘ sort (key0 ∘ recKey54) d asc x_in) i)
      ((recPay54 ∘ sort (key0 ∘ recKey54) d asc x_in) i) = _
    rw [hk_i, hp_i]
  have hf := act_sortWithTraceGen_ket d (w_k + w_p) anc_cmp (key0 ∘ recKey54) cmp hcmp asc x_in
  rw [hsort, htrace] at hf
  rw [← hf, ← act_mul, LayeredCircuit.adj_unitary,
    Matrix.mem_unitaryGroup_iff'.mp (sortWithTraceGen d (w_k + w_p) anc_cmp cmp asc).unitary_mem_unitaryGroup,
    act_one]

private def keyCmpEmb (w_k w_p : ℕ) :
    Fin ((w_k + w_k + 1) + w_k) ↪ Fin (((w_k + w_p) + (w_k + w_p) + 1) + w_k) where
  toFun u :=
    if h1 : u.1 < w_k then ⟨u.1, by omega⟩
    else if h2 : u.1 < w_k + w_k then ⟨(w_k + w_p) + (u.1 - w_k), by omega⟩
    else if h3 : u.1 = w_k + w_k then ⟨(w_k + w_p) + (w_k + w_p), by omega⟩
    else ⟨(w_k + w_p) + (w_k + w_p) + 1 + (u.1 - (w_k + w_k + 1)), by have := u.isLt; omega⟩
  inj' u v h := by
    have hv := congrArg Fin.val h
    dsimp only at hv
    by_cases hu1 : u.1 < w_k
    · rw [dif_pos hu1] at hv
      by_cases hv1 : v.1 < w_k
      · rw [dif_pos hv1] at hv; exact Fin.ext (by simp only at hv; exact hv)
      · by_cases hv2 : v.1 < w_k + w_k
        · rw [dif_neg hv1, dif_pos hv2] at hv; simp only at hv; omega
        · by_cases hv3 : v.1 = w_k + w_k
          · rw [dif_neg hv1, dif_neg hv2, dif_pos hv3] at hv; simp only at hv; omega
          · rw [dif_neg hv1, dif_neg hv2, dif_neg hv3] at hv; simp only at hv; omega
    · by_cases hu2 : u.1 < w_k + w_k
      · rw [dif_neg hu1, dif_pos hu2] at hv
        by_cases hv1 : v.1 < w_k
        · rw [dif_pos hv1] at hv; simp only at hv; omega
        · by_cases hv2 : v.1 < w_k + w_k
          · rw [dif_neg hv1, dif_pos hv2] at hv; simp only at hv; exact Fin.ext (by omega)
          · by_cases hv3 : v.1 = w_k + w_k
            · rw [dif_neg hv1, dif_neg hv2, dif_pos hv3] at hv; simp only at hv; omega
            · rw [dif_neg hv1, dif_neg hv2, dif_neg hv3] at hv; simp only at hv; omega
      · by_cases hu3 : u.1 = w_k + w_k
        · rw [dif_neg hu1, dif_neg hu2, dif_pos hu3] at hv
          by_cases hv1 : v.1 < w_k
          · rw [dif_pos hv1] at hv; simp only at hv; omega
          · by_cases hv2 : v.1 < w_k + w_k
            · rw [dif_neg hv1, dif_pos hv2] at hv; simp only at hv; omega
            · by_cases hv3 : v.1 = w_k + w_k
              · exact Fin.ext (hu3.trans hv3.symm)
              · rw [dif_neg hv1, dif_neg hv2, dif_neg hv3] at hv; simp only at hv; omega
        · rw [dif_neg hu1, dif_neg hu2, dif_neg hu3] at hv
          by_cases hv1 : v.1 < w_k
          · rw [dif_pos hv1] at hv; simp only at hv; omega
          · by_cases hv2 : v.1 < w_k + w_k
            · rw [dif_neg hv1, dif_pos hv2] at hv; simp only at hv; omega
            · by_cases hv3 : v.1 = w_k + w_k
              · rw [dif_neg hv1, dif_neg hv2, dif_pos hv3] at hv; simp only at hv; omega
              · rw [dif_neg hv1, dif_neg hv2, dif_neg hv3] at hv; simp only at hv
                have hu_ge : w_k + w_k + 1 ≤ u.1 := by omega
                have hv_ge : w_k + w_k + 1 ≤ v.1 := by omega
                exact Fin.ext (by omega)

private lemma keyCmpEmb_apply (w_k w_p : ℕ) (u : Fin ((w_k + w_k + 1) + w_k)) :
    keyCmpEmb w_k w_p u =
      if h1 : u.1 < w_k then ⟨u.1, by omega⟩
      else if h2 : u.1 < w_k + w_k then ⟨(w_k + w_p) + (u.1 - w_k), by omega⟩
      else if h3 : u.1 = w_k + w_k then ⟨(w_k + w_p) + (w_k + w_p), by omega⟩
      else ⟨(w_k + w_p) + (w_k + w_p) + 1 + (u.1 - (w_k + w_k + 1)), by have := u.isLt; omega⟩ := rfl

noncomputable def keyCmpCircuit (w_k w_p : ℕ) :
    LayeredCircuit (((w_k + w_p) + (w_k + w_p) + 1) + w_k) :=
  (ltBitsCircuit w_k).mapWires (keyCmpEmb w_k w_p)

lemma keyCmpCircuit_size (w_k w_p : ℕ) : (keyCmpCircuit w_k w_p).size ≤ 20 * w_k + 1 := by
  simpa [keyCmpCircuit] using ltBitsCircuit_size w_k

lemma keyCmpCircuit_implements (w_k w_p : ℕ) :
    (keyCmpCircuit w_k w_p).ImplementsOnClean
      (permMat (cmpLtFn54 (w_k + w_p) (fun r => bitsToNat (recKey54 r)))) := by
  apply implementsOnClean_of_act_perm
  intro x
  let emb := keyCmpEmb w_k w_p
  let xK : Qubits (w_k + w_k + 1) := fun u =>
    if u.1 < w_k then x ⟨u.1, by omega⟩
    else if u.1 < w_k + w_k then x ⟨(w_k + w_p) + (u.1 - w_k), by omega⟩
    else x ⟨(w_k + w_p) + (w_k + w_p), by omega⟩
  let zIn := padZero ((w_k + w_p) + (w_k + w_p) + 1) w_k x
  let zOut := padZero ((w_k + w_p) + (w_k + w_p) + 1) w_k
    (cmpLtFn54 (w_k + w_p) (fun r => bitsToNat (recKey54 r)) x)
  have ha_eq : (fun i : Fin w_k => xK ⟨i.1, by omega⟩) =
      recKey54 (fun i : Fin (w_k + w_p) => x ⟨i.1, by omega⟩) := by
    funext i; dsimp only [xK, recKey54]; rw [if_pos i.isLt]; rfl
  have hb_eq : (fun i : Fin w_k => xK ⟨w_k + i.1, by omega⟩) =
      recKey54 (fun i : Fin (w_k + w_p) => x ⟨(w_k + w_p) + i.1, by omega⟩) := by
    funext i; dsimp only [xK, recKey54]
    have h1 : ¬ (w_k + i.1 < w_k) := by omega
    have h2 : w_k + i.1 < w_k + w_k := by have := i.isLt; omega
    rw [if_neg h1, if_pos h2]
    congr 1; apply Fin.ext; dsimp only [Fin.val_castAdd]; omega
  have hflag_eq : xK ⟨w_k + w_k, by omega⟩ = x ⟨(w_k + w_p) + (w_k + w_p), by omega⟩ := by
    dsimp only [xK]
    have h1 : ¬ (w_k + w_k < w_k) := by omega
    have h2 : ¬ (w_k + w_k < w_k + w_k) := by omega
    rw [if_neg h1, if_neg h2]
  have hcomp_in : zIn ∘ emb = padZero (w_k + w_k + 1) w_k xK := by
    funext u
    dsimp only [Function.comp_apply, emb, zIn]
    rw [keyCmpEmb_apply]
    by_cases h1 : u.1 < w_k
    · rw [dif_pos h1]
      have hl : (⟨u.1, by omega⟩ : Fin (((w_k + w_p) + (w_k + w_p) + 1) + w_k)) =
          Fin.castAdd w_k ⟨u.1, by omega⟩ := Fin.ext rfl
      have hr : u = Fin.castAdd w_k ⟨u.1, by omega⟩ := Fin.ext rfl
      rw [hl, padZero_castAdd]; conv_rhs => rw [hr, padZero_castAdd]
      dsimp only [xK]; rw [if_pos h1]
    · by_cases h2 : u.1 < w_k + w_k
      · rw [dif_neg h1, dif_pos h2]
        have hl : (⟨(w_k + w_p) + (u.1 - w_k), by omega⟩ :
            Fin (((w_k + w_p) + (w_k + w_p) + 1) + w_k)) =
            Fin.castAdd w_k ⟨(w_k + w_p) + (u.1 - w_k), by omega⟩ := Fin.ext rfl
        have hr : u = Fin.castAdd w_k ⟨u.1, by omega⟩ := Fin.ext rfl
        rw [hl, padZero_castAdd]; conv_rhs => rw [hr, padZero_castAdd]
        dsimp only [xK]; rw [if_neg h1, if_pos h2]
      · by_cases h3 : u.1 = w_k + w_k
        · rw [dif_neg h1, dif_neg h2, dif_pos h3]
          have hl : (⟨(w_k + w_p) + (w_k + w_p), by omega⟩ :
              Fin (((w_k + w_p) + (w_k + w_p) + 1) + w_k)) =
              Fin.castAdd w_k ⟨(w_k + w_p) + (w_k + w_p), by omega⟩ := Fin.ext rfl
          have hr : u = Fin.castAdd w_k ⟨u.1, by omega⟩ := Fin.ext rfl
          rw [hl, padZero_castAdd]; conv_rhs => rw [hr, padZero_castAdd]
          dsimp only [xK]; rw [if_neg h1, if_neg h2]
        · rw [dif_neg h1, dif_neg h2, dif_neg h3]
          have hl : (⟨(w_k + w_p) + (w_k + w_p) + 1 + (u.1 - (w_k + w_k + 1)), by have := u.isLt; omega⟩ :
              Fin (((w_k + w_p) + (w_k + w_p) + 1) + w_k)) =
              Fin.natAdd ((w_k + w_p) + (w_k + w_p) + 1) ⟨u.1 - (w_k + w_k + 1), by have := u.isLt; omega⟩ :=
            Fin.ext rfl
          have hr : u = Fin.natAdd (w_k + w_k + 1) ⟨u.1 - (w_k + w_k + 1), by have := u.isLt; omega⟩ := by
            ext; simp; omega
          rw [hl, padZero_natAdd]; conv_rhs => rw [hr, padZero_natAdd]
  have hcomp_out : zOut ∘ emb = padZero (w_k + w_k + 1) w_k (ltBitsFn54 w_k xK) := by
    funext u
    dsimp only [Function.comp_apply, emb, zOut, cmpLtFn54, ltBitsFn54]
    rw [keyCmpEmb_apply]
    by_cases h1 : u.1 < w_k
    · rw [dif_pos h1]
      have hl : (⟨u.1, by omega⟩ : Fin (((w_k + w_p) + (w_k + w_p) + 1) + w_k)) =
          Fin.castAdd w_k ⟨u.1, by omega⟩ := Fin.ext rfl
      have hr : u = Fin.castAdd w_k ⟨u.1, by omega⟩ := Fin.ext rfl
      rw [hl, padZero_castAdd, Function.update_of_ne (Fin.ne_of_val_ne (by dsimp; omega))]
      conv_rhs => rw [hr, padZero_castAdd, Function.update_of_ne (Fin.ne_of_val_ne (by dsimp; omega))]
      dsimp only [xK]; rw [if_pos h1]
    · by_cases h2 : u.1 < w_k + w_k
      · rw [dif_neg h1, dif_pos h2]
        have hl : (⟨(w_k + w_p) + (u.1 - w_k), by omega⟩ :
            Fin (((w_k + w_p) + (w_k + w_p) + 1) + w_k)) =
            Fin.castAdd w_k ⟨(w_k + w_p) + (u.1 - w_k), by omega⟩ := Fin.ext rfl
        have hr : u = Fin.castAdd w_k ⟨u.1, by omega⟩ := Fin.ext rfl
        rw [hl, padZero_castAdd, Function.update_of_ne (Fin.ne_of_val_ne (by dsimp; omega))]
        conv_rhs => rw [hr, padZero_castAdd, Function.update_of_ne (Fin.ne_of_val_ne (by dsimp; omega))]
        dsimp only [xK]; rw [if_neg h1, if_pos h2]
      · by_cases h3 : u.1 = w_k + w_k
        · rw [dif_neg h1, dif_neg h2, dif_pos h3]
          have hl : (⟨(w_k + w_p) + (w_k + w_p), by omega⟩ :
              Fin (((w_k + w_p) + (w_k + w_p) + 1) + w_k)) =
              Fin.castAdd w_k ⟨(w_k + w_p) + (w_k + w_p), by omega⟩ := Fin.ext rfl
          have hr : u = Fin.castAdd w_k ⟨u.1, by omega⟩ := Fin.ext rfl
          have hr2 : (⟨u.1, by omega⟩ : Fin (w_k + w_k + 1)) = ⟨w_k + w_k, by omega⟩ := Fin.ext h3
          rw [hl, padZero_castAdd, Function.update_self]
          conv_rhs => rw [hr, padZero_castAdd, hr2, Function.update_self]
          rw [ha_eq, hb_eq, hflag_eq]
        · rw [dif_neg h1, dif_neg h2, dif_neg h3]
          have hl : (⟨(w_k + w_p) + (w_k + w_p) + 1 + (u.1 - (w_k + w_k + 1)), by have := u.isLt; omega⟩ :
              Fin (((w_k + w_p) + (w_k + w_p) + 1) + w_k)) =
              Fin.natAdd ((w_k + w_p) + (w_k + w_p) + 1) ⟨u.1 - (w_k + w_k + 1), by have := u.isLt; omega⟩ :=
            Fin.ext rfl
          have hr : u = Fin.natAdd (w_k + w_k + 1) ⟨u.1 - (w_k + w_k + 1), by have := u.isLt; omega⟩ := by
            ext; simp; omega
          rw [hl, padZero_natAdd]; conv_rhs => rw [hr, padZero_natAdd]
  have hact : act (ltBitsCircuit w_k).unitary (ket (zIn ∘ emb)) =
      ket (padZero (w_k + w_k + 1) w_k (ltBitsFn54 w_k xK)) := by
    rw [hcomp_in]
    exact act_ket_of_implementsOnClean_perm (ltBitsCircuit_implements w_k) xK
  refine act_mapWires_ket (ltBitsCircuit w_k) emb zIn _ hact zOut hcomp_out ?_
  intro u hu
  cases u using Fin.addCases with
  | left a =>
    dsimp only [zOut, zIn, cmpLtFn54]
    rw [padZero_castAdd, padZero_castAdd]
    have hne : a ≠ ⟨(w_k + w_p) + (w_k + w_p), by omega⟩ := by
      intro ha; apply hu
      refine ⟨Fin.castAdd w_k ⟨w_k + w_k, by omega⟩, ?_⟩
      change emb ⟨w_k + w_k, by omega⟩ = Fin.castAdd w_k a
      rw [keyCmpEmb_apply, dif_neg (by simp only; omega), dif_neg (by simp only; omega), dif_pos rfl]
      exact Fin.ext (by simp [ha])
    rw [Function.update_of_ne hne]
  | right b =>
    dsimp only [zOut, zIn]; rw [padZero_natAdd, padZero_natAdd]

noncomputable def bitonicSortKeyCircuit (d w_k w_p : ℕ) (asc : Bool) :
    LayeredCircuit ((arity d * (w_k + w_p) + sortTraceSize d) + w_k) :=
  sortWithTraceGen d (w_k + w_p) w_k (keyCmpCircuit w_k w_p) asc

lemma bitonicSortKeyCircuit_size (d w_k w_p : ℕ) (asc : Bool) :
    ((bitonicSortKeyCircuit d w_k w_p asc).size : ℝ) ≤
      27 * (2 ^ d : ℝ) * ((d + 1 : ℝ) ^ 2) * (w_k + w_p + 1 : ℝ) := by
  have h1 : (bitonicSortKeyCircuit d w_k w_p asc).size ≤
      sortTraceSize d * ((20 * w_k + 1) + 7 * (w_k + w_p) + 1) := by
    have hs := sortWithTraceGen_size d (w_k + w_p) w_k (keyCmpCircuit w_k w_p) asc
    have hk := keyCmpCircuit_size w_k w_p
    exact le_trans hs (Nat.mul_le_mul_left _ (by omega))
  have h2 : sortTraceSize d * ((20 * w_k + 1) + 7 * (w_k + w_p) + 1) ≤
      sortTraceSize d * (27 * (w_k + w_p + 1)) := by
    refine Nat.mul_le_mul_left _ (by omega)
  have htr_le : sortTraceSize d ≤ 2 ^ d * (d + 1) ^ 2 := by
    have ht := four_mul_sortTraceSize d
    have hle1 : d * (d + 1) ≤ (d + 1) ^ 2 := by nlinarith
    have hle2 : d * (d + 1) * 2 ^ d ≤ (d + 1) ^ 2 * 2 ^ d := Nat.mul_le_mul_right _ hle1
    rw [Nat.mul_comm ((d + 1) ^ 2) (2 ^ d)] at hle2
    omega
  have htr_real : (sortTraceSize d : ℝ) ≤ (2 ^ d : ℝ) * ((d + 1 : ℝ) ^ 2) := by
    exact_mod_cast htr_le
  have hnat : (bitonicSortKeyCircuit d w_k w_p asc).size ≤
      sortTraceSize d * (27 * (w_k + w_p + 1)) := le_trans h1 h2
  have hreal : ((bitonicSortKeyCircuit d w_k w_p asc).size : ℝ) ≤
      (sortTraceSize d : ℝ) * (27 * (w_k + w_p + 1 : ℝ)) := by exact_mod_cast hnat
  nlinarith

lemma act_bitonicSortKeyCircuit_ket (d w_k w_p : ℕ) (asc : Bool)
    (x : Fin (arity d) → Qubits (w_k + w_p)) :
    act (bitonicSortKeyCircuit d w_k w_p asc).unitary
        (ket (packDTA54 (arity d) (w_k + w_p) (sortTraceSize d) w_k x (fun _ => false))) =
      ket (packDTA54 (arity d) (w_k + w_p) (sortTraceSize d) w_k
        (sort (fun r => bitsToNat (recKey54 r)) d asc x)
        (sortTrace (fun r => bitsToNat (recKey54 r)) d asc x)) :=
  act_sortWithTraceGen_ket d (w_k + w_p) w_k (fun r => bitsToNat (recKey54 r))
    (keyCmpCircuit w_k w_p) (keyCmpCircuit_implements w_k w_p) asc x

lemma act_bitonicSortKeyCircuit_adj_unroute (d w_k w_p : ℕ) (asc : Bool)
    (k_in : Fin (arity d) → Qubits w_k) (y_p : Fin (arity d) → Qubits w_p) :
    act (bitonicSortKeyCircuit d w_k w_p asc).adj.unitary
        (ket (packDTA54 (arity d) (w_k + w_p) (sortTraceSize d) w_k
          (fun i => Fin.append (sort bitsToNat d asc k_in i) (y_p i))
          (sortTrace bitsToNat d asc k_in))) =
      ket (packDTA54 (arity d) (w_k + w_p) (sortTraceSize d) w_k
        (fun i => Fin.append (k_in i) (unrouteSort d (sortTrace bitsToNat d asc k_in) y_p i))
        (fun _ => false)) :=
  sortWithTraceGen_adj_unroute d w_k w_p w_k bitsToNat
    (keyCmpCircuit w_k w_p) (keyCmpCircuit_implements w_k w_p) asc k_in y_p

/-! ### Piece 3: Classical-`m` Uniform Prefix State Preparation (`unifPrefixCircuit`) -/

private lemma bitsToNat_natToBits {q k : ℕ} (hk : k < 2 ^ q) :
    bitsToNat (natToBits q k) = k := by
  rw [← bitsEquivFin_apply]
  simp [natToBits, Nat.mod_eq_of_lt hk]

private lemma natToBits_bitsToNat {q : ℕ} (b : Qubits q) :
    natToBits q (bitsToNat b) = b := by
  have hlt : bitsToNat b < 2 ^ q := by
    rw [← bitsEquivFin_apply]
    exact (bitsEquivFin q b).isLt
  apply (bitsEquivFin q).injective
  ext
  rw [bitsEquivFin_apply, bitsToNat_natToBits hlt]
  exact (bitsEquivFin_apply b).symm

private lemma bitsToNat_cons {b : ℕ} (c : Bool) (u : Qubits b) :
    bitsToNat (Fin.cons (α := fun _ => Bool) c u) = (if c then 2 ^ b else 0) + bitsToNat u := by
  simp only [bitsToNat, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : i.1 < b := i.isLt
  have he : b - (i.1 + 1) = b - 1 - i.1 := by omega
  simp [he]

private lemma natToBits_succ_lt {b d : ℕ} (hd : d < 2 ^ b) :
    natToBits (b + 1) d = Fin.cons (α := fun _ => Bool) false (natToBits b d) := by
  have hbt : bitsToNat (Fin.cons (α := fun _ => Bool) false (natToBits b d)) = d := by
    simp only [bitsToNat_cons, Bool.false_eq_true, ↓reduceIte, zero_add, bitsToNat_natToBits hd]
  conv_lhs => rw [← hbt]
  exact natToBits_bitsToNat (Fin.cons (α := fun _ => Bool) false (natToBits b d))

private lemma natToBits_succ_ge {b d : ℕ} (hd : d < 2 ^ b) :
    natToBits (b + 1) (2 ^ b + d) = Fin.cons (α := fun _ => Bool) true (natToBits b d) := by
  have hbt : bitsToNat (Fin.cons (α := fun _ => Bool) true (natToBits b d)) = 2 ^ b + d := by
    simp only [bitsToNat_cons, ↓reduceIte, bitsToNat_natToBits hd]
  conv_lhs => rw [← hbt]
  exact natToBits_bitsToNat (Fin.cons (α := fun _ => Bool) true (natToBits b d))

noncomputable def rotMat54 (a c : ℕ) : Matrix Bool Bool ℂ :=
  if _h : 1 ≤ a then
    let s : ℝ := Real.sqrt ((a + c : ℕ) : ℝ)
    let ca : ℂ := ((Real.sqrt (a : ℝ) / s : ℝ) : ℂ)
    let sc : ℂ := ((Real.sqrt (c : ℝ) / s : ℝ) : ℂ)
    Matrix.of fun r col => match r, col with
      | false, false => ca
      | false, true  => -sc
      | true,  false => sc
      | true,  true  => ca
  else 1

private lemma rotMat54_mem_unitaryGroup (a c : ℕ) :
    rotMat54 a c ∈ Matrix.unitaryGroup Bool ℂ := by
  by_cases ha : 1 ≤ a
  · rw [Matrix.mem_unitaryGroup_iff']
    dsimp only [rotMat54]
    rw [dif_pos ha]
    have hpos : (0 : ℝ) < ((a + c : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < a + c)
    have hs_ne : Real.sqrt ((a + c : ℕ) : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    have hsq_sum : (Real.sqrt (a : ℝ) / Real.sqrt ((a + c : ℕ) : ℝ)) ^ 2 +
        (Real.sqrt (c : ℝ) / Real.sqrt ((a + c : ℕ) : ℝ)) ^ 2 = 1 := by
      have ha_nn : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
      have hc_nn : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
      rw [div_pow, div_pow, ← add_div, Real.sq_sqrt ha_nn, Real.sq_sqrt hc_nn,
        Real.sq_sqrt (le_of_lt hpos)]
      have hcast : ((a : ℝ) + (c : ℝ)) = ((a + c : ℕ) : ℝ) := by push_cast; rfl
      rw [hcast, div_self hpos.ne']
    ext i j
    simp only [Matrix.mul_apply, Matrix.star_apply, Fintype.sum_bool, Matrix.one_apply]
    cases i <;> cases j <;> simp only [Matrix.of_apply, star_neg, Bool.false_eq_true,
      Bool.true_eq_false, ↓reduceIte]
    · simp only [RCLike.star_def, Complex.conj_ofReal]
      norm_cast
      simpa only [div_eq_mul_inv, sq, mul_comm, add_comm] using hsq_sum
    · simp only [RCLike.star_def, Complex.conj_ofReal]
      norm_cast; ring
    · simp only [RCLike.star_def, Complex.conj_ofReal]
      norm_cast; ring
    · simp only [RCLike.star_def, Complex.conj_ofReal]
      norm_cast
      simpa only [div_eq_mul_inv, sq, mul_comm, neg_mul_neg] using hsq_sum
  · simp only [rotMat54, dif_neg ha]; exact one_mem _

private lemma act_ctrlHadamardN_false (n : ℕ) (v : Qubits n) :
    act (ctrlHadamardN n).unitary (ket (padZero (1 + n) n (Fin.append (fun _ : Fin 1 => false) v))) =
      ket (padZero (1 + n) n (Fin.append (fun _ : Fin 1 => false) v)) := by
  let z₀ : Qubits (1 + n) := Fin.append (fun _ : Fin 1 => false) v
  have hz0 : z₀ ((0 : Fin (n + 1)).cast (Nat.add_comm n 1)) = false := by
    change z₀ (Fin.castAdd n (0 : Fin 1)) = false
    simp [z₀, Fin.append_left]
  rw [act_ket_of_implementsOnClean (ctrlHadamardN_implements n) z₀]
  rw [Finset.sum_eq_single z₀]
  · have hmat : ctrlHadamardMat n z₀ z₀ = 1 := by
      dsimp only [ctrlHadamardMat, controlledQubits, controlled, Matrix.of_apply, Matrix.submatrix_apply]
      rw [if_pos rfl, hz0]; simp
    rw [hmat, one_smul]
  · intro y _ hy
    have hmat : ctrlHadamardMat n y z₀ = 0 := by
      dsimp only [ctrlHadamardMat, controlledQubits, controlled, Matrix.of_apply, Matrix.submatrix_apply]
      by_cases hy0 : y ((0 : Fin (n + 1)).cast (Nat.add_comm n 1)) =
          z₀ ((0 : Fin (n + 1)).cast (Nat.add_comm n 1))
      · simp only [hy0, hz0, Bool.false_eq_true, ↓reduceIte, Matrix.one_apply]
        rw [if_neg]
        intro htail; apply hy; funext k
        cases k using Fin.addCases with
        | left i =>
          have hi0 : i = 0 := Fin.ext (by have := i.isLt; omega)
          subst hi0
          exact hy0
        | right j =>
          have ht := congrFun htail j
          simp only [Fin.tail] at ht
          have heq : (Fin.cast (Nat.add_comm n 1) j.succ : Fin (1 + n)) = Fin.natAdd 1 j :=
            Fin.ext (by simp [Nat.add_comm])
          simpa only [heq] using ht
      · rw [if_neg hy0]
    rw [hmat, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma act_ctrlHadamardN_true_zero (n : ℕ) :
    act (ctrlHadamardN n).unitary
        (ket (padZero (1 + n) n (Fin.append (fun _ : Fin 1 => true) (fun _ : Fin n => false)))) =
      ((1 / Real.sqrt ((2 ^ n : ℕ) : ℝ) : ℝ) : ℂ) •
        ∑ d : Fin (2 ^ n), ket (padZero (1 + n) n (Fin.append (fun _ : Fin 1 => true) (natToBits n d.val))) := by
  let z₀ : Qubits (1 + n) := Fin.append (fun _ : Fin 1 => true) (fun _ : Fin n => false)
  rw [act_ket_of_implementsOnClean (ctrlHadamardN_implements n) z₀]
  have hsplit : (∑ y : Qubits (1 + n), ctrlHadamardMat n y z₀ • ket (padZero (1 + n) n y)) =
      ∑ u : Qubits n, ctrlHadamardMat n (Fin.append (fun _ : Fin 1 => true) u) z₀ •
        ket (padZero (1 + n) n (Fin.append (fun _ : Fin 1 => true) u)) := by
    let e : Qubits n ↪ Qubits (1 + n) :=
      ⟨fun u => Fin.append (fun _ : Fin 1 => true) u, fun u₁ u₂ h => by
        funext j
        have := congrFun h (Fin.natAdd 1 j)
        simpa [Fin.append_right] using this⟩
    have he_apply : ∀ u : Qubits n, e u = Fin.append (fun _ : Fin 1 => true) u := fun _ => rfl
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e))]
    · rw [Finset.sum_image (fun u₁ _ u₂ _ h => e.injective h)]
      rfl
    · intro y _ hy
      have hy0 : y ((0 : Fin (n + 1)).cast (Nat.add_comm n 1)) = false := by
        cases h0 : y ((0 : Fin (n + 1)).cast (Nat.add_comm n 1)) with
        | false => rfl
        | true =>
          exfalso; apply hy; rw [Finset.mem_image]
          refine ⟨fun j => y (Fin.natAdd 1 j), Finset.mem_univ _, ?_⟩
          funext k; cases k using Fin.addCases with
          | left i =>
            have hi0 : i = 0 := Fin.ext (by have := i.isLt; omega)
            subst hi0
            rw [he_apply, Fin.append_left]
            change true = y ((0 : Fin (n + 1)).cast (Nat.add_comm n 1))
            exact h0.symm
          | right j => rw [he_apply, Fin.append_right]
      have hz0 : z₀ ((0 : Fin (n + 1)).cast (Nat.add_comm n 1)) = true := by
        change z₀ (Fin.castAdd n (0 : Fin 1)) = true
        simp [z₀, Fin.append_left]
      have hmat : ctrlHadamardMat n y z₀ = 0 := by
        dsimp only [ctrlHadamardMat, controlledQubits, controlled, Matrix.of_apply, Matrix.submatrix_apply]
        rw [if_neg (by rw [hy0, hz0]; decide)]
      rw [hmat, zero_smul]
  rw [hsplit]
  have hterm : ∀ u : Qubits n,
      ctrlHadamardMat n (Fin.append (fun _ : Fin 1 => true) u) z₀ =
        ((1 / Real.sqrt ((2 ^ n : ℕ) : ℝ) : ℝ) : ℂ) := fun u => by
    dsimp only [ctrlHadamardMat, controlledQubits, controlled, Matrix.of_apply, Matrix.submatrix_apply]
    have hy0 : (Fin.append (fun _ : Fin 1 => true) u) ((0 : Fin (n + 1)).cast (Nat.add_comm n 1)) = true := by
      change (Fin.append (fun _ : Fin 1 => true) u) (Fin.castAdd n 0) = true
      simp [Fin.append_left]
    have hz0 : z₀ ((0 : Fin (n + 1)).cast (Nat.add_comm n 1)) = true := by
      change z₀ (Fin.castAdd n 0) = true
      simp [z₀, Fin.append_left]
    rw [if_pos (hy0.trans hz0.symm), if_pos hy0]
    have htail_z : Fin.tail (fun i : Fin (n + 1) => z₀ (i.cast (Nat.add_comm n 1))) = fun _ => false := by
      funext j
      simp only [Fin.tail]
      have hj : (Fin.cast (Nat.add_comm n 1) j.succ : Fin (1 + n)) = Fin.natAdd 1 j :=
        Fin.ext (by simp [Nat.add_comm])
      rw [hj]; simp [z₀, Fin.append_right]
    have hdot : dotBits (Fin.tail (fun i : Fin (n + 1) => z₀ (i.cast (Nat.add_comm n 1))))
        (Fin.tail (fun i : Fin (n + 1) => (Fin.append (fun _ : Fin 1 => true) u) (i.cast (Nat.add_comm n 1)))) =
        false := by
      rw [htail_z]; unfold dotBits; simp only [Bool.false_and]
      exact Finset.sum_const_zero
    simp only [hadamardN, Matrix.of_apply, hdot, Bool.false_eq_true, ↓reduceIte]
    congr 1
    have hsqrt : Real.sqrt ((2 ^ n : ℕ) : ℝ) = (Real.sqrt 2) ^ n :=
      (Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)).mpr (by
        rw [← pow_add, ← two_mul, pow_mul, Real.sq_sqrt (by norm_num), Nat.cast_pow, Nat.cast_ofNat])
    rw [hsqrt, one_div, inv_pow]
  simp_rw [hterm]
  rw [← Finset.smul_sum]
  congr 1
  let eqv : Fin (2 ^ n) ≃ Qubits n :=
    { toFun := fun d => natToBits n d.val
      invFun := fun u => ⟨bitsToNat u, by rw [← bitsEquivFin_apply]; exact (bitsEquivFin n u).isLt⟩
      left_inv := fun d => Fin.ext (bitsToNat_natToBits d.isLt)
      right_inv := fun u => natToBits_bitsToNat u }
  exact (Fintype.sum_equiv eqv _ _ (fun _ => rfl)).symm

private def unifSubEmb (b : ℕ) : Fin ((1 + b) + b) ↪ Fin ((1 + (b + 1)) + (b + 1)) where
  toFun u :=
    if u.1 = 0 then ⟨0, by omega⟩
    else if u.1 < 1 + b then ⟨1 + u.1, by omega⟩
    else ⟨2 + u.1, by have := u.isLt; omega⟩
  inj' x y h := by
    have hx := x.isLt; have hy := y.isLt
    have hv := congrArg Fin.val h
    dsimp only at hv
    by_cases hx0 : x.1 = 0 <;> by_cases hy0 : y.1 = 0
    · exact Fin.ext (by omega)
    · exfalso; by_cases hy1 : y.1 < 1 + b
      · rw [if_pos hx0, if_neg hy0, if_pos hy1] at hv; simp only at hv; omega
      · rw [if_pos hx0, if_neg hy0, if_neg hy1] at hv; simp only at hv; omega
    · exfalso; by_cases hx1 : x.1 < 1 + b
      · rw [if_neg hx0, if_pos hx1, if_pos hy0] at hv; simp only at hv; omega
      · rw [if_neg hx0, if_neg hx1, if_pos hy0] at hv; simp only at hv; omega
    · by_cases hx1 : x.1 < 1 + b <;> by_cases hy1 : y.1 < 1 + b
      · rw [if_neg hx0, if_pos hx1, if_neg hy0, if_pos hy1] at hv; simp only at hv; exact Fin.ext (by omega)
      · rw [if_neg hx0, if_pos hx1, if_neg hy0, if_neg hy1] at hv; simp only at hv; omega
      · rw [if_neg hx0, if_neg hx1, if_neg hy0, if_pos hy1] at hv; simp only at hv; omega
      · rw [if_neg hx0, if_neg hx1, if_neg hy0, if_neg hy1] at hv; simp only at hv; exact Fin.ext (by omega)

private lemma unifSubEmb_apply (b : ℕ) (u : Fin ((1 + b) + b)) :
    unifSubEmb b u =
      if u.1 = 0 then ⟨0, by omega⟩
      else if u.1 < 1 + b then ⟨1 + u.1, by omega⟩
      else ⟨2 + u.1, by have := u.isLt; omega⟩ := rfl

private def unifAuxSubEmb (b : ℕ) : Fin ((1 + b) + b) ↪ Fin ((1 + (b + 1)) + (b + 1)) where
  toFun u :=
    if u.1 = 0 then ⟨1 + (b + 1), by omega⟩
    else if u.1 < 1 + b then ⟨1 + u.1, by omega⟩
    else ⟨2 + u.1, by have := u.isLt; omega⟩
  inj' x y h := by
    have hx := x.isLt; have hy := y.isLt
    have hv := congrArg Fin.val h
    dsimp only at hv
    by_cases hx0 : x.1 = 0 <;> by_cases hy0 : y.1 = 0
    · exact Fin.ext (by omega)
    · exfalso; by_cases hy1 : y.1 < 1 + b
      · rw [if_pos hx0, if_neg hy0, if_pos hy1] at hv; simp only at hv; omega
      · rw [if_pos hx0, if_neg hy0, if_neg hy1] at hv; simp only at hv; omega
    · exfalso; by_cases hx1 : x.1 < 1 + b
      · rw [if_neg hx0, if_pos hx1, if_pos hy0] at hv; simp only at hv; omega
      · rw [if_neg hx0, if_neg hx1, if_pos hy0] at hv; simp only at hv; omega
    · by_cases hx1 : x.1 < 1 + b <;> by_cases hy1 : y.1 < 1 + b
      · rw [if_neg hx0, if_pos hx1, if_neg hy0, if_pos hy1] at hv; simp only at hv; exact Fin.ext (by omega)
      · rw [if_neg hx0, if_pos hx1, if_neg hy0, if_neg hy1] at hv; simp only at hv; omega
      · rw [if_neg hx0, if_neg hx1, if_neg hy0, if_pos hy1] at hv; simp only at hv; omega
      · rw [if_neg hx0, if_neg hx1, if_neg hy0, if_neg hy1] at hv; simp only at hv; exact Fin.ext (by omega)

private lemma unifAuxSubEmb_apply (b : ℕ) (u : Fin ((1 + b) + b)) :
    unifAuxSubEmb b u =
      if u.1 = 0 then ⟨1 + (b + 1), by omega⟩
      else if u.1 < 1 + b then ⟨1 + u.1, by omega⟩
      else ⟨2 + u.1, by have := u.isLt; omega⟩ := rfl

private lemma act_unifSubEmb_ket_false (b : ℕ)
    (lc : LayeredCircuit ((1 + b) + b))
    (hlc_false : ∀ v : Qubits b,
      act lc.unitary (ket (padZero (1 + b) b (Fin.append (fun _ : Fin 1 => false) v))) =
        ket (padZero (1 + b) b (Fin.append (fun _ : Fin 1 => false) v)))
    (v : Qubits (b + 1)) :
    act (lc.mapWires (unifSubEmb b)).unitary
        (ket (padZero (1 + (b + 1)) (b + 1) (Fin.append (fun _ : Fin 1 => false) v))) =
      ket (padZero (1 + (b + 1)) (b + 1) (Fin.append (fun _ : Fin 1 => false) v)) := by
  let z := padZero (1 + (b + 1)) (b + 1) (Fin.append (fun _ : Fin 1 => false) v)
  let v' : Qubits b := Fin.tail v
  have hcomp : z ∘ unifSubEmb b = padZero (1 + b) b (Fin.append (fun _ : Fin 1 => false) v') := by
    funext u
    dsimp only [Function.comp_apply, z]
    rw [unifSubEmb_apply]
    by_cases hu0 : u.1 = 0
    · rw [if_pos hu0]
      have hu_eq : u = Fin.castAdd b (Fin.castAdd b (0 : Fin 1)) := Fin.ext hu0
      have hz_eq : (⟨0, by omega⟩ : Fin ((1 + (b + 1)) + (b + 1))) =
          Fin.castAdd (b + 1) (Fin.castAdd (b + 1) (0 : Fin 1)) := Fin.ext rfl
      rw [hz_eq, padZero_castAdd, Fin.append_left]
      conv_rhs => rw [hu_eq, padZero_castAdd, Fin.append_left]
    · by_cases hu1 : u.1 < 1 + b
      · rw [if_neg hu0, if_pos hu1]
        have hu_eq : u = Fin.castAdd b (Fin.natAdd 1 ⟨u.1 - 1, by omega⟩) := by ext; simp; omega
        have hz_eq : (⟨1 + u.1, by omega⟩ : Fin ((1 + (b + 1)) + (b + 1))) =
            Fin.castAdd (b + 1) (Fin.natAdd 1 (Fin.succ ⟨u.1 - 1, by omega⟩)) := by ext; simp; omega
        rw [hz_eq, padZero_castAdd, Fin.append_right]
        conv_rhs => rw [hu_eq, padZero_castAdd, Fin.append_right]
        rfl
      · rw [if_neg hu0, if_neg hu1]
        have hu_eq : u = Fin.natAdd (1 + b) ⟨u.1 - (1 + b), by have := u.isLt; omega⟩ := by
          ext; simp; omega
        have hz_eq : (⟨2 + u.1, by have := u.isLt; omega⟩ : Fin ((1 + (b + 1)) + (b + 1))) =
            Fin.natAdd (1 + (b + 1)) ⟨1 + (u.1 - (1 + b)), by have := u.isLt; omega⟩ := by
          ext; simp; omega
        rw [hz_eq, padZero_natAdd]
        conv_rhs => rw [hu_eq, padZero_natAdd]
  refine act_mapWires_ket lc (unifSubEmb b) z
    (padZero (1 + b) b (Fin.append (fun _ : Fin 1 => false) v'))
    (by rw [hcomp]; exact hlc_false v') z hcomp (fun _ _ => rfl)

private lemma act_unifSubEmb_ket_sum (b : ℕ) {κ : Type*} [Fintype κ]
    (lc : LayeredCircuit ((1 + b) + b)) (α : κ → ℂ) (f : κ → Qubits b)
    (v0 : Qubits b)
    (hlc : act lc.unitary (ket (padZero (1 + b) b (Fin.append (fun _ : Fin 1 => true) v0))) =
      ∑ j : κ, α j • ket (padZero (1 + b) b (Fin.append (fun _ : Fin 1 => true) (f j)))) :
    act (lc.mapWires (unifSubEmb b)).unitary
        (ket (padZero (1 + (b + 1)) (b + 1)
          (Fin.append (fun _ : Fin 1 => true) (Fin.cons (α := fun _ => Bool) false v0)))) =
      ∑ j : κ, α j • ket (padZero (1 + (b + 1)) (b + 1)
        (Fin.append (fun _ : Fin 1 => true) (Fin.cons (α := fun _ => Bool) false (f j)))) := by
  have hcomp : ∀ (w : Qubits b),
      padZero (1 + (b + 1)) (b + 1) (Fin.append (fun _ : Fin 1 => true) (Fin.cons (α := fun _ => Bool) false w)) ∘
        unifSubEmb b = padZero (1 + b) b (Fin.append (fun _ : Fin 1 => true) w) := by
    intro w; funext u
    dsimp only [Function.comp_apply]
    rw [unifSubEmb_apply]
    by_cases hu0 : u.1 = 0
    · rw [if_pos hu0]
      have hu_eq : u = Fin.castAdd b (Fin.castAdd b (0 : Fin 1)) := Fin.ext hu0
      have hz_eq : (⟨0, by omega⟩ : Fin ((1 + (b + 1)) + (b + 1))) =
          Fin.castAdd (b + 1) (Fin.castAdd (b + 1) (0 : Fin 1)) := Fin.ext rfl
      rw [hz_eq, padZero_castAdd, Fin.append_left]
      conv_rhs => rw [hu_eq, padZero_castAdd, Fin.append_left]
    · by_cases hu1 : u.1 < 1 + b
      · rw [if_neg hu0, if_pos hu1]
        have hu_eq : u = Fin.castAdd b (Fin.natAdd 1 ⟨u.1 - 1, by omega⟩) := by ext; simp; omega
        have hz_eq : (⟨1 + u.1, by omega⟩ : Fin ((1 + (b + 1)) + (b + 1))) =
            Fin.castAdd (b + 1) (Fin.natAdd 1 (Fin.succ ⟨u.1 - 1, by omega⟩)) := by ext; simp; omega
        rw [hz_eq, padZero_castAdd, Fin.append_right, Fin.cons_succ]
        conv_rhs => rw [hu_eq, padZero_castAdd, Fin.append_right]
      · rw [if_neg hu0, if_neg hu1]
        have hu_eq : u = Fin.natAdd (1 + b) ⟨u.1 - (1 + b), by have := u.isLt; omega⟩ := by
          ext; simp; omega
        have hz_eq : (⟨2 + u.1, by have := u.isLt; omega⟩ : Fin ((1 + (b + 1)) + (b + 1))) =
            Fin.natAdd (1 + (b + 1)) ⟨1 + (u.1 - (1 + b)), by have := u.isLt; omega⟩ := by
          ext; simp; omega
        rw [hz_eq, padZero_natAdd]
        conv_rhs => rw [hu_eq, padZero_natAdd]
  refine act_mapWires_ket_sum lc (unifSubEmb b) _ α _ _
    (by rw [hcomp v0]; exact hlc) (fun j => hcomp (f j)) ?_
  intro j i hi
  by_cases hi1 : i.1 = 1
  · have hi_eq : i = Fin.castAdd (b + 1) (Fin.natAdd 1 0) := Fin.ext hi1
    rw [hi_eq, padZero_castAdd, Fin.append_right, padZero_castAdd, Fin.append_right,
      Fin.cons_zero, Fin.cons_zero]
  · by_cases hi_aux0 : i.1 = 1 + (b + 1)
    · have hi_eq : i = Fin.natAdd (1 + (b + 1)) 0 := Fin.ext (by simp [hi_aux0])
      rw [hi_eq, padZero_natAdd, padZero_natAdd]
    · exfalso; apply hi
      have hi_lt := i.isLt
      by_cases hi0 : i.1 = 0
      · refine ⟨⟨0, by omega⟩, Fin.ext ?_⟩
        rw [unifSubEmb_apply, if_pos rfl]; exact hi0.symm
      · by_cases hi_mid : i.1 < 1 + (b + 1)
        · refine ⟨⟨i.1 - 1, by omega⟩, Fin.ext ?_⟩
          rw [unifSubEmb_apply, if_neg (by simp; omega), if_pos (by simp; omega)]; simp; omega
        · refine ⟨⟨i.1 - 2, by omega⟩, Fin.ext ?_⟩
          rw [unifSubEmb_apply, if_neg (by simp; omega), if_neg (by simp; omega)]; simp; omega

private lemma act_unifAuxSubEmb_ket_false (b : ℕ)
    (lc : LayeredCircuit ((1 + b) + b))
    (hlc_false : ∀ v : Qubits b,
      act lc.unitary (ket (padZero (1 + b) b (Fin.append (fun _ : Fin 1 => false) v))) =
        ket (padZero (1 + b) b (Fin.append (fun _ : Fin 1 => false) v)))
    (c0 b1 : Bool) (v : Qubits b) :
    act (lc.mapWires (unifAuxSubEmb b)).unitary
        (ket (padZero (1 + (b + 1)) (b + 1)
          (Fin.append (fun _ : Fin 1 => c0) (Fin.cons (α := fun _ => Bool) b1 v)))) =
      ket (padZero (1 + (b + 1)) (b + 1)
        (Fin.append (fun _ : Fin 1 => c0) (Fin.cons (α := fun _ => Bool) b1 v))) := by
  let z := padZero (1 + (b + 1)) (b + 1)
    (Fin.append (fun _ : Fin 1 => c0) (Fin.cons (α := fun _ => Bool) b1 v))
  have hcomp : z ∘ unifAuxSubEmb b = padZero (1 + b) b (Fin.append (fun _ : Fin 1 => false) v) := by
    funext u
    dsimp only [Function.comp_apply, z]
    rw [unifAuxSubEmb_apply]
    by_cases hu0 : u.1 = 0
    · rw [if_pos hu0]
      have hu_eq : u = Fin.castAdd b (Fin.castAdd b (0 : Fin 1)) := Fin.ext hu0
      have hz_eq : (⟨1 + (b + 1), by omega⟩ : Fin ((1 + (b + 1)) + (b + 1))) =
          Fin.natAdd (1 + (b + 1)) 0 := Fin.ext rfl
      rw [hz_eq, padZero_natAdd]
      conv_rhs => rw [hu_eq, padZero_castAdd, Fin.append_left]
    · by_cases hu1 : u.1 < 1 + b
      · rw [if_neg hu0, if_pos hu1]
        have hu_eq : u = Fin.castAdd b (Fin.natAdd 1 ⟨u.1 - 1, by omega⟩) := by ext; simp; omega
        have hz_eq : (⟨1 + u.1, by omega⟩ : Fin ((1 + (b + 1)) + (b + 1))) =
            Fin.castAdd (b + 1) (Fin.natAdd 1 (Fin.succ ⟨u.1 - 1, by omega⟩)) := by ext; simp; omega
        rw [hz_eq, padZero_castAdd, Fin.append_right, Fin.cons_succ]
        conv_rhs => rw [hu_eq, padZero_castAdd, Fin.append_right]
      · rw [if_neg hu0, if_neg hu1]
        have hu_eq : u = Fin.natAdd (1 + b) ⟨u.1 - (1 + b), by have := u.isLt; omega⟩ := by
          ext; simp; omega
        have hz_eq : (⟨2 + u.1, by have := u.isLt; omega⟩ : Fin ((1 + (b + 1)) + (b + 1))) =
            Fin.natAdd (1 + (b + 1)) ⟨1 + (u.1 - (1 + b)), by have := u.isLt; omega⟩ := by
          ext; simp; omega
        rw [hz_eq, padZero_natAdd]
        conv_rhs => rw [hu_eq, padZero_natAdd]
  refine act_mapWires_ket lc (unifAuxSubEmb b) z
    (padZero (1 + b) b (Fin.append (fun _ : Fin 1 => false) v))
    (by rw [hcomp]; exact hlc_false v) z hcomp (fun _ _ => rfl)

private lemma act_unifAuxSubEmb_ket_true_sum (b : ℕ) {κ : Type*} [Fintype κ]
    (lc : LayeredCircuit ((1 + b) + b)) (α : κ → ℂ) (f : κ → Qubits b)
    (c0 b1 : Bool) (v0 : Qubits b)
    (hlc : act lc.unitary (ket (padZero (1 + b) b (Fin.append (fun _ : Fin 1 => true) v0))) =
      ∑ j : κ, α j • ket (padZero (1 + b) b (Fin.append (fun _ : Fin 1 => true) (f j)))) :
    let aux0 : Qubits (1 + (b + 1) + (b + 1)) :=
      Function.update
        (padZero (1 + (b + 1)) (b + 1)
          (Fin.append (fun _ : Fin 1 => c0) (Fin.cons (α := fun _ => Bool) b1 v0)))
        ⟨1 + (b + 1), by omega⟩ true
    act (lc.mapWires (unifAuxSubEmb b)).unitary (ket aux0) =
      ∑ j : κ, α j • ket (Function.update
        (padZero (1 + (b + 1)) (b + 1)
          (Fin.append (fun _ : Fin 1 => c0) (Fin.cons (α := fun _ => Bool) b1 (f j))))
        ⟨1 + (b + 1), by omega⟩ true) := by
  intro aux0
  have hcomp : ∀ w : Qubits b,
      Function.update
        (padZero (1 + (b + 1)) (b + 1)
          (Fin.append (fun _ : Fin 1 => c0) (Fin.cons (α := fun _ => Bool) b1 w)))
        ⟨1 + (b + 1), by omega⟩ true ∘ unifAuxSubEmb b =
      padZero (1 + b) b (Fin.append (fun _ : Fin 1 => true) w) := by
    intro w; funext u
    dsimp only [Function.comp_apply]
    rw [unifAuxSubEmb_apply]
    by_cases hu0 : u.1 = 0
    · rw [if_pos hu0, Function.update_self]
      have hu_eq : u = Fin.castAdd b (Fin.castAdd b (0 : Fin 1)) := Fin.ext hu0
      conv_rhs => rw [hu_eq, padZero_castAdd, Fin.append_left]
    · by_cases hu1 : u.1 < 1 + b
      · rw [if_neg hu0, if_pos hu1,
          Function.update_of_ne (Fin.ne_of_val_ne (by dsimp; omega))]
        have hu_eq : u = Fin.castAdd b (Fin.natAdd 1 ⟨u.1 - 1, by omega⟩) := by ext; simp; omega
        have hz_eq : (⟨1 + u.1, by omega⟩ : Fin ((1 + (b + 1)) + (b + 1))) =
            Fin.castAdd (b + 1) (Fin.natAdd 1 (Fin.succ ⟨u.1 - 1, by omega⟩)) := by ext; simp; omega
        rw [hz_eq, padZero_castAdd, Fin.append_right, Fin.cons_succ]
        conv_rhs => rw [hu_eq, padZero_castAdd, Fin.append_right]
      · rw [if_neg hu0, if_neg hu1,
          Function.update_of_ne (Fin.ne_of_val_ne (by dsimp; omega))]
        have hu_eq : u = Fin.natAdd (1 + b) ⟨u.1 - (1 + b), by have := u.isLt; omega⟩ := by
          ext; simp; omega
        have hz_eq : (⟨2 + u.1, by have := u.isLt; omega⟩ : Fin ((1 + (b + 1)) + (b + 1))) =
            Fin.natAdd (1 + (b + 1)) ⟨1 + (u.1 - (1 + b)), by have := u.isLt; omega⟩ := by
          ext; simp; omega
        rw [hz_eq, padZero_natAdd]
        conv_rhs => rw [hu_eq, padZero_natAdd]
  refine act_mapWires_ket_sum lc (unifAuxSubEmb b) aux0 α _ _
    (by dsimp only [aux0]; rw [hcomp v0]; exact hlc) (fun j => hcomp (f j)) ?_
  intro j i hi
  by_cases hi0 : i.1 = 0
  · have hne : i ≠ ⟨1 + (b + 1), by omega⟩ := Fin.ne_of_val_ne (by dsimp; omega)
    dsimp only [aux0]
    rw [Function.update_of_ne hne, Function.update_of_ne hne]
    have hi_eq : i = Fin.castAdd (b + 1) (Fin.castAdd (b + 1) (0 : Fin 1)) := Fin.ext hi0
    rw [hi_eq, padZero_castAdd, Fin.append_left, padZero_castAdd, Fin.append_left]
  · by_cases hi1 : i.1 = 1
    · have hne : i ≠ ⟨1 + (b + 1), by omega⟩ := Fin.ne_of_val_ne (by dsimp; omega)
      dsimp only [aux0]
      rw [Function.update_of_ne hne, Function.update_of_ne hne]
      have hi_eq : i = Fin.castAdd (b + 1) (Fin.natAdd 1 0) := Fin.ext hi1
      rw [hi_eq, padZero_castAdd, Fin.append_right, padZero_castAdd, Fin.append_right,
        Fin.cons_zero, Fin.cons_zero]
    · exfalso; apply hi
      have hi_lt := i.isLt
      by_cases hi_aux : i.1 = 1 + (b + 1)
      · refine ⟨⟨0, by omega⟩, Fin.ext ?_⟩
        rw [unifAuxSubEmb_apply, if_pos rfl]; exact hi_aux.symm
      · by_cases hi_mid : i.1 < 1 + (b + 1)
        · refine ⟨⟨i.1 - 1, by omega⟩, Fin.ext ?_⟩
          rw [unifAuxSubEmb_apply, if_neg (by simp; omega), if_pos (by simp; omega)]; simp; omega
        · refine ⟨⟨i.1 - 2, by omega⟩, Fin.ext ?_⟩
          rw [unifAuxSubEmb_apply, if_neg (by simp; omega), if_neg (by simp; omega)]; simp; omega

private noncomputable def comp0Circuit54 {n : ℕ} (cW msbW auxW : Fin n)
    (hc_msb : cW ≠ msbW) (hc_aux : cW ≠ auxW) (hmsb_aux : msbW ≠ auxW) : LayeredCircuit n :=
  (pauliXGate msbW).seq ((toffoliOn cW msbW auxW hc_msb hc_aux hmsb_aux).seq (pauliXGate msbW))

private lemma comp0Circuit54_size {n : ℕ} (cW msbW auxW : Fin n)
    (hc_msb : cW ≠ msbW) (hc_aux : cW ≠ auxW) (hmsb_aux : msbW ≠ auxW) :
    (comp0Circuit54 cW msbW auxW hc_msb hc_aux hmsb_aux).size = 7 := by
  simp [comp0Circuit54]

noncomputable def unifPrefixCircuit :
    (b m : ℕ) → 1 ≤ m → m ≤ 2 ^ b → LayeredCircuit ((1 + b) + b)
  | 0, _, _, _ => LayeredCircuit.id ((1 + 0) + 0)
  | b + 1, m, hm1, hm2 =>
    if hle : m ≤ 2 ^ b then
      (unifPrefixCircuit b m hm1 hle).mapWires (unifSubEmb b)
    else
      let m' := m - 2 ^ b
      have hm1' : 1 ≤ m' := by omega
      have hm2' : m' ≤ 2 ^ b := by rw [pow_succ, mul_two] at hm2; omega
      let cW : Fin ((1 + (b + 1)) + (b + 1)) := ⟨0, by omega⟩
      let msbW : Fin ((1 + (b + 1)) + (b + 1)) := ⟨1, by omega⟩
      let auxW : Fin ((1 + (b + 1)) + (b + 1)) := ⟨1 + (b + 1), by omega⟩
      have hc_msb : cW ≠ msbW := Fin.ne_of_val_ne (by dsimp [cW, msbW]; omega)
      have hc_aux : cW ≠ auxW := Fin.ne_of_val_ne (by dsimp [cW, auxW]; omega)
      have hmsb_aux : msbW ≠ auxW := Fin.ne_of_val_ne (by dsimp [msbW, auxW]; omega)
      let rot := ctrlGate1 (rotMat54 (2 ^ b) m') (rotMat54_mem_unitaryGroup (2 ^ b) m') cW msbW hc_msb
      let comp0 := comp0Circuit54 cW msbW auxW hc_msb hc_aux hmsb_aux
      let had := (ctrlHadamardN b).mapWires (unifAuxSubEmb b)
      let comp1 := toffoliOn cW msbW auxW hc_msb hc_aux hmsb_aux
      let recCirc := (unifPrefixCircuit b m' hm1' hm2').mapWires (unifAuxSubEmb b)
      rot.seq (comp0.seq (had.seq (comp0.seq (comp1.seq (recCirc.seq comp1)))))

lemma unifPrefixCircuit_size (b m : ℕ) (hm1 : 1 ≤ m) (hm2 : m ≤ 2 ^ b) :
    (unifPrefixCircuit b m hm1 hm2).size ≤ 25 * (b + 1) ^ 2 := by
  induction b generalizing m with
  | zero => simp [unifPrefixCircuit]
  | succ b ih =>
    dsimp only [unifPrefixCircuit]
    split_ifs with hle
    · simp only [LayeredCircuit.mapWires_size]
      exact le_trans (ih m hm1 hle) (by gcongr; omega)
    · simp only [LayeredCircuit.seq_size, LayeredCircuit.mapWires_size,
        ctrlGate1_size, comp0Circuit54_size, toffoliOn_size]
      have hH : (ctrlHadamardN b).size ≤ 3 * b := ctrlHadamardN_size b
      have hrec := ih (m - 2 ^ b) (by omega) (by rw [pow_succ, mul_two] at hm2; omega)
      nlinarith

lemma act_unifPrefixCircuit_false (b m : ℕ) (hm1 : 1 ≤ m) (hm2 : m ≤ 2 ^ b) (v : Qubits b) :
    act (unifPrefixCircuit b m hm1 hm2).unitary
        (ket (padZero (1 + b) b (Fin.append (fun _ : Fin 1 => false) v))) =
      ket (padZero (1 + b) b (Fin.append (fun _ : Fin 1 => false) v)) := by
  induction b generalizing m with
  | zero => simp [unifPrefixCircuit, LayeredCircuit.id_unitary, act_one]
  | succ b ih =>
    dsimp only [unifPrefixCircuit]
    split_ifs with hle
    · exact act_unifSubEmb_ket_false b (unifPrefixCircuit b m hm1 hle) (ih m hm1 hle) v
    · let z := padZero (1 + (b + 1)) (b + 1) (Fin.append (fun _ : Fin 1 => false) v)
      let cW : Fin ((1 + (b + 1)) + (b + 1)) := ⟨0, by omega⟩
      let msbW : Fin ((1 + (b + 1)) + (b + 1)) := ⟨1, by omega⟩
      let auxW : Fin ((1 + (b + 1)) + (b + 1)) := ⟨1 + (b + 1), by omega⟩
      have hc_msb : cW ≠ msbW := Fin.ne_of_val_ne (by dsimp [cW, msbW]; omega)
      have hc_aux : cW ≠ auxW := Fin.ne_of_val_ne (by dsimp [cW, auxW]; omega)
      have hmsb_aux : msbW ≠ auxW := Fin.ne_of_val_ne (by dsimp [msbW, auxW]; omega)
      have hzc : z cW = false := by
        change padZero (1 + (b + 1)) (b + 1) (Fin.append (fun _ => false) v)
          (Fin.castAdd (b + 1) (Fin.castAdd (b + 1) 0)) = false
        rw [padZero_castAdd, Fin.append_left]
      have hz_eq : z = padZero (1 + (b + 1)) (b + 1)
          (Fin.append (fun _ : Fin 1 => false) (Fin.cons (α := fun _ => Bool) (v 0) (Fin.tail v))) := by
        dsimp only [z]
        apply congrArg (padZero (1 + (b + 1)) (b + 1))
        apply congrArg (Fin.append (fun _ : Fin 1 => false))
        exact (Fin.cons_self_tail v).symm
      have hrot : act (ctrlGate1 (rotMat54 (2 ^ b) (m - 2 ^ b))
          (rotMat54_mem_unitaryGroup (2 ^ b) (m - 2 ^ b)) cW msbW hc_msb).unitary (ket z) = ket z := by
        simp only [act_ctrlGate1_ket, hzc, Bool.false_eq_true, ↓reduceIte]
        rw [Finset.sum_eq_single (z msbW)]
        · simp [Function.update_eq_self]
        · intro b _ hb; simp [hb]
        · intro h; exact absurd (Finset.mem_univ _) h
      have hcomp1 : act (toffoliOn cW msbW auxW hc_msb hc_aux hmsb_aux).unitary (ket z) = ket z := by
        rw [act_toffoliOn_ket, hzc, Bool.false_and, Bool.xor_false, Function.update_eq_self]
      have hcomp0 : act (comp0Circuit54 cW msbW auxW hc_msb hc_aux hmsb_aux).unitary
          (ket z) = ket z := by
        dsimp only [comp0Circuit54]
        rw [LayeredCircuit.seq_unitary, LayeredCircuit.seq_unitary, act_mul, act_mul,
          act_pauliXGate_ket, act_toffoliOn_ket, Function.update_of_ne hc_msb,
          hzc, Bool.false_and, Bool.xor_false, act_pauliXGate_ket]
        congr 1; funext i
        by_cases him : i = msbW
        · subst him
          simp only [Function.update_apply, ↓reduceIte, hmsb_aux, hmsb_aux.symm, Bool.not_not]
        · by_cases hia : i = auxW
          · subst hia
            simp only [Function.update_apply, ↓reduceIte, hmsb_aux.symm]
          · simp only [Function.update_apply, ↓reduceIte, hia, him]
      have hhad : act ((ctrlHadamardN b).mapWires (unifAuxSubEmb b)).unitary (ket z) = ket z := by
        rw [hz_eq]
        exact act_unifAuxSubEmb_ket_false b (ctrlHadamardN b) (act_ctrlHadamardN_false b)
          false (v 0) (Fin.tail v)
      have hrec : act ((unifPrefixCircuit b (m - 2 ^ b) (by omega)
          (by rw [pow_succ, mul_two] at hm2; omega)).mapWires (unifAuxSubEmb b)).unitary (ket z) = ket z := by
        rw [hz_eq]
        exact act_unifAuxSubEmb_ket_false b _ (ih (m - 2 ^ b) (by omega) _)
          false (v 0) (Fin.tail v)
      rw [LayeredCircuit.seq_unitary, act_mul, hrot,
        LayeredCircuit.seq_unitary, act_mul, hcomp0,
        LayeredCircuit.seq_unitary, act_mul, hhad,
        LayeredCircuit.seq_unitary, act_mul, hcomp0,
        LayeredCircuit.seq_unitary, act_mul, hcomp1,
        LayeredCircuit.seq_unitary, act_mul, hrec, hcomp1]

lemma act_unifPrefixCircuit_true (b m : ℕ) (hm1 : 1 ≤ m) (hm2 : m ≤ 2 ^ b) :
    act (unifPrefixCircuit b m hm1 hm2).unitary
        (ket (padZero (1 + b) b (Fin.append (fun _ : Fin 1 => true) (fun _ : Fin b => false)))) =
      ((1 / Real.sqrt (m : ℝ) : ℝ) : ℂ) •
        ∑ d : Fin m, ket (padZero (1 + b) b (Fin.append (fun _ : Fin 1 => true) (natToBits b d.val))) := by
  induction b generalizing m with
  | zero =>
    have hm_eq : m = 1 := by simp only [pow_zero] at hm2; omega
    subst hm_eq
    simp only [unifPrefixCircuit, LayeredCircuit.id_unitary, act_one, Nat.cast_one, Real.sqrt_one,
      div_one, Complex.ofReal_one, one_smul, Fin.sum_univ_one]
    congr 2; funext i; cases i using Fin.addCases with
    | left a =>
      have : a = 0 := Subsingleton.elim a 0
      subst this; rfl
    | right j => exact Fin.elim0 j
  | succ b ih =>
    dsimp only [unifPrefixCircuit]
    split_ifs with hle
    · have hcons0 : (Fin.cons (α := fun _ => Bool) false (fun _ : Fin b => false)) = fun _ : Fin (b + 1) => false := by
        funext i; cases i using Fin.cases <;> rfl
      rw [← hcons0]
      rw [act_unifSubEmb_ket_sum b (unifPrefixCircuit b m hm1 hle)
        (fun _ : Fin m => ((1 / Real.sqrt (m : ℝ) : ℝ) : ℂ))
        (fun d : Fin m => natToBits b d.val) (fun _ => false)
        (by simpa only [Finset.smul_sum] using ih m hm1 hle)]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      congr 3; rw [natToBits_succ_lt (lt_of_lt_of_le d.isLt hle)]
    · have hlt : 2 ^ b < m := by omega
      set m' := m - 2 ^ b
      have hm1' : 1 ≤ m' := by omega
      have hm2' : m' ≤ 2 ^ b := by rw [pow_succ, mul_two] at hm2; omega
      have hmsum : 2 ^ b + m' = m := by omega
      let z0 := padZero (1 + (b + 1)) (b + 1)
        (Fin.append (fun _ : Fin 1 => true) (fun _ : Fin (b + 1) => false))
      have hz0_cons : z0 = padZero (1 + (b + 1)) (b + 1)
          (Fin.append (fun _ : Fin 1 => true) (Fin.cons (α := fun _ => Bool) false (fun _ : Fin b => false))) := by
        dsimp only [z0]
        apply congrArg (padZero (1 + (b + 1)) (b + 1))
        apply congrArg (Fin.append (fun _ : Fin 1 => true))
        funext i; cases i using Fin.cases <;> rfl
      let cW : Fin ((1 + (b + 1)) + (b + 1)) := ⟨0, by omega⟩
      let msbW : Fin ((1 + (b + 1)) + (b + 1)) := ⟨1, by omega⟩
      let auxW : Fin ((1 + (b + 1)) + (b + 1)) := ⟨1 + (b + 1), by omega⟩
      have hc_msb : cW ≠ msbW := Fin.ne_of_val_ne (by dsimp [cW, msbW]; omega)
      have hc_aux : cW ≠ auxW := Fin.ne_of_val_ne (by dsimp [cW, auxW]; omega)
      have hmsb_aux : msbW ≠ auxW := Fin.ne_of_val_ne (by dsimp [msbW, auxW]; omega)
      let sM : ℝ := Real.sqrt (m : ℝ)
      let s2b : ℝ := Real.sqrt ((2 ^ b : ℕ) : ℝ)
      let sm' : ℝ := Real.sqrt (m' : ℝ)
      let ca : ℂ := ((s2b / sM : ℝ) : ℂ)
      let sc : ℂ := ((sm' / sM : ℝ) : ℂ)
      let ketB : Bool → Qubits b → Qubits (1 + (b + 1) + (b + 1)) := fun bit u =>
        padZero (1 + (b + 1)) (b + 1) (Fin.append (fun _ : Fin 1 => true) (Fin.cons (α := fun _ => Bool) bit u))
      let ketBAux : Bool → Qubits b → Qubits (1 + (b + 1) + (b + 1)) := fun bit u =>
        Function.update (ketB bit u) auxW true
      have hupd_msb : Function.update z0 msbW true = ketB true (fun _ => false) := by
        funext i
        by_cases hi : i = msbW
        · subst hi
          rw [Function.update_self]
          change _ = (padZero (1 + (b + 1)) (b + 1) (Fin.append (fun _ : Fin 1 => true)
            (Fin.cons (α := fun _ => Bool) true (fun _ : Fin b => false)))) (Fin.castAdd (b + 1) (Fin.natAdd 1 0))
          rw [padZero_castAdd, Fin.append_right, Fin.cons_zero]
        · rw [Function.update_of_ne hi, hz0_cons]
          dsimp only [ketB]
          cases i using Fin.addCases with
          | left a =>
            rw [padZero_castAdd, padZero_castAdd]
            cases a using Fin.addCases with
            | left k => rw [Fin.append_left, Fin.append_left]
            | right j =>
              rw [Fin.append_right, Fin.append_right]
              cases j using Fin.cases with
              | zero => exfalso; apply hi; exact Fin.ext rfl
              | succ j' => rfl
          | right k => rw [padZero_natAdd, padZero_natAdd]
      have hrot : act (ctrlGate1 (rotMat54 (2 ^ b) m') (rotMat54_mem_unitaryGroup (2 ^ b) m')
          cW msbW hc_msb).unitary (ket z0) =
          ca • ket (ketB false (fun _ => false)) + sc • ket (ketB true (fun _ => false)) := by
        rw [act_ctrlGate1_ket]
        have hzc : z0 cW = true := by
          change padZero (1 + (b + 1)) (b + 1) (Fin.append (fun _ => true) _)
            (Fin.castAdd (b + 1) (Fin.castAdd (b + 1) 0)) = true
          rw [padZero_castAdd, Fin.append_left]
        have hzm : z0 msbW = false := by
          change padZero (1 + (b + 1)) (b + 1) (Fin.append (fun _ => true) _)
            (Fin.castAdd (b + 1) (Fin.natAdd 1 0)) = false
          rw [padZero_castAdd, Fin.append_right]
        simp only [hzc, ↓reduceIte, Fintype.sum_bool, hzm]
        have hupd_f : Function.update z0 msbW false = ketB false (fun _ => false) := by
          rw [Function.update_eq_self_iff.mpr hzm.symm, hz0_cons]
        rw [hupd_f, hupd_msb]
        have h2b1 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
        have hs_eq : (2 ^ b + m' : ℕ) = m := hmsum
        have hmf : rotMat54 (2 ^ b) m' false false = ca := by
          simp [rotMat54, dif_pos h2b1, hs_eq, ca, s2b, sM]
        have hmt : rotMat54 (2 ^ b) m' true false = sc := by
          simp [rotMat54, dif_pos h2b1, hs_eq, sc, sm', sM]
        rw [hmf, hmt, add_comm (sc • _)]
      have hcomp0_ketB : ∀ (bit : Bool) (u : Qubits b),
          act (comp0Circuit54 cW msbW auxW hc_msb hc_aux hmsb_aux).unitary
            (ket (ketB bit u)) =
            if bit then ket (ketB true u) else ket (ketBAux false u) := fun bit u => by
        dsimp only [comp0Circuit54]
        have hkc : ketB bit u cW = true := by
          change padZero (1 + (b + 1)) (b + 1) _ (Fin.castAdd (b + 1) (Fin.castAdd (b + 1) 0)) = true
          rw [padZero_castAdd, Fin.append_left]
        have hkm : ketB bit u msbW = bit := by
          change padZero (1 + (b + 1)) (b + 1) _ (Fin.castAdd (b + 1) (Fin.natAdd 1 0)) = bit
          rw [padZero_castAdd, Fin.append_right, Fin.cons_zero]
        have hka : ketB bit u auxW = false := by
          change padZero (1 + (b + 1)) (b + 1) _ (Fin.natAdd (1 + (b + 1)) 0) = false
          rw [padZero_natAdd]
        rw [LayeredCircuit.seq_unitary, LayeredCircuit.seq_unitary, act_mul, act_mul,
          act_pauliXGate_ket, act_toffoliOn_ket, Function.update_of_ne hc_msb,
          Function.update_self, Function.update_of_ne hmsb_aux.symm, hkc, hkm, hka,
          act_pauliXGate_ket]
        cases bit
        · simp only [Bool.not_false, Bool.and_true, Bool.false_xor, Bool.false_eq_true, ↓reduceIte]
          congr 1; funext i
          by_cases him : i = msbW
          · subst him
            simp only [ketBAux, Function.update_apply, ↓reduceIte, hmsb_aux, Bool.not_true, hkm]
          · by_cases hia : i = auxW
            · subst hia
              dsimp only [ketBAux]; simp only [Function.update_apply, ↓reduceIte, hmsb_aux.symm]
            · dsimp only [ketBAux]; simp only [Function.update_apply, ↓reduceIte, him, hia]
        · simp only [Bool.not_true, Bool.and_false, Bool.false_xor, ↓reduceIte]
          congr 1; funext i
          by_cases him : i = msbW
          · subst him
            simp only [Function.update_apply, ↓reduceIte, hmsb_aux, Bool.not_false, hkm]
          · by_cases hia : i = auxW
            · subst hia
              simp only [Function.update_apply, ↓reduceIte, hmsb_aux.symm, hka]
            · simp only [Function.update_apply, ↓reduceIte, him, hia]
      have hcomp0_ketBAux : ∀ (u : Qubits b),
          act (comp0Circuit54 cW msbW auxW hc_msb hc_aux hmsb_aux).unitary
            (ket (ketBAux false u)) = ket (ketB false u) := fun u => by
        dsimp only [comp0Circuit54]
        have hkc : ketBAux false u cW = true := by
          dsimp only [ketBAux]; rw [Function.update_of_ne hc_aux]
          change padZero (1 + (b + 1)) (b + 1) _ (Fin.castAdd (b + 1) (Fin.castAdd (b + 1) 0)) = true
          rw [padZero_castAdd, Fin.append_left]
        have hkm : ketBAux false u msbW = false := by
          dsimp only [ketBAux]; rw [Function.update_of_ne hmsb_aux]
          change padZero (1 + (b + 1)) (b + 1) _ (Fin.castAdd (b + 1) (Fin.natAdd 1 0)) = false
          rw [padZero_castAdd, Fin.append_right, Fin.cons_zero]
        have hka : ketBAux false u auxW = true := by dsimp only [ketBAux]; rw [Function.update_self]
        have hkm_B : ketB false u msbW = false := by
          change padZero (1 + (b + 1)) (b + 1) _ (Fin.castAdd (b + 1) (Fin.natAdd 1 0)) = false
          rw [padZero_castAdd, Fin.append_right, Fin.cons_zero]
        have hka_B : ketB false u auxW = false := by
          change padZero (1 + (b + 1)) (b + 1) _ (Fin.natAdd (1 + (b + 1)) 0) = false
          rw [padZero_natAdd]
        rw [LayeredCircuit.seq_unitary, LayeredCircuit.seq_unitary, act_mul, act_mul,
          act_pauliXGate_ket, act_toffoliOn_ket, Function.update_of_ne hc_msb,
          Function.update_self, Function.update_of_ne hmsb_aux.symm, hkc, hkm, hka,
          act_pauliXGate_ket]
        simp only [Bool.not_false, Bool.and_true, Bool.xor_self]
        congr 1; funext i
        by_cases him : i = msbW
        · subst him
          simp only [Function.update_apply, ↓reduceIte, hmsb_aux, Bool.not_true, hkm_B]
        · by_cases hia : i = auxW
          · subst hia
            simp only [Function.update_apply, ↓reduceIte, hmsb_aux.symm, hka_B]
          · dsimp only [ketBAux]; simp only [Function.update_apply, ↓reduceIte, him, hia]
      have hcomp1_ketB : ∀ (bit : Bool) (u : Qubits b),
          act (toffoliOn cW msbW auxW hc_msb hc_aux hmsb_aux).unitary (ket (ketB bit u)) =
            if bit then ket (ketBAux true u) else ket (ketB false u) := fun bit u => by
        have hkc : ketB bit u cW = true := by
          change padZero (1 + (b + 1)) (b + 1) _ (Fin.castAdd (b + 1) (Fin.castAdd (b + 1) 0)) = true
          rw [padZero_castAdd, Fin.append_left]
        have hkm : ketB bit u msbW = bit := by
          change padZero (1 + (b + 1)) (b + 1) _ (Fin.castAdd (b + 1) (Fin.natAdd 1 0)) = bit
          rw [padZero_castAdd, Fin.append_right, Fin.cons_zero]
        have hka : ketB bit u auxW = false := by
          change padZero (1 + (b + 1)) (b + 1) _ (Fin.natAdd (1 + (b + 1)) 0) = false
          rw [padZero_natAdd]
        rw [act_toffoliOn_ket, hkc, hkm, hka]
        cases bit
        · simp only [Bool.and_false, Bool.xor_self, Bool.false_eq_true, ↓reduceIte]
          congr 1; exact Function.update_eq_self_iff.mpr hka.symm
        · simp only [Bool.and_true, Bool.false_xor, ↓reduceIte]; rfl
      have hcomp1_ketBAux : ∀ (u : Qubits b),
          act (toffoliOn cW msbW auxW hc_msb hc_aux hmsb_aux).unitary (ket (ketBAux true u)) =
            ket (ketB true u) := fun u => by
        have hkc : ketBAux true u cW = true := by
          dsimp only [ketBAux]; rw [Function.update_of_ne hc_aux]
          change padZero (1 + (b + 1)) (b + 1) _ (Fin.castAdd (b + 1) (Fin.castAdd (b + 1) 0)) = true
          rw [padZero_castAdd, Fin.append_left]
        have hkm : ketBAux true u msbW = true := by
          dsimp only [ketBAux]; rw [Function.update_of_ne hmsb_aux]
          change padZero (1 + (b + 1)) (b + 1) _ (Fin.castAdd (b + 1) (Fin.natAdd 1 0)) = true
          rw [padZero_castAdd, Fin.append_right, Fin.cons_zero]
        have hka : ketBAux true u auxW = true := by dsimp only [ketBAux]; rw [Function.update_self]
        have hka_B : ketB true u auxW = false := by
          change padZero (1 + (b + 1)) (b + 1) _ (Fin.natAdd (1 + (b + 1)) 0) = false
          rw [padZero_natAdd]
        rw [act_toffoliOn_ket, hkc, hkm, hka]
        simp only [Bool.and_true, Bool.xor_self]
        dsimp only [ketBAux]
        rw [Function.update_idem]
        congr 1; exact Function.update_eq_self_iff.mpr hka_B.symm
      have hhad_zero : act ((ctrlHadamardN b).mapWires (unifAuxSubEmb b)).unitary
          (ket (ketBAux false (fun _ => false))) =
          ((1 / s2b : ℝ) : ℂ) • ∑ d : Fin (2 ^ b), ket (ketBAux false (natToBits b d.val)) := by
        simpa [ketBAux, ketB, auxW, s2b, Finset.smul_sum] using
          act_unifAuxSubEmb_ket_true_sum b (ctrlHadamardN b)
            (fun _ : Fin (2 ^ b) => ((1 / Real.sqrt ((2 ^ b : ℕ) : ℝ) : ℝ) : ℂ))
            (fun d : Fin (2 ^ b) => natToBits b d.val) true false (fun _ => false)
            (by simpa only [Finset.smul_sum] using act_ctrlHadamardN_true_zero b)
      have hhad_true : act ((ctrlHadamardN b).mapWires (unifAuxSubEmb b)).unitary
          (ket (ketB true (fun _ => false))) = ket (ketB true (fun _ => false)) :=
        act_unifAuxSubEmb_ket_false b (ctrlHadamardN b) (act_ctrlHadamardN_false b)
          true true (fun _ => false)
      have hrec_false : ∀ u : Qubits b,
          act ((unifPrefixCircuit b m' hm1' hm2').mapWires (unifAuxSubEmb b)).unitary (ket (ketB false u)) =
            ket (ketB false u) := fun u =>
        act_unifAuxSubEmb_ket_false b _ (act_unifPrefixCircuit_false b m' hm1' hm2') true false u
      have hrec_true : act ((unifPrefixCircuit b m' hm1' hm2').mapWires (unifAuxSubEmb b)).unitary
          (ket (ketBAux true (fun _ => false))) =
          ((1 / sm' : ℝ) : ℂ) • ∑ d : Fin m', ket (ketBAux true (natToBits b d.val)) := by
        simpa [ketBAux, ketB, auxW, sm', Finset.smul_sum] using
          act_unifAuxSubEmb_ket_true_sum b _
            (fun _ : Fin m' => ((1 / Real.sqrt (m' : ℝ) : ℝ) : ℂ))
            (fun d : Fin m' => natToBits b d.val) true true (fun _ => false)
            (by simpa only [Finset.smul_sum] using ih m' hm1' hm2')
      have hs2b_ne : s2b ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast Nat.two_pow_pos b)).ne'
      have hsm'_ne : sm' ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < m'))).ne'
      have hcoeff_a : ca * ((1 / s2b : ℝ) : ℂ) = ((1 / sM : ℝ) : ℂ) := by
        dsimp only [ca]; norm_cast; field_simp [hs2b_ne]
      have hcoeff_c : sc * ((1 / sm' : ℝ) : ℂ) = ((1 / sM : ℝ) : ℂ) := by
        dsimp only [sc]; norm_cast; field_simp [hsm'_ne]
      have hbranch1 : ∀ u : Qubits b,
          act (toffoliOn cW msbW auxW hc_msb hc_aux hmsb_aux).unitary
            (act ((unifPrefixCircuit b m' hm1' hm2').mapWires (unifAuxSubEmb b)).unitary
              (act (toffoliOn cW msbW auxW hc_msb hc_aux hmsb_aux).unitary
                (act (comp0Circuit54 cW msbW auxW hc_msb hc_aux hmsb_aux).unitary
                  (ket (ketBAux false u))))) = ket (ketB false u) := fun u => by
        rw [hcomp0_ketBAux, hcomp1_ketB false]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hrec_false, hcomp1_ketB false]
        simp only [Bool.false_eq_true, ↓reduceIte]
      have hbranch2 :
          act (toffoliOn cW msbW auxW hc_msb hc_aux hmsb_aux).unitary
            (act ((unifPrefixCircuit b m' hm1' hm2').mapWires (unifAuxSubEmb b)).unitary
              (act (toffoliOn cW msbW auxW hc_msb hc_aux hmsb_aux).unitary
                (act (comp0Circuit54 cW msbW auxW hc_msb hc_aux hmsb_aux).unitary
                  (ket (ketB true (fun _ => false)))))) =
            ((1 / sm' : ℝ) : ℂ) • ∑ d : Fin m', ket (ketB true (natToBits b d.val)) := by
        rw [hcomp0_ketB true, if_pos rfl, hcomp1_ketB true, if_pos rfl, hrec_true,
          act_smul, act_sum]
        congr 1
        exact Finset.sum_congr rfl fun d _ => hcomp1_ketBAux (natToBits b d.val)
      have hsum1 :
          (∑ x : Fin (2 ^ b),
            act (toffoliOn cW msbW auxW hc_msb hc_aux hmsb_aux).unitary
              (act ((unifPrefixCircuit b m' hm1' hm2').mapWires (unifAuxSubEmb b)).unitary
                (act (toffoliOn cW msbW auxW hc_msb hc_aux hmsb_aux).unitary
                  (act (comp0Circuit54 cW msbW auxW hc_msb hc_aux hmsb_aux).unitary
                    (ket (ketBAux false (natToBits b x.val))))))) =
            ∑ x : Fin (2 ^ b), ket (ketB false (natToBits b x.val)) :=
        Finset.sum_congr rfl fun x _ => hbranch1 (natToBits b x.val)
      simp only [LayeredCircuit.seq_unitary, act_mul]
      rw [hrot, act_add, act_smul, act_smul, hcomp0_ketB false, hcomp0_ketB true]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [act_add, act_smul, act_smul, hhad_zero, hhad_true]
      simp only [act_add, act_smul, act_sum]
      rw [hsum1, hbranch2]
      rw [smul_smul, smul_smul, hcoeff_a, hcoeff_c, ← smul_add]
      congr 1
      have hcast_eq : ∑ d : Fin m, ket (padZero (1 + (b + 1)) (b + 1)
            (Fin.append (fun _ : Fin 1 => true) (natToBits (b + 1) d.val))) =
          ∑ d : Fin (2 ^ b + m'), ket (padZero (1 + (b + 1)) (b + 1)
            (Fin.append (fun _ : Fin 1 => true) (natToBits (b + 1) d.val))) := by
        let eqv : Fin m ≃ Fin (2 ^ b + m') := Fin.castOrderIso hmsum.symm |>.toEquiv
        exact Fintype.sum_equiv eqv _ _ (fun _ => rfl)
      rw [hcast_eq, Fin.sum_univ_add]
      congr 1
      · refine Finset.sum_congr rfl fun d _ => ?_
        dsimp only [ketB]
        congr 3; rw [Fin.val_castAdd, natToBits_succ_lt d.isLt]
      · refine Finset.sum_congr rfl fun d _ => ?_
        dsimp only [ketB]
        congr 3; rw [Fin.val_natAdd, natToBits_succ_ge (lt_of_lt_of_le d.isLt hm2')]


lemma routeSort_apply {α : Type*} (d : ℕ) (flags : Fin (sortTraceSize d) → Bool)
    (x : Fin (arity d) → α) (i : Fin (arity d)) :
    routeSort d flags x i = x (routeSort d flags id i) := by
  simpa only [Function.comp_id, Function.comp_apply] using
    congrFun (routeSort_comp d flags x id) i

lemma routeSortCircuit_size_real (d w : ℕ) :
    ((routeSortCircuit d w).size : ℝ) ≤
      27 * (2 ^ d : ℝ) * ((d + 1 : ℝ) ^ 2) * (w + 1 : ℝ) := by
  have htr_le : sortTraceSize d ≤ 2 ^ d * (d + 1) ^ 2 := by
    have ht := four_mul_sortTraceSize d
    have hle1 : d * (d + 1) ≤ (d + 1) ^ 2 := by nlinarith
    have hle2 : d * (d + 1) * 2 ^ d ≤ (d + 1) ^ 2 * 2 ^ d := Nat.mul_le_mul_right _ hle1
    rw [Nat.mul_comm ((d + 1) ^ 2) (2 ^ d)] at hle2
    omega
  have hnat : (routeSortCircuit d w).size ≤ 27 * (2 ^ d * (d + 1) ^ 2) * (w + 1) := by
    rw [routeSortCircuit_size]
    calc 7 * w * sortTraceSize d
        ≤ 7 * (w + 1) * (2 ^ d * (d + 1) ^ 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 7 (Nat.le_succ w)) htr_le
      _ ≤ 27 * (2 ^ d * (d + 1) ^ 2) * (w + 1) := by
          have h1 : 7 ≤ 27 := by omega
          calc 7 * (w + 1) * (2 ^ d * (d + 1) ^ 2)
              = 7 * (2 ^ d * (d + 1) ^ 2) * (w + 1) := by ring
            _ ≤ 27 * (2 ^ d * (d + 1) ^ 2) * (w + 1) :=
              Nat.mul_le_mul_right (w + 1) (Nat.mul_le_mul_right _ h1)
  have hreal : ((routeSortCircuit d w).size : ℝ) ≤
      ((27 * (2 ^ d * (d + 1) ^ 2) * (w + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
  push_cast at hreal
  simpa only [mul_assoc] using hreal

lemma unrouteSortCircuit_size_real (d w : ℕ) :
    ((unrouteSortCircuit d w).size : ℝ) ≤
      27 * (2 ^ d : ℝ) * ((d + 1 : ℝ) ^ 2) * (w + 1 : ℝ) := by
  simpa [unrouteSortCircuit, LayeredCircuit.adj_size] using routeSortCircuit_size_real d w

lemma unifPrefixCircuit_size_real (b m : ℕ) (hm1 : 1 ≤ m) (hm2 : m ≤ 2 ^ b) :
    ((unifPrefixCircuit b m hm1 hm2).size : ℝ) ≤ 25 * ((b + 1 : ℝ) ^ 2) := by
  have h : ((unifPrefixCircuit b m hm1 hm2).size : ℝ) ≤ ((25 * (b + 1) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast unifPrefixCircuit_size b m hm1 hm2
  push_cast at h
  exact h

lemma act_unifPrefixCircuit_adj_false (b m : ℕ) (hm1 : 1 ≤ m) (hm2 : m ≤ 2 ^ b) (v : Qubits b) :
    act (unifPrefixCircuit b m hm1 hm2).adj.unitary
        (ket (padZero (1 + b) b (Fin.append (fun _ : Fin 1 => false) v))) =
      ket (padZero (1 + b) b (Fin.append (fun _ : Fin 1 => false) v)) := by
  have hf := act_unifPrefixCircuit_false b m hm1 hm2 v
  conv_lhs => rw [← hf]
  rw [← act_mul, LayeredCircuit.adj_unitary,
    Matrix.mem_unitaryGroup_iff'.mp (unifPrefixCircuit b m hm1 hm2).unitary_mem_unitaryGroup, act_one]

lemma act_unifPrefixCircuit_adj_true (b m : ℕ) (hm1 : 1 ≤ m) (hm2 : m ≤ 2 ^ b) :
    act (unifPrefixCircuit b m hm1 hm2).adj.unitary
        (((1 / Real.sqrt (m : ℝ) : ℝ) : ℂ) •
          ∑ d : Fin m, ket (padZero (1 + b) b (Fin.append (fun _ : Fin 1 => true) (natToBits b d.val)))) =
      ket (padZero (1 + b) b (Fin.append (fun _ : Fin 1 => true) (fun _ : Fin b => false))) := by
  have ht := act_unifPrefixCircuit_true b m hm1 hm2
  conv_lhs => rw [← ht]
  rw [← act_mul, LayeredCircuit.adj_unitary,
    Matrix.mem_unitaryGroup_iff'.mp (unifPrefixCircuit b m hm1 hm2).unitary_mem_unitaryGroup, act_one]

end BitonicSol54


open QuantumLTF.Membership.Supplement

theorem solution : Nonempty QuantumLTF.Membership.Supplement.BitonicRouting54 := by
  refine ⟨{
    C_sort := 27
    hC_sort_pos := by norm_num
    C_unif := 25
    hC_unif_pos := by norm_num
    sort_perm := fun key d asc x => BitonicSol54.sort_perm key d asc x
    sort_sorted := fun key d asc x => BitonicSol54.sort_sorted key d asc x
    monotone_sort := fun key d x => BitonicSol54.monotone_sort key d x
    antitone_sort := fun key d x => BitonicSol54.antitone_sort key d x
    unrouteSort_routeSort := fun d flags x => BitonicSol54.unrouteSort_routeSort d flags x
    routeSort_unrouteSort := fun d flags x => BitonicSol54.routeSort_unrouteSort d flags x
    routeSort_sortTrace := fun key d asc x => BitonicSol54.routeSort_sortTrace key d asc x
    routeSort_comp := fun d flags f x => BitonicSol54.routeSort_comp d flags f x
    unrouteSort_comp := fun d flags f x => BitonicSol54.unrouteSort_comp d flags f x
    unrouteSort_comp_sort := fun key d asc f x => BitonicSol54.unrouteSort_comp_sort key d asc f x
    routeSort_apply := fun d flags x i => BitonicSol54.routeSort_apply d flags x i
    unrouteSort_apply := fun d flags x i => BitonicSol54.unrouteSort_apply d flags x i
    unrouteSort_rel_sort := fun key d asc x y R h i => BitonicSol54.unrouteSort_rel_sort key d asc x y R h i
    two_mul_mergeTraceSize := BitonicSol54.two_mul_mergeTraceSize
    four_mul_sortTraceSize := BitonicSol54.four_mul_sortTraceSize
    sort_of_key_comp := fun key0 f d asc x => BitonicSol54.sort_of_key_comp key0 f d asc x
    sortTrace_of_key_comp := fun key0 f d asc x => BitonicSol54.sortTrace_of_key_comp key0 f d asc x
    ltBitsCircuit := BitonicSol54.ltBitsCircuit
    ltBitsCircuit_size := BitonicSol54.ltBitsCircuit_size
    ltBitsCircuit_implements := BitonicSol54.ltBitsCircuit_implements
    cswapRegCircuit := BitonicSol54.cswapRegCircuit
    cswapRegCircuit_size := BitonicSol54.cswapRegCircuit_size
    cswapRegCircuit_implements := BitonicSol54.cswapRegCircuit_implements
    routeSortCircuit := BitonicSol54.routeSortCircuit
    routeSortCircuit_size_nat := BitonicSol54.routeSortCircuit_size
    routeSortCircuit_size := BitonicSol54.routeSortCircuit_size_real
    act_routeSortCircuit_ket := BitonicSol54.act_routeSortCircuit_ket
    unrouteSortCircuit := BitonicSol54.unrouteSortCircuit
    unrouteSortCircuit_eq_adj := fun _ _ => rfl
    unrouteSortCircuit_size_nat := BitonicSol54.unrouteSortCircuit_size
    unrouteSortCircuit_size := BitonicSol54.unrouteSortCircuit_size_real
    act_unrouteSortCircuit_ket := BitonicSol54.act_unrouteSortCircuit_ket
    sortWithTraceCircuit := BitonicSol54.sortWithTraceGen
    sortWithTraceCircuit_size_nat := BitonicSol54.sortWithTraceGen_size
    act_sortWithTraceCircuit_ket := fun {κ} [LinearOrder κ] d w_r anc_cmp key cmp hcmp asc x =>
      BitonicSol54.act_sortWithTraceGen_ket d w_r anc_cmp key cmp hcmp asc x
    sortWithTraceCircuit_adj_unroute := fun {κ} [LinearOrder κ] d w_k w_p anc_cmp key0 cmp hcmp asc k_in y_p =>
      BitonicSol54.sortWithTraceGen_adj_unroute d w_k w_p anc_cmp key0 cmp hcmp asc k_in y_p
    bitonicSortKeyCircuit := BitonicSol54.bitonicSortKeyCircuit
    bitonicSortKeyCircuit_size := BitonicSol54.bitonicSortKeyCircuit_size
    act_bitonicSortKeyCircuit_ket := BitonicSol54.act_bitonicSortKeyCircuit_ket
    act_bitonicSortKeyCircuit_adj_unroute := BitonicSol54.act_bitonicSortKeyCircuit_adj_unroute
    unifPrefixCircuit := BitonicSol54.unifPrefixCircuit
    unifPrefixCircuit_size := BitonicSol54.unifPrefixCircuit_size_real
    act_unifPrefixCircuit_false := BitonicSol54.act_unifPrefixCircuit_false
    act_unifPrefixCircuit_true := BitonicSol54.act_unifPrefixCircuit_true
    act_unifPrefixCircuit_adj_false := BitonicSol54.act_unifPrefixCircuit_adj_false
    act_unifPrefixCircuit_adj_true := BitonicSol54.act_unifPrefixCircuit_adj_true
  }⟩
