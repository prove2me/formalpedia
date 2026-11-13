-- Prove2me | solution 1 for PinwheelDensity.ExactRange.lemma_B_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:51:39.871102+00:00
-- url     : https://prove2.me/submissions/fffd4077-b0a1-4a6b-92d7-29e623d7a850

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_Schedulable
import Definitions.Def_PinwheelDensity_ExactRange_cellOf
import Definitions.Def_PinwheelDensity_ExactRange_checkRun
import Theorems.Thm_PinwheelDensity_ExactRange_lemma_B_1

section
set_option autoImplicit false

namespace PinwheelDensity.ExactRange.Dev.FoldAux

open PinwheelDensity.ExactRange

/-- `toQ` as a plain `List.map` (the coercion in the definition elaborates through a monad lift). -/
theorem toQ_eq (A : List ℕ) : toQ A = A.map (fun a : ℕ => ((a : ℕ) : ℚ)) := by
  induction A with
  | nil => rfl
  | cons a l ih =>
    have : toQ (a :: l) = (a : ℚ) :: toQ l := by simp [toQ]
    rw [this, ih]; rfl

/-! ### Counting executions -/

/-! ### Lemma A.2 / A.3: relabeling, deletion, monotonicity -/

/-! ### Lemma A.4: the pair fold -/

/-! ### Lemma A.5: sorting is monotone -/

theorem sortQ_perm (l : List ℚ) : (sortQ l).Perm l := List.perm_insertionSort _ l

theorem sortQ_sorted (l : List ℚ) : (sortQ l).Pairwise (· ≤ ·) :=
  List.pairwise_insertionSort _ l

/-! ### Lemma A.6: folding preserves order -/

/-! ### Corollary A.7: domination certificates -/

end PinwheelDensity.ExactRange.Dev.FoldAux
end

section
set_option autoImplicit false

namespace PinwheelDensity.ExactRange.Dev.FoldDown

open PinwheelDensity.ExactRange PinwheelDensity.ExactRange.Dev.FoldAux

/-! ### Equations and induction principle for `foldDown` -/

theorem fd_nil (θ : ℚ) : foldDown θ [] = [] := by simp [foldDown]

theorem fd_le {θ x : ℚ} (l : List ℚ) (h : x ≤ θ) : foldDown θ (x :: l) = x :: l := by
  rw [foldDown.eq_def]; simp [h]

theorem fd_single {θ x : ℚ} (h : θ < x) : foldDown θ [x] = [θ] := by
  rw [foldDown.eq_def]; simp [not_le.mpr h]

theorem fd_clamp {θ x y : ℚ} (l : List ℚ) (hx : θ < x) (hy : y ≤ θ) :
    foldDown θ (x :: y :: l) = θ :: y :: l := by
  rw [foldDown.eq_def]; simp [not_le.mpr hx, hy]

theorem fd_step {θ x y : ℚ} (l : List ℚ) (hx : θ < x) (hy : θ < y) :
    foldDown θ (x :: y :: l) = foldDown θ (List.orderedInsert (· ≥ ·) (y / 2) l) := by
  rw [foldDown.eq_def]; simp [not_le.mpr hx, not_le.mpr hy]

/-- Induction along the recursion of `foldDown`. -/
theorem foldDown_induct (θ : ℚ) (P : List ℚ → Prop) (h0 : P [])
    (h1 : ∀ x l, x ≤ θ → P (x :: l)) (h2 : ∀ x, θ < x → P [x])
    (h3 : ∀ x y l, θ < x → y ≤ θ → P (x :: y :: l))
    (h4 : ∀ x y l, θ < x → θ < y → P (List.orderedInsert (· ≥ ·) (y / 2) l) → P (x :: y :: l)) :
    ∀ l, P l := by
  intro l
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
    match l with
    | [] => exact h0
    | x :: l' =>
      by_cases hx : x ≤ θ
      · exact h1 x l' hx
      · match l' with
        | [] => exact h2 x (not_le.mp hx)
        | y :: l'' =>
          by_cases hy : y ≤ θ
          · exact h3 x y l'' (not_le.mp hx) hy
          · refine h4 x y l'' (not_le.mp hx) (not_le.mp hy) ?_
            refine ih _ ?_ _ rfl
            simp only [List.length_cons] at hn
            rw [List.orderedInsert_length]; omega

/-! ### Lemma A.8 (a) -/

theorem foldDown_sorted_pos_le {θ : ℚ} (hθ : 0 < θ) :
    ∀ l : List ℚ, l.Pairwise (· ≥ ·) → (∀ x ∈ l, 0 < x) →
      (foldDown θ l).Pairwise (· ≥ ·) ∧ ∀ z ∈ foldDown θ l, 0 < z ∧ z ≤ θ := by
  refine foldDown_induct θ _ ?_ ?_ ?_ ?_ ?_
  · intro _ _; simp [fd_nil]
  · intro x l hx hs hp
    rw [fd_le l hx]
    refine ⟨hs, ?_⟩
    intro z hz
    refine ⟨hp z hz, ?_⟩
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hx
    · exact le_trans (List.rel_of_pairwise_cons hs hz) hx
  · intro x hx _ _
    rw [fd_single hx]
    simp [hθ]
  · intro x y l hx hy hs hp
    rw [fd_clamp l hx hy]
    refine ⟨?_, ?_⟩
    · rw [List.pairwise_cons]
      refine ⟨?_, hs.of_cons⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hy
      · exact le_trans (List.rel_of_pairwise_cons hs.of_cons hb) hy
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨hθ, le_rfl⟩
      · refine ⟨hp z (by simp [hz]), ?_⟩
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hy
        · exact le_trans (List.rel_of_pairwise_cons hs.of_cons hz) hy
  · intro x y l hx hy ih hs hp
    rw [fd_step l hx hy]
    apply ih
    · exact List.Pairwise.orderedInsert _ _ hs.of_cons.of_cons
    · intro z hz
      rcases (List.mem_orderedInsert _).mp hz with rfl | hz
      · have := hp y (by simp); linarith
      · exact hp z (by simp [hz])

/-! ### Lemma A.8 (b) -/

/-! ### Lemma A.8 (c) -/

/-! ### Lemma A.8 (d) -/

/-- Lemma A.8 (d): up to order, `F_θ(l)` consists of the entries of `l` that are `≤ θ`
together with new entries in `(θ/2, θ]`. -/
theorem foldDown_orig {θ : ℚ} (hθ : 0 < θ) :
    ∀ l : List ℚ, l.Pairwise (· ≥ ·) →
      ∃ N : List ℚ, (foldDown θ l).Perm (l.filter (fun z => decide (z ≤ θ)) ++ N) ∧
        ∀ z ∈ N, θ / 2 < z ∧ z ≤ θ := by
  refine foldDown_induct θ _ ?_ ?_ ?_ ?_ ?_
  · intro _; exact ⟨[], by simp [fd_nil], by simp⟩
  · intro x l hx hs
    refine ⟨[], ?_, by simp⟩
    rw [fd_le l hx]
    have : (x :: l).filter (fun z => decide (z ≤ θ)) = x :: l := by
      rw [List.filter_eq_self]
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · simpa using hx
      · simpa using le_trans (List.rel_of_pairwise_cons hs ha) hx
    rw [this]; simp
  · intro x hx _
    refine ⟨[θ], ?_, by intro z hz; simp at hz; subst hz; constructor <;> linarith⟩
    rw [fd_single hx]
    simp [not_le.mpr hx]
  · intro x y l hx hy hs
    refine ⟨[θ], ?_, by intro z hz; simp at hz; subst hz; constructor <;> linarith⟩
    rw [fd_clamp l hx hy]
    have : (x :: y :: l).filter (fun z => decide (z ≤ θ)) = y :: l := by
      simp only [List.filter_cons, not_le.mpr hx, decide_false, Bool.false_eq_true, if_false]
      rw [if_pos (by simpa using hy)]
      congr 1
      rw [List.filter_eq_self]
      intro a ha
      simpa using le_trans (List.rel_of_pairwise_cons hs.of_cons ha) hy
    rw [this]
    exact (List.perm_append_singleton _ _).symm
  · intro x y l hx hy ih hs
    obtain ⟨N0, hN0, hN1⟩ := ih (List.Pairwise.orderedInsert _ _ hs.of_cons.of_cons)
    rw [fd_step l hx hy]
    have hl : (x :: y :: l).filter (fun z => decide (z ≤ θ)) = l.filter (fun z => decide (z ≤ θ)) := by
      simp [List.filter_cons, not_le.mpr hx, not_le.mpr hy]
    have hy2 : θ / 2 < y / 2 := by linarith
    have hperm : ((List.orderedInsert (· ≥ ·) (y / 2) l).filter (fun z => decide (z ≤ θ))).Perm
        ((y / 2 :: l).filter (fun z => decide (z ≤ θ))) :=
      ((List.perm_orderedInsert _ _ _).filter _)
    by_cases hc : y / 2 ≤ θ
    · refine ⟨y / 2 :: N0, ?_, ?_⟩
      · rw [hl]
        refine hN0.trans ((hperm.append_right N0).trans ?_)
        rw [List.filter_cons, if_pos (by simpa using hc)]
        exact (List.perm_middle).symm
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨hy2, hc⟩
        · exact hN1 z hz
    · refine ⟨N0, ?_, hN1⟩
      rw [hl]
      refine hN0.trans ((hperm.append_right N0).trans ?_)
      rw [List.filter_cons, if_neg (by simpa using hc)]

end PinwheelDensity.ExactRange.Dev.FoldDown
end

section
set_option autoImplicit false

namespace PinwheelDensity.ExactRange.Dev.LB5Aux

open PinwheelDensity.ExactRange PinwheelDensity.ExactRange.Dev.FoldAux
  PinwheelDensity.ExactRange.Dev.FoldDown

/-! ### Rounding -/

theorem round_low (θ k : ℕ) (hθ : θ / 2 = k) (z : ℚ) (h : z ≤ k) : roundCell θ z = ⌊z⌋₊ := by
  unfold roundCell; rw [hθ, if_pos h]

theorem round_high (θ k : ℕ) (hθ : θ / 2 = k) (z : ℚ) (h : (k : ℚ) < z) :
    roundCell θ z = ⌈z⌉₊ - 1 := by
  unfold roundCell; rw [hθ, if_neg (not_le.mpr h)]

theorem round_mono (θ k : ℕ) (hθ : θ / 2 = k) {x y : ℚ} (hxy : x ≤ y) :
    roundCell θ x ≤ roundCell θ y := by
  by_cases hx : x ≤ k
  · by_cases hy : y ≤ k
    · rw [round_low θ k hθ x hx, round_low θ k hθ y hy]; exact Nat.floor_le_floor hxy
    · have hy' : (k : ℚ) < y := not_le.mp hy
      rw [round_low θ k hθ x hx, round_high θ k hθ y hy']
      have h1 : ⌊x⌋₊ ≤ k := by
        have := Nat.floor_le_floor hx
        simpa using this
      have h2 : k + 1 ≤ ⌈y⌉₊ := Nat.lt_ceil.mpr hy'
      omega
  · have hx' : (k : ℚ) < x := not_le.mp hx
    have hy' : (k : ℚ) < y := lt_of_lt_of_le hx' hxy
    rw [round_high θ k hθ x hx', round_high θ k hθ y hy']
    have := Nat.ceil_mono hxy
    omega

theorem cell_sorted (θ : ℕ) (A : List ℕ) : (cellOf θ A).Pairwise (· ≤ ·) := by
  unfold cellOf foldOf
  exact (sortQ_sorted _).map _ (fun a b hab => round_mono θ (θ / 2) rfl hab)

end PinwheelDensity.ExactRange.Dev.LB5Aux
end

section
set_option autoImplicit false

namespace PinwheelDensity.ExactRange.Dev.LB2

open PinwheelDensity.ExactRange PinwheelDensity.ExactRange.Dev.FoldAux
  PinwheelDensity.ExactRange.Dev.FoldDown PinwheelDensity.ExactRange.Dev.LB5Aux

/-! ### Completeness of the generic enumerator -/

theorem enum_complete (ok : List ℕ → Bool) (lo hi : ℕ) :
    ∀ (c pref : List ℕ) (fuel : ℕ), c ≠ [] → c.length ≤ fuel → (pref ++ c).Pairwise (· ≤ ·) →
      (∀ x ∈ c, lo ≤ x ∧ x < hi) →
      (∀ k, pref.length < k → k ≤ (pref ++ c).length → ok ((pref ++ c).take k) = true) →
      pref ++ c ∈ enumSorted ok lo hi fuel pref := by
  intro c
  induction c with
  | nil => intro _ _ hne; exact absurd rfl hne
  | cons v c' ih =>
    intro pref fuel _ hlen hsort hrange hok
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hlen; omega⟩
    have hv := hrange v (by simp)
    have hstart : max lo (pref.getLast?.getD lo) ≤ v := by
      refine max_le hv.1 ?_
      cases hl : pref.getLast? with
      | none => simpa using hv.1
      | some w =>
        simp only [Option.getD_some]
        have hw : w ∈ pref := List.mem_of_getLast? hl
        exact (List.pairwise_append.mp hsort).2.2 w hw v (by simp)
    have e : (pref ++ [v]) ++ c' = pref ++ v :: c' := by simp
    have hokp : ok (pref ++ [v]) = true := by
      have := hok (pref.length + 1) (by omega) (by simp)
      rw [← e, List.take_left' (by simp)] at this
      exact this
    simp only [enumSorted]
    rw [List.mem_flatMap]
    refine ⟨v, ?_, ?_⟩
    · rw [List.mem_range'_1]; omega
    · rw [if_pos hokp]
      by_cases hc' : c' = []
      · subst hc'; simp
      · apply List.mem_cons_of_mem
        have := ih (pref ++ [v]) f hc' (by simp at hlen; omega) (by rw [e]; exact hsort)
          (fun x hx => hrange x (List.mem_cons_of_mem _ hx))
          (by rw [e]; intro k hk1 hk2; exact hok k (by simp at hk1; omega) (by simpa using hk2))
        rwa [e] at this

/-! ### Weight -/

theorem weight_append (θ : ℕ) (a b : List ℕ) : weight θ (a ++ b) = weight θ a + weight θ b := by
  unfold weight; rw [List.map_append, List.sum_append]

theorem weight_nonneg (θ : ℕ) (c : List ℕ) : 0 ≤ weight θ c := by
  unfold weight
  apply List.sum_nonneg
  intro x hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
  split_ifs <;> positivity

theorem weight_take_le (θ : ℕ) (c : List ℕ) (k : ℕ) : weight θ (c.take k) ≤ weight θ c := by
  conv_rhs => rw [← List.take_append_drop k c]
  rw [weight_append]
  linarith [weight_nonneg θ (c.drop k)]

theorem weight_ge_length (θ : ℕ) :
    ∀ c : List ℕ, (∀ x ∈ c, 1 ≤ x ∧ x < θ) → (c.length : ℚ) / θ ≤ weight θ c := by
  intro c
  induction c with
  | nil => intro _; simp [weight]
  | cons a t ih =>
    intro h
    have h1 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    obtain ⟨ha1, ha2⟩ := h a (by simp)
    have hθ : (0 : ℚ) < θ := by exact_mod_cast (by omega : 0 < θ)
    have ha0 : (0 : ℚ) < a := by exact_mod_cast (by omega : 0 < a)
    have hterm : (1 : ℚ) / θ ≤
        (if a < θ / 2 then (1 : ℚ) / (a : ℚ) else (1 : ℚ) / ((a : ℚ) + 1)) := by
      split_ifs
      · exact one_div_le_one_div_of_le ha0 (by exact_mod_cast ha2.le)
      · exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast ha2)
    have : weight θ (a :: t) = (if a < θ / 2 then (1 : ℚ) / (a : ℚ) else (1 : ℚ) / ((a : ℚ) + 1)) +
        weight θ t := by
      unfold weight; simp
    rw [this, List.length_cons]
    push_cast
    rw [add_div]
    linarith

/-! ### Nonemptiness of the fold -/

theorem foldDown_ne_nil (θ : ℚ) : ∀ l : List ℚ, l ≠ [] → foldDown θ l ≠ [] := by
  refine foldDown_induct θ _ ?_ ?_ ?_ ?_ ?_
  · intro h; exact absurd rfl h
  · intro x l hx _; rw [fd_le l hx]; simp
  · intro x hx _; rw [fd_single hx]; simp
  · intro x y l hx hy _; rw [fd_clamp l hx hy]; simp
  · intro x y l hx hy ih _
    rw [fd_step l hx hy]
    apply ih
    intro hnil
    have := List.orderedInsert_length l (y / 2) (r := (· ≥ ·))
    rw [hnil] at this
    simp at this

/-! ### Main -/

theorem main (m : ℕ) (hm : 1 ≤ m) (B : ℚ) (hB0 : 0 ≤ B) (hB1 : B ≤ 1)
    (θ₀ : ℕ) (hθ : Even θ₀) (hθ4 : 4 ≤ θ₀) (A : List ℕ) (hne : A ≠ []) (hA : IsTarget m B A) :
    cellOf θ₀ A ∈ InitialCases m B θ₀ ∧ cellOf θ₀ A ∈ initCases m B θ₀ := by
  obtain ⟨h, rfl⟩ : ∃ h, θ₀ = 2 * h := ⟨θ₀ / 2, by obtain ⟨k, hk⟩ := hθ; omega⟩
  have hh : 2 ≤ h := by omega
  have hk : 2 * h / 2 = h := by omega
  set θq : ℚ := ((2 * h : ℕ) : ℚ) with hθq
  have hθq' : θq = 2 * h := by simp [hθq]
  have hApos : ∀ a ∈ A, 0 < a := fun a ha => lt_of_lt_of_le hm (hA.1 a ha)
  set l := (toQ A).insertionSort (· ≥ ·) with hl
  have hlperm : l.Perm (toQ A) := List.perm_insertionSort _ _
  have hlsorted : l.Pairwise (· ≥ ·) := List.pairwise_insertionSort _ _
  have hmemA : ∀ z ∈ l, ∃ a ∈ A, z = (a : ℚ) := by
    intro z hz
    have h := hlperm.mem_iff.mp hz
    simp only [toQ_eq, List.mem_map] at h
    obtain ⟨a, ha, rfl⟩ := h
    exact ⟨a, ha, rfl⟩
  have hlpos : ∀ x ∈ l, 0 < x := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := hmemA x hx
    exact_mod_cast hApos a ha
  have hθpos : (0 : ℚ) < θq := by rw [hθq']; positivity
  obtain ⟨hFs, hFp⟩ := foldDown_sorted_pos_le hθpos l hlsorted hlpos
  obtain ⟨N, hFN, hN⟩ := foldDown_orig hθpos l hlsorted
  set F := foldDown θq l with hF
  have hcell : cellOf (2 * h) A = (sortQ F).map (roundCell (2 * h)) := rfl
  have hcperm : (cellOf (2 * h) A).Perm (F.map (roundCell (2 * h))) := by
    rw [hcell]; exact (sortQ_perm F).map _
  -- nonempty
  have hlne : l ≠ [] := by
    intro hnil
    apply hne
    have := hlperm.length_eq
    rw [hnil] at this
    simpa [toQ] using this.symm
  have hFne : F ≠ [] := foldDown_ne_nil θq l hlne
  have hcne : cellOf (2 * h) A ≠ [] := by
    intro hnil
    have := hcperm.length_eq
    rw [hnil] at this
    simp at this
    exact hFne (List.length_eq_zero_iff.mp this.symm)
  -- entries
  have hent : ∀ x ∈ cellOf (2 * h) A, min m h ≤ x ∧ x < 2 * h := by
    intro x hx
    obtain ⟨z, zF, rfl⟩ := List.mem_map.mp (hcperm.mem_iff.mp hx)
    have hzle := (hFp z zF).2
    rcases List.mem_append.mp (hFN.mem_iff.mp zF) with h1 | h1
    · obtain ⟨a, haA, rfl⟩ := hmemA z (List.mem_filter.mp h1).1
      have ha2 : a ≤ 2 * h := by
        have := (List.mem_filter.mp h1).2
        simp only [decide_eq_true_eq] at this
        rw [hθq'] at this
        exact_mod_cast this
      have ham := hA.1 a haA
      by_cases hah : a ≤ h
      · rw [round_low (2 * h) h hk _ (by exact_mod_cast hah), Nat.floor_natCast]
        constructor
        · exact le_trans (min_le_left _ _) ham
        · omega
      · rw [round_high (2 * h) h hk _ (by exact_mod_cast (by omega : h < a)), Nat.ceil_natCast]
        constructor
        · exact le_trans (min_le_right _ _) (by omega)
        · omega
    · obtain ⟨h2, h3⟩ := hN z h1
      have e : (h : ℚ) < z := by rw [hθq'] at h2; linarith
      rw [round_high (2 * h) h hk z e]
      have c1 : h + 1 ≤ ⌈z⌉₊ := Nat.lt_ceil.mpr e
      have c2 : ⌈z⌉₊ ≤ 2 * h := Nat.ceil_le.mpr (by rw [hθq'] at h3; exact_mod_cast h3)
      constructor
      · exact le_trans (min_le_right _ _) (by omega)
      · omega
  have hw : weight (2 * h) (cellOf (2 * h) A) < beta B (2 * h) :=
    (lemma_B_1 m hm B hB0 hB1 (2 * h) ⟨h, by omega⟩ hθ4 A hA).2.1
  have hsorted := cell_sorted (2 * h) A
  refine ⟨⟨hcne, hsorted, fun x hx => by rw [hk]; exact hent x hx, hw⟩, ?_⟩
  -- enumeration
  have hmin : 1 ≤ min m h := le_min hm (by omega)
  have hlow : ∀ x ∈ cellOf (2 * h) A, 1 ≤ x ∧ x < 2 * h :=
    fun x hx => ⟨le_trans hmin (hent x hx).1, (hent x hx).2⟩
  have hlenq := weight_ge_length (2 * h) _ hlow
  have hθ0 : (0 : ℚ) < ((2 * h : ℕ) : ℚ) := by exact_mod_cast (by omega : 0 < 2 * h)
  have hfuel : (cellOf (2 * h) A).length ≤ ⌈((2 * h : ℕ) : ℚ) * B⌉₊ + 1 := by
    have h1 : ((cellOf (2 * h) A).length : ℚ) / ((2 * h : ℕ) : ℚ) <
        B + 1 / ((2 * h : ℕ) : ℚ) := lt_of_le_of_lt hlenq hw
    rw [div_lt_iff₀ hθ0, add_mul, one_div_mul_cancel hθ0.ne'] at h1
    have h2 : (B * ((2 * h : ℕ) : ℚ)) ≤ (⌈((2 * h : ℕ) : ℚ) * B⌉₊ : ℚ) := by
      rw [mul_comm]; exact Nat.le_ceil _
    have h3 : ((cellOf (2 * h) A).length : ℚ) < ⌈((2 * h : ℕ) : ℚ) * B⌉₊ + 1 + 1 := by
      linarith
    have : (cellOf (2 * h) A).length < ⌈((2 * h : ℕ) : ℚ) * B⌉₊ + 1 + 1 := by exact_mod_cast h3
    omega
  unfold initCases
  have := enum_complete (fun p => decide (weight (2 * h) p < beta B (2 * h))) (min m (2 * h / 2))
    (2 * h) (cellOf (2 * h) A) [] (⌈((2 * h : ℕ) : ℚ) * B⌉₊ + 1) hcne hfuel
    (by simpa using hsorted) (by rw [hk]; exact hent)
    (by
      intro k _ hk2
      simp only [List.nil_append, decide_eq_true_eq]
      exact lt_of_le_of_lt (weight_take_le _ _ _) hw)
  simpa using this

end PinwheelDensity.ExactRange.Dev.LB2

namespace PinwheelDensity.ExactRange

theorem chk_lemma_B_2 (m : ℕ) (hm : 1 ≤ m) (B : ℚ) (hB0 : 0 ≤ B) (hB1 : B ≤ 1)
    (θ₀ : ℕ) (hθ : Even θ₀) (hθ4 : 4 ≤ θ₀) (A : List ℕ) (hne : A ≠ []) (hA : IsTarget m B A) :
    cellOf θ₀ A ∈ InitialCases m B θ₀ ∧ cellOf θ₀ A ∈ initCases m B θ₀ :=
  Dev.LB2.main m hm B hB0 hB1 θ₀ hθ hθ4 A hne hA

end PinwheelDensity.ExactRange
end

theorem solution : type_of% @PinwheelDensity.ExactRange.chk_lemma_B_2 := @PinwheelDensity.ExactRange.chk_lemma_B_2
