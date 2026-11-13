-- Prove2me | solution 1 for PinwheelDensity.ExactRange.prop_B_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:51:39.635825+00:00
-- url     : https://prove2.me/submissions/d53ec196-f82e-4c6e-9c68-19768237b1a9

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

/-- Lemma B.3: `F_θ ∘ F_{θ+2} = F_θ`. -/
theorem foldDown_comp (θ : ℚ) :
    ∀ l : List ℚ, foldDown θ (foldDown (θ + 2) l) = foldDown θ l := by
  refine foldDown_induct (θ + 2) _ ?_ ?_ ?_ ?_ ?_
  · simp [fd_nil]
  · intro x l hx
    rw [fd_le l hx]
  · intro x hx
    rw [fd_single hx, fd_single (by linarith : θ < θ + 2), fd_single (by linarith : θ < x)]
  · intro x y l hx hy
    rw [fd_clamp l hx hy]
    by_cases hyθ : y ≤ θ
    · rw [fd_clamp l (by linarith : θ < θ + 2) hyθ, fd_clamp l (by linarith : θ < x) hyθ]
    · rw [fd_step l (by linarith : θ < θ + 2) (not_le.mp hyθ),
        fd_step l (by linarith : θ < x) (not_le.mp hyθ)]
  · intro x y l hx hy ih
    rw [fd_step l hx hy, ih, fd_step l (by linarith : θ < x) (by linarith : θ < y)]

/-- Lemma B.4 (multiset form). -/
theorem foldDown_bounded {θ : ℚ} (hθ : 2 ≤ θ) :
    ∀ l : List ℚ, l.Pairwise (· ≥ ·) → (∀ z ∈ l, z ≤ θ + 2) →
      ∃ G O : List ℚ, (foldDown θ l).Perm (l.filter (fun z => decide (z ≤ θ)) ++ G ++ O) ∧
        (∀ z ∈ G, θ / 2 < z ∧ z ≤ θ / 2 + 1) ∧ (∀ z ∈ O, z = θ) ∧ O.length ≤ 1 ∧
        2 * G.length + O.length = l.countP (fun z => decide (θ < z)) := by
  refine foldDown_induct θ _ ?_ ?_ ?_ ?_ ?_
  · intro _ _; exact ⟨[], [], by simp [fd_nil], by simp, by simp, by simp, by simp⟩
  · intro x l hx hs _
    have hall : ∀ a ∈ x :: l, a ≤ θ := by
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hx
      · exact le_trans (List.rel_of_pairwise_cons hs ha) hx
    refine ⟨[], [], ?_, by simp, by simp, by simp, ?_⟩
    · rw [fd_le l hx, List.filter_eq_self.mpr (fun a ha => by simpa using hall a ha)]; simp
    · rw [List.countP_eq_zero.mpr (fun a ha => by simpa using hall a ha)]; simp
  · intro x hx _ _
    refine ⟨[], [θ], ?_, by simp, by simp, by simp, ?_⟩
    · rw [fd_single hx]; simp [not_le.mpr hx]
    · simp [List.countP_cons, hx]
  · intro x y l hx hy hs _
    have hall : ∀ a ∈ y :: l, a ≤ θ := by
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hy
      · exact le_trans (List.rel_of_pairwise_cons hs.of_cons ha) hy
    refine ⟨[], [θ], ?_, by simp, by simp, by simp, ?_⟩
    · rw [fd_clamp l hx hy]
      have : (x :: y :: l).filter (fun z => decide (z ≤ θ)) = y :: l := by
        simp only [List.filter_cons, not_le.mpr hx, decide_false, Bool.false_eq_true, if_false]
        rw [if_pos (by simpa using hy)]
        congr 1
        exact List.filter_eq_self.mpr (fun a ha => by simpa using hall a (List.mem_cons_of_mem _ ha))
      rw [this]
      simpa using (List.perm_append_singleton θ (y :: l)).symm
    · rw [List.countP_cons_of_pos (by simpa using hx),
        List.countP_eq_zero.mpr (fun a ha => by simpa using hall a ha)]
      simp
  · intro x y l hx hy ih hs hb
    have hs' : (List.orderedInsert (· ≥ ·) (y / 2) l).Pairwise (· ≥ ·) :=
      List.Pairwise.orderedInsert _ _ hs.of_cons.of_cons
    have hy2 : y / 2 ≤ θ := by
      have := hb y (by simp)
      linarith
    have hb' : ∀ z ∈ List.orderedInsert (· ≥ ·) (y / 2) l, z ≤ θ + 2 := by
      intro z hz
      rcases (List.mem_orderedInsert _).mp hz with rfl | hz
      · linarith
      · exact hb z (by simp [hz])
    obtain ⟨G, O, h1, h2, h3, h4, h5⟩ := ih hs' hb'
    have hperm := List.perm_orderedInsert (· ≥ ·) (y / 2) l
    refine ⟨y / 2 :: G, O, ?_, ?_, h3, h4, ?_⟩
    · rw [fd_step l hx hy]
      refine h1.trans ?_
      have hl : (x :: y :: l).filter (fun z => decide (z ≤ θ)) = l.filter (fun z => decide (z ≤ θ)) := by
        simp [List.filter_cons, not_le.mpr hx, not_le.mpr hy]
      rw [hl]
      have hp2 : ((List.orderedInsert (· ≥ ·) (y / 2) l).filter (fun z => decide (z ≤ θ))).Perm
          (y / 2 :: l.filter (fun z => decide (z ≤ θ))) := by
        refine (hperm.filter _).trans ?_
        rw [List.filter_cons, if_pos (by simpa using hy2)]
      refine (List.Perm.append (hp2.append_right G) (List.Perm.refl O)).trans ?_
      simp only [List.cons_append, List.append_assoc]
      exact List.perm_middle.symm
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨by linarith, by linarith [hb y (by simp)]⟩
      · exact h2 z hz
    · have hc1 : (List.orderedInsert (· ≥ ·) (y / 2) l).countP (fun z => decide (θ < z)) =
          l.countP (fun z => decide (θ < z)) := by
        rw [hperm.countP_eq, List.countP_cons_of_neg (by simpa using hy2)]
      have hc2 : (x :: y :: l).countP (fun z => decide (θ < z)) =
          l.countP (fun z => decide (θ < z)) + 2 := by
        simp [List.countP_cons, hx, hy]
      rw [hc2, ← hc1, ← h5]
      simp
      omega

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

namespace PinwheelDensity.ExactRange.Dev.LB5

open PinwheelDensity.ExactRange PinwheelDensity.ExactRange.Dev.FoldAux
  PinwheelDensity.ExactRange.Dev.FoldDown PinwheelDensity.ExactRange.Dev.LB5Aux

theorem count_filter' (q : ℕ → Bool) (c : List ℕ) (x : ℕ) :
    (c.filter q).count x = if q x = true then c.count x else 0 := by
  by_cases hq : q x = true
  · rw [if_pos hq]; exact List.count_filter hq
  · rw [if_neg hq]
    apply List.count_eq_zero.mpr
    intro hm
    exact hq (by simpa using (List.mem_filter.mp hm).2)

theorem form_perm (h : ℕ) (hh : 2 ≤ h) (c T : List ℕ) (g p o v : ℕ) (hv : v ≤ 2 * g + o) (ho : o ≤ 1)
    (hc : c.Perm (T ++ List.replicate p h ++ List.replicate g h ++ List.replicate o (2 * h - 1))) :
    UnfoldAdmissible (2 * h) c g p o v ∧
    (T ++ List.replicate p (h + 1) ++ List.replicate (2 * g + o - v) (2 * h) ++
      List.replicate v (2 * h + 1)).Perm (unfoldForm (2 * h) c g p o v) := by
  have hθ2 : 2 * h / 2 = h := by omega
  have hcnt : ∀ x, c.count x = T.count x + (if x = h then p + g else 0) +
      (if x = 2 * h - 1 then o else 0) := by
    intro x
    rw [hc.count_eq]
    simp only [List.count_append, List.count_replicate, beq_iff_eq]
    split_ifs <;> omega
  have hne : h ≠ 2 * h - 1 := by omega
  have e1 := hcnt h
  have e2 := hcnt (2 * h - 1)
  simp only [if_true, hne, hne.symm, if_false] at e1 e2
  refine ⟨?_, ?_⟩
  · simp only [UnfoldAdmissible, hθ2]
    omega
  · rw [List.perm_iff_count]
    intro x
    simp only [unfoldForm, hθ2, List.count_append, List.count_replicate, count_filter',
      beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq, ne_eq]
    have hx := hcnt x
    by_cases h1 : x = h
    · rw [h1] at hx ⊢
      split_ifs at hx ⊢ <;> omega
    · by_cases h2 : x = 2 * h - 1
      · rw [h2] at hx ⊢
        split_ifs at hx ⊢ <;> omega
      · split_ifs at hx ⊢ <;> omega

theorem two_vals (a : ℕ) : ∀ W : List ℕ, (∀ x ∈ W, x = a ∨ x = a + 1) →
    W.Perm (List.replicate (W.length - W.count (a + 1)) a ++
      List.replicate (W.count (a + 1)) (a + 1)) := by
  intro W hW
  have hsum : W.count a + W.count (a + 1) = W.length := by
    induction W with
    | nil => simp
    | cons x t ih =>
      have := ih (fun y hy => hW y (List.mem_cons_of_mem _ hy))
      rcases hW x (by simp) with rfl | rfl <;> simp [List.count_cons] <;> omega
  rw [List.perm_iff_count]
  intro y
  simp only [List.count_append, List.count_replicate, beq_iff_eq]
  by_cases h1 : y = a
  · subst h1; simp; try omega
  by_cases h2 : y = a + 1
  · subst h2; simp; try omega
  · have h1' : a ≠ y := fun e => h1 e.symm
    have h2' : a + 1 ≠ y := fun e => h2 e.symm
    have : W.count y = 0 :=
      List.count_eq_zero.mpr (fun hy => by rcases hW y hy with h | h <;> contradiction)
    simp [h1, h2, h1', h2', this]

theorem part1 (h : ℕ) (hh : 2 ≤ h) (m : ℕ) (hm : 1 ≤ m) (B : ℚ) (A : List ℕ) (hA : IsTarget m B A) :
    ∃ g p o v : ℕ, UnfoldAdmissible (2 * h) (cellOf (2 * h) A) g p o v ∧
      (cellOf (2 * h + 2) A).Perm (unfoldForm (2 * h) (cellOf (2 * h) A) g p o v) := by
  have hk : 2 * h / 2 = h := by omega
  have hk' : (2 * h + 2) / 2 = h + 1 := by omega
  set θq : ℚ := ((2 * h : ℕ) : ℚ) with hθq
  have hθq' : θq = 2 * h := by simp [hθq]
  have hhq : (2 : ℚ) ≤ h := by exact_mod_cast hh
  have hθ2 : (2 : ℚ) ≤ θq := by rw [hθq']; linarith
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
  have hθ2pos : (0 : ℚ) < θq + 2 := by linarith
  set F2 := foldDown (θq + 2) l with hF2
  obtain ⟨hFs, hFp⟩ := foldDown_sorted_pos_le hθ2pos l hlsorted hlpos
  obtain ⟨N, hFN, hN⟩ := foldDown_orig hθ2pos l hlsorted
  have hF1 : foldDown θq l = foldDown θq F2 := (foldDown_comp θq l).symm
  obtain ⟨G, O, hGO, hG, hO, hO1, hcount⟩ :=
    foldDown_bounded hθ2 F2 hFs (fun z hz => (hFp z hz).2)
  have hcell1 : cellOf (2 * h) A = (sortQ (foldDown θq l)).map (roundCell (2 * h)) := rfl
  have hcell2 : cellOf (2 * h + 2) A = (sortQ F2).map (roundCell (2 * h + 2)) := by
    unfold cellOf foldOf
    rw [show (((2 * h + 2 : ℕ)) : ℚ) = θq + 2 by rw [hθq']; push_cast; ring]
  -- integrality of small entries of F2
  have hint : ∀ z ∈ F2, z ≤ ((h : ℚ) + 1) → ∃ a : ℕ, z = a := by
    intro z zF hz
    rcases List.mem_append.mp (hFN.mem_iff.mp zF) with h1 | h1
    · obtain ⟨a, _, rfl⟩ := hmemA z (List.mem_filter.mp h1).1
      exact ⟨a, rfl⟩
    · have := (hN z h1).1
      rw [hθq'] at this
      linarith
  set S := F2.filter (fun z => decide (z ≤ θq)) with hS
  set U := F2.filter (fun z => !decide (z ≤ θq)) with hU
  have hSU : (S ++ U).Perm F2 := List.filter_append_perm _ _
  have hUmem : ∀ z ∈ U, z ∈ F2 ∧ θq < z := by
    intro z hz
    obtain ⟨h1, h2⟩ := List.mem_filter.mp hz
    exact ⟨h1, by simpa using h2⟩
  have hUlen : U.length = F2.countP (fun z => decide (θq < z)) := by
    rw [List.countP_eq_length_filter]
    congr 1
    exact List.filter_congr (fun z _ => by
      by_cases hz : z ≤ θq
      · simp [hz]
      · simp [hz, not_le.mp hz])
  have hSmem : ∀ z ∈ S, z ∈ F2 ∧ z ≤ θq := by
    intro z hz
    obtain ⟨h1, h2⟩ := List.mem_filter.mp hz
    exact ⟨h1, by simpa using h2⟩
  set S0 := S.filter (fun z => decide (z ≠ ((h : ℚ) + 1))) with hS0
  set S1 := S.filter (fun z => !decide (z ≠ ((h : ℚ) + 1))) with hS1
  have hSS : (S0 ++ S1).Perm S := List.filter_append_perm _ _
  have hS1eq : S1 = List.replicate S1.length ((h : ℚ) + 1) := by
    rw [List.eq_replicate_iff]
    refine ⟨by simp, fun z hz => ?_⟩
    have := (List.mem_filter.mp hz).2
    simpa using this
  have hS0mem : ∀ z ∈ S0, z ∈ F2 ∧ z ≤ θq ∧ z ≠ (h : ℚ) + 1 := by
    intro z hz
    obtain ⟨h1, h2⟩ := List.mem_filter.mp hz
    obtain ⟨h3, h4⟩ := hSmem z h1
    exact ⟨h3, h4, by simpa using h2⟩
  set p := S1.length with hp
  set g := G.length with hg
  set o := O.length with ho
  have hGrep : G.map (roundCell (2 * h)) = List.replicate g h := by
    rw [List.eq_replicate_iff]
    refine ⟨by simp [hg], fun x hx => ?_⟩
    obtain ⟨z, zG, rfl⟩ := List.mem_map.mp hx
    obtain ⟨h1, h2⟩ := hG z zG
    have e : θq / 2 = h := by rw [hθq']; ring
    rw [e] at h1 h2
    rw [round_high (2 * h) h hk z h1]
    have : ⌈z⌉₊ = h + 1 := by
      rw [Nat.ceil_eq_iff (by omega)]
      constructor
      · simpa using h1
      · exact_mod_cast h2
    omega
  have hOrep : O = List.replicate o θq := by
    rw [List.eq_replicate_iff]
    exact ⟨by simp [ho], fun z hz => hO z hz⟩
  have hθh : (h : ℚ) < θq := by rw [hθq']; linarith
  have hOmap : O.map (roundCell (2 * h)) = List.replicate o (2 * h - 1) := by
    rw [hOrep, List.map_replicate, round_high (2 * h) h hk θq hθh]
    have : ⌈θq⌉₊ = 2 * h := by rw [hθq]; exact Nat.ceil_natCast _
    rw [this]
  have hR1 : roundCell (2 * h) ((h : ℚ) + 1) = h := by
    have e : ((h : ℚ) + 1) = ((h + 1 : ℕ) : ℚ) := by push_cast; ring
    rw [round_high (2 * h) h hk _ (by linarith), e, Nat.ceil_natCast]; rfl
  have hR2 : roundCell (2 * h + 2) ((h : ℚ) + 1) = h + 1 := by
    have e : ((h : ℚ) + 1) = ((h + 1 : ℕ) : ℚ) := by push_cast; ring
    rw [round_low (2 * h + 2) (h + 1) hk' _ (by push_cast; linarith), e, Nat.floor_natCast]
  set T := S0.map (roundCell (2 * h)) with hT
  have hTeq : S0.map (roundCell (2 * h + 2)) = T := by
    rw [hT]
    refine List.map_congr_left (fun z hz => ?_)
    obtain ⟨h1, h2, h3⟩ := hS0mem z hz
    by_cases hzh : z ≤ h
    · rw [round_low (2 * h) h hk z hzh, round_low (2 * h + 2) (h + 1) hk' z (by push_cast; linarith)]
    · have hzh' : (h : ℚ) < z := not_le.mp hzh
      have hz1 : (h : ℚ) + 1 < z := by
        by_contra hcon
        have hle : z ≤ (h : ℚ) + 1 := not_lt.mp hcon
        obtain ⟨a, ha⟩ := hint z h1 hle
        rw [ha] at hzh' hle
        have a1 : h < a := by exact_mod_cast hzh'
        have a2 : a ≤ h + 1 := by exact_mod_cast hle
        apply h3
        rw [ha]
        have : a = h + 1 := by omega
        rw [this]; push_cast; ring
      rw [round_high (2 * h) h hk z hzh', round_high (2 * h + 2) (h + 1) hk' z (by push_cast; exact hz1)]
  -- the two multisets
  have hSR : (S.map (roundCell (2 * h))).Perm (T ++ List.replicate p h) := by
    refine ((hSS.symm.map _)).trans ?_
    rw [List.map_append, hT]
    refine List.Perm.append_left _ (List.Perm.of_eq ?_)
    rw [hS1eq, List.map_replicate, hR1]
  have hSR' : (S.map (roundCell (2 * h + 2))).Perm (T ++ List.replicate p (h + 1)) := by
    refine ((hSS.symm.map _)).trans ?_
    rw [List.map_append, hTeq]
    refine List.Perm.append_left _ (List.Perm.of_eq ?_)
    rw [hS1eq, List.map_replicate, hR2]
  -- U
  have hUR : ∀ x ∈ U.map (roundCell (2 * h + 2)), x = 2 * h ∨ x = 2 * h + 1 := by
    intro x hx
    obtain ⟨z, zU, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hzF, hzθ⟩ := hUmem z zU
    have hzle := (hFp z hzF).2
    have h1 : (h : ℚ) + 1 < z := by rw [hθq'] at hzθ; linarith
    rw [round_high (2 * h + 2) (h + 1) hk' z (by push_cast; exact h1)]
    have c1 : 2 * h < ⌈z⌉₊ := Nat.lt_ceil.mpr (by rw [hθq] at hzθ; exact hzθ)
    have c2 : ⌈z⌉₊ ≤ 2 * h + 2 := by
      apply Nat.ceil_le.mpr
      push_cast; rw [hθq'] at hzle; exact hzle
    omega
  set W := U.map (roundCell (2 * h + 2)) with hW
  set v := W.count (2 * h + 1) with hv
  have hWlen : W.length = 2 * g + o := by rw [hW, List.length_map, hUlen, ← hcount]
  have hvle : v ≤ 2 * g + o := hWlen ▸ List.count_le_length
  have hWp := two_vals (2 * h) W hUR
  rw [hWlen, ← hv] at hWp
  -- c
  have hc : (cellOf (2 * h) A).Perm
      (T ++ List.replicate p h ++ List.replicate g h ++ List.replicate o (2 * h - 1)) := by
    rw [hcell1]
    refine ((sortQ_perm _).map _).trans ?_
    rw [hF1]
    refine (hGO.map _).trans ?_
    rw [List.map_append, List.map_append, hGrep, hOmap]
    exact (hSR.append_right _).append_right _
  have hc' : (cellOf (2 * h + 2) A).Perm
      (T ++ List.replicate p (h + 1) ++ List.replicate (2 * g + o - v) (2 * h) ++
        List.replicate v (2 * h + 1)) := by
    rw [hcell2]
    refine ((sortQ_perm _).map _).trans ?_
    refine (hSU.symm.map _).trans ?_
    rw [List.map_append, ← hW]
    refine (hSR'.append hWp).trans (List.Perm.of_eq ?_)
    simp [List.append_assoc]
  obtain ⟨hadm, hperm⟩ := form_perm h hh _ T g p o v hvle (by omega) hc
  exact ⟨g, p, o, v, hadm, hc'.trans hperm⟩

theorem gen_iff (B : ℚ) (θ : ℕ) (c d : List ℕ) :
    d ∈ unfoldCell B θ c ↔ ∃ g p o v : ℕ, UnfoldAdmissible θ c g p o v ∧
      d = (unfoldForm θ c g p o v).insertionSort (· ≤ ·) ∧
      weight (θ + 2) d < beta B (θ + 2) := by
  unfold unfoldCell
  simp only [List.mem_flatMap, List.mem_range, List.mem_filterMap, UnfoldAdmissible]
  constructor
  · rintro ⟨g, hg, p, hp, o, ho, v, hv, hfm⟩
    split_ifs at hfm with hw
    · cases hfm
      refine ⟨g, p, o, v, ⟨by omega, ?_, ?_, by omega⟩, rfl, hw⟩ <;> omega
  · rintro ⟨g, p, o, v, ⟨h1, h2, h3, h4⟩, rfl, hw⟩
    refine ⟨g, by omega, p, by omega, o, by omega, v, by omega, ?_⟩
    rw [if_pos hw]

end PinwheelDensity.ExactRange.Dev.LB5

namespace PinwheelDensity.ExactRange

open Dev.LB5 Dev.LB5Aux in
theorem chk_prop_B_5 (B : ℚ) (θ : ℕ) (hθ : Even θ) (hθ4 : 4 ≤ θ) :
    (∀ (m : ℕ) (A : List ℕ), 1 ≤ m → 0 ≤ B → B ≤ 1 → IsTarget m B A →
      (∃ g p o v : ℕ, UnfoldAdmissible θ (cellOf θ A) g p o v ∧
        (cellOf (θ + 2) A).Perm (unfoldForm θ (cellOf θ A) g p o v)) ∧
      weight (θ + 2) (cellOf (θ + 2) A) < beta B (θ + 2) ∧
      cellOf (θ + 2) A ∈ unfoldCell B θ (cellOf θ A)) ∧
    (∀ c d : List ℕ, d ∈ unfoldCell B θ c ↔
      ∃ g p o v : ℕ, UnfoldAdmissible θ c g p o v ∧
        d = (unfoldForm θ c g p o v).insertionSort (· ≤ ·) ∧
        weight (θ + 2) d < beta B (θ + 2)) := by
  refine ⟨fun m A hm hB0 hB1 hA => ?_, fun c d => gen_iff B θ c d⟩
  obtain ⟨h, rfl⟩ : ∃ h, θ = 2 * h := ⟨θ / 2, by obtain ⟨k, hk⟩ := hθ; omega⟩
  have hh : 2 ≤ h := by omega
  have hw : weight (2 * h + 2) (cellOf (2 * h + 2) A) < beta B (2 * h + 2) :=
    (lemma_B_1 m hm B hB0 hB1 (2 * h + 2) ⟨h + 1, by omega⟩ (by omega) A hA).2.1
  obtain ⟨g, p, o, v, hadm, hperm⟩ := part1 h hh m hm B A hA
  refine ⟨⟨g, p, o, v, hadm, hperm⟩, hw, ?_⟩
  rw [gen_iff]
  refine ⟨g, p, o, v, hadm, ?_, hw⟩
  exact List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (cell_sorted _ A)
    (List.pairwise_insertionSort _ _) (hperm.trans (List.perm_insertionSort _ _).symm)

end PinwheelDensity.ExactRange
end

theorem solution : type_of% @PinwheelDensity.ExactRange.chk_prop_B_5 := @PinwheelDensity.ExactRange.chk_prop_B_5
