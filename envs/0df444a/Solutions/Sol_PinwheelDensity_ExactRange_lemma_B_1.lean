-- Prove2me | solution 1 for PinwheelDensity.ExactRange.lemma_B_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:27:53.421439+00:00
-- url     : https://prove2.me/submissions/8d453174-f9d4-43fb-b737-895f906eac3f

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_Schedulable
import Definitions.Def_PinwheelDensity_ExactRange_cellOf
import Definitions.Def_PinwheelDensity_ExactRange_checkRun

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

theorem cnt_succ (s : ℕ → Option ℕ) (i t w : ℕ) :
    cnt s i t (w + 1) = cnt s i t w + if s (t + w) = some i then 1 else 0 := by
  unfold cnt
  rw [List.range_succ, List.filter_append]
  by_cases h : s (t + w) = some i <;> simp [h]

theorem cnt_add (s : ℕ → Option ℕ) (i t a b : ℕ) :
    cnt s i t (a + b) = cnt s i t a + cnt s i (t + a) b := by
  induction b with
  | zero => simp [cnt]
  | succ b ih =>
    rw [← add_assoc, cnt_succ, cnt_succ, ih, add_assoc, add_assoc]

theorem cnt_mono_of_imp (s s' : ℕ → Option ℕ) (i i' t w : ℕ)
    (h : ∀ k, k < w → s (t + k) = some i → s' (t + k) = some i') :
    cnt s i t w ≤ cnt s' i' t w := by
  induction w with
  | zero => simp [cnt]
  | succ w ih =>
    rw [cnt_succ, cnt_succ]
    have := ih (fun k hk => h k (by omega))
    by_cases h1 : s (t + w) = some i
    · have h2 := h w (by omega) h1
      simp [h1, h2]; omega
    · simp only [h1, if_false]
      split_ifs <;> omega

theorem cnt_congr (s s' : ℕ → Option ℕ) (i t w : ℕ)
    (h : ∀ k, k < w → (s (t + k) = some i ↔ s' (t + k) = some i)) :
    cnt s i t w = cnt s' i t w :=
  le_antisymm (cnt_mono_of_imp s s' i i t w fun k hk => (h k hk).1)
    (cnt_mono_of_imp s' s i i t w fun k hk => (h k hk).2)

theorem serves_mono {s : ℕ → Option ℕ} {i : ℕ} {a a' : ℚ} (ha : 0 < a) (haa : a ≤ a')
    (h : Serves s i a) : Serves s i a' := by
  intro t w
  refine le_trans (Nat.floor_le_floor ?_) (h t w)
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) ha haa

/-! ### Lemma A.2 / A.3: relabeling, deletion, monotonicity -/

/-- Relabeling, deletion and monotonicity at once (Lemmas A.2 and A.3): if every entry `B[j]`
of `B` is at least the entry `A[σ j]` of a schedulable list `A`, for an index map `σ` that is
injective on the positions of `B`, then `B` is schedulable. -/
theorem RatSchedulable.of_embed {A B : List ℚ} (σ : ℕ → ℕ)
    (hinj : ∀ j k, j < B.length → k < B.length → σ j = σ k → j = k)
    (hle : ∀ j (hj : j < B.length), ∃ a, A[σ j]? = some a ∧ a ≤ B[j])
    (hA : RatSchedulable A) : RatSchedulable B := by
  classical
  obtain ⟨hpos, s, hs⟩ := hA
  have hσ : ∀ j (hj : j < B.length), ∃ h : σ j < A.length, A[σ j] ≤ B[j] := by
    intro j hj
    obtain ⟨a, ha, hab⟩ := hle j hj
    obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.mp ha
    exact ⟨h, hab⟩
  have hApos : ∀ j (hj : j < B.length), 0 < A[σ j]'(hσ j hj).1 :=
    fun j hj => hpos _ (List.getElem_mem _)
  refine ⟨?_, ?_⟩
  · intro b hb
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hb
    exact lt_of_lt_of_le (hApos j hj) (hσ j hj).2
  · let s' : ℕ → Option ℕ := fun t =>
      match s t with
      | none => none
      | some k => if h : ∃ j, j < B.length ∧ σ j = k then some (Classical.choose h) else none
    refine ⟨s', fun j hj => ?_⟩
    have h1 : Serves s (σ j) B[j] :=
      serves_mono (hApos j hj) (hσ j hj).2 (hs (σ j) (hσ j hj).1)
    intro t w
    refine le_trans (h1 t w) (cnt_mono_of_imp s s' _ _ t w fun k _ hk => ?_)
    have hex : ∃ j', j' < B.length ∧ σ j' = σ j := ⟨j, hj, rfl⟩
    have hc := Classical.choose_spec hex
    have := hinj _ _ hc.1 hj hc.2
    simp only [s', hk, dif_pos hex]
    rw [this]

theorem perm_index {α : Type} {A B : List α} (h : A.Perm B) :
    ∃ σ : ℕ → ℕ, (∀ j, j < B.length → σ j < A.length ∧ A[σ j]? = B[j]?) ∧
      ∀ j k, j < B.length → k < B.length → σ j = σ k → j = k := by
  induction h with
  | nil => exact ⟨id, by simp, by simp⟩
  | cons x _ ih =>
    obtain ⟨σ, h1, h2⟩ := ih
    refine ⟨fun j => if j = 0 then 0 else σ (j - 1) + 1, ?_, ?_⟩
    · intro j hj
      cases j with
      | zero => simp
      | succ j =>
        have := h1 j (by simpa using hj)
        simp only [List.length_cons] at hj ⊢
        simp [this.2]; omega
    · intro j k hj hk hjk
      simp only [List.length_cons] at hj hk
      cases j <;> cases k <;> simp at hjk ⊢
      exact h2 _ _ (by omega) (by omega) hjk
  | swap x y l =>
    refine ⟨fun j => if j = 0 then 1 else if j = 1 then 0 else j, ?_, ?_⟩
    · intro j hj
      simp only [List.length_cons] at hj ⊢
      rcases j with _ | _ | j <;> simp
      omega
    · intro j k hj hk hjk
      simp only at hjk
      split_ifs at hjk <;> omega
  | trans _ _ ih1 ih2 =>
    obtain ⟨σ1, a1, b1⟩ := ih1
    obtain ⟨σ2, a2, b2⟩ := ih2
    refine ⟨fun j => σ1 (σ2 j), ?_, ?_⟩
    · intro j hj
      obtain ⟨c1, c2⟩ := a2 j hj
      obtain ⟨d1, d2⟩ := a1 (σ2 j) c1
      exact ⟨d1, d2.trans c2⟩
    · intro j k hj hk h
      exact b2 j k hj hk (b1 _ _ (a2 j hj).1 (a2 k hk).1 h)

/-- Lemma A.2: schedulability is invariant under permutations. -/
theorem RatSchedulable.perm {A B : List ℚ} (h : A.Perm B) (hA : RatSchedulable A) :
    RatSchedulable B := by
  obtain ⟨σ, h1, h2⟩ := perm_index h
  refine RatSchedulable.of_embed σ h2 (fun j hj => ?_) hA
  obtain ⟨c1, c2⟩ := h1 j hj
  exact ⟨B[j], by rw [c2]; simp [hj], le_refl _⟩

/-- Lemma A.3: schedulability is monotone in the periods (componentwise). -/
theorem RatSchedulable.mono {A B : List ℚ} (h : List.Forall₂ (· ≤ ·) A B)
    (hA : RatSchedulable A) : RatSchedulable B := by
  obtain ⟨hl, hge⟩ := List.forall₂_iff_get.mp h
  refine RatSchedulable.of_embed id (fun j k _ _ hjk => hjk) (fun j hj => ?_) hA
  have hj' : j < A.length := by omega
  exact ⟨A[j], by simp [hj'], by simpa using hge j hj' hj⟩

/-! ### Lemma A.4: the pair fold -/

theorem half_floor {x m : ℚ} (hm : 0 < m) (hx : 2 * m ≤ x) (w : ℕ) :
    ⌊(w : ℚ) / x⌋₊ ≤ ⌊(w : ℚ) / m⌋₊ / 2 := by
  have h2 := Nat.floor_div_natCast ((w : ℚ) / m) 2
  push_cast at h2
  rw [← h2]
  refine Nat.floor_le_floor ?_
  rw [div_div, div_le_div_iff₀ (by linarith) (by positivity)]
  have : (0 : ℚ) ≤ w := Nat.cast_nonneg _
  nlinarith

/-- Lemma A.4 (pair fold): if `A ++ [min x y / 2]` is schedulable, so is `A ++ [x, y]`. -/
theorem RatSchedulable.pairFold {A : List ℚ} {x y : ℚ} (hx : 0 < x) (hy : 0 < y)
    (h : RatSchedulable (A ++ [min x y / 2])) : RatSchedulable (A ++ [x, y]) := by
  obtain ⟨hpos, s, hs⟩ := h
  have hμ : 0 < min x y / 2 := by have := lt_min hx hy; linarith
  let ν := A.length
  let N : ℕ → ℕ := fun t => cnt s ν 0 t
  let s' : ℕ → Option ℕ := fun t =>
    if s t = some ν then (if N t % 2 = 0 then some ν else some (ν + 1))
    else if s t = some (ν + 1) then none else s t
  have e1 : ∀ t, s' t = some ν ↔ s t = some ν ∧ N t % 2 = 0 := by
    intro t; simp only [s']; split_ifs <;> simp_all
  have e2 : ∀ t, s' t = some (ν + 1) ↔ s t = some ν ∧ ¬ N t % 2 = 0 := by
    intro t; simp only [s']; split_ifs <;> simp_all
  have e3 : ∀ t i, i < ν → (s' t = some i ↔ s t = some i) := by
    intro t i hi; simp only [s']; split_ifs <;> simp_all <;> omega
  have key : ∀ t w, cnt s' ν t w = (cnt s ν t w + (if N t % 2 = 0 then 1 else 0)) / 2 ∧
      cnt s' (ν + 1) t w = (cnt s ν t w + (if N t % 2 = 0 then 0 else 1)) / 2 := by
    intro t w
    induction w with
    | zero => split_ifs <;> simp [cnt]
    | succ w ih =>
      simp only [cnt_succ]
      have hN : N (t + w) = N t + cnt s ν t w := by
        have := cnt_add s ν 0 t w
        simpa [N] using this
      have f1 := e1 (t + w)
      have f2 := e2 (t + w)
      rw [hN] at f1 f2
      obtain ⟨ih1, ih2⟩ := ih
      by_cases hc : s (t + w) = some ν
      · by_cases hp : (N t + cnt s ν t w) % 2 = 0
        · have g1 : s' (t + w) = some ν := f1.2 ⟨hc, hp⟩
          have g2 : ¬ s' (t + w) = some (ν + 1) := fun hh => (f2.1 hh).2 hp
          simp [g1, g2, hc]
          split_ifs at ih1 ih2 ⊢ <;> omega
        · have g1 : ¬ s' (t + w) = some ν := fun hh => hp (f1.1 hh).2
          have g2 : s' (t + w) = some (ν + 1) := f2.2 ⟨hc, hp⟩
          simp [g1, g2, hc]
          split_ifs at ih1 ih2 ⊢ <;> omega
      · have g1 : ¬ s' (t + w) = some ν := fun hh => hc (f1.1 hh).1
        have g2 : ¬ s' (t + w) = some (ν + 1) := fun hh => hc (f2.1 hh).1
        simp [g1, g2, hc]
        split_ifs at ih1 ih2 ⊢ <;> omega
  refine ⟨?_, s', ?_⟩
  · intro a ha
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ha | rfl | rfl
    · exact hpos a (by simp [ha])
    · exact hx
    · exact hy
  · intro i hi
    simp only [List.length_append, List.length_cons, List.length_nil, ν] at hi
    have hAl : (A ++ [x, y]).length = A.length + 2 := by simp
    rcases Nat.lt_or_ge i A.length with hlt | hge
    · have e : (A ++ [x, y])[i] = (A ++ [min x y / 2])[i]'(by simp; omega) := by
        rw [List.getElem_append_left hlt, List.getElem_append_left hlt]
      intro t w
      rw [e]
      have := hs i (by simp; omega) t w
      rw [cnt_congr s' s i t w (fun k _ => e3 _ i hlt)]
      exact this
    · have hμs : (A ++ [min x y / 2])[ν]'(by simp [ν]) = min x y / 2 := by simp [ν]
      have hs0 := hs ν (by simp [ν])
      rw [hμs] at hs0
      rcases (show i = A.length ∨ i = A.length + 1 by omega) with rfl | rfl
      · have e : (A ++ [x, y])[A.length] = x := by simp
        intro t w
        rw [e]
        have := half_floor (x := x) (m := min x y / 2) hμ (by have := min_le_left x y; linarith) w
        have h3 := hs0 t w
        have h4 := (key t w).1
        rw [h4]
        have : ⌊(w : ℚ) / x⌋₊ ≤ cnt s ν t w / 2 := le_trans this (Nat.div_le_div_right h3)
        omega
      · have e : (A ++ [x, y])[A.length + 1] = y := by simp
        intro t w
        rw [e]
        have := half_floor (x := y) (m := min x y / 2) hμ (by have := min_le_right x y; linarith) w
        have h3 := hs0 t w
        have h4 := (key t w).2
        rw [h4]
        have : ⌊(w : ℚ) / y⌋₊ ≤ cnt s ν t w / 2 := le_trans this (Nat.div_le_div_right h3)
        omega

/-! ### Lemma A.5: sorting is monotone -/

theorem sortQ_perm (l : List ℚ) : (sortQ l).Perm l := List.perm_insertionSort _ l

theorem fle_refl : ∀ l : List ℚ, List.Forall₂ (· ≤ ·) l l := fun l =>
  List.forall₂_same.2 (fun _ _ => le_rfl)

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

theorem foldDown_sched {θ : ℚ} (hθ : 0 < θ) :
    ∀ l : List ℚ, l.Pairwise (· ≥ ·) → (∀ x ∈ l, 0 < x) →
      RatSchedulable (foldDown θ l) → RatSchedulable l := by
  refine foldDown_induct θ _ ?_ ?_ ?_ ?_ ?_
  · intro _ _ h; simpa [fd_nil] using h
  · intro x l hx _ _ h
    rwa [fd_le l hx] at h
  · intro x hx _ _ h
    rw [fd_single hx] at h
    exact RatSchedulable.mono (List.Forall₂.cons hx.le List.Forall₂.nil) h
  · intro x y l hx hy _ _ h
    rw [fd_clamp l hx hy] at h
    exact RatSchedulable.mono (List.Forall₂.cons hx.le (fle_refl _)) h
  · intro x y l hx hy ih hs hp h
    rw [fd_step l hx hy] at h
    have hl := ih (List.Pairwise.orderedInsert _ _ hs.of_cons.of_cons) (by
      intro z hz
      rcases (List.mem_orderedInsert _).mp hz with rfl | hz
      · have := hp y (by simp); linarith
      · exact hp z (by simp [hz])) h
    have hyx : y ≤ x := List.rel_of_pairwise_cons hs (by simp)
    have h1 : RatSchedulable (l ++ [y / 2]) :=
      RatSchedulable.perm (((List.perm_orderedInsert _ _ _).trans
        (List.perm_append_singleton _ _).symm)) hl
    have h2 := RatSchedulable.pairFold (A := l) (hp x (by simp)) (hp y (by simp))
      (by rwa [min_eq_right hyx])
    exact RatSchedulable.perm (List.perm_append_comm.trans (by simp)) h2

/-! ### Lemma A.8 (c) -/

theorem densityQ_cons (x : ℚ) (l : List ℚ) : densityQ (x :: l) = 1 / x + densityQ l := by
  simp [densityQ]

theorem densityQ_perm {l l' : List ℚ} (h : l.Perm l') : densityQ l = densityQ l' := by
  unfold densityQ; exact (h.map _).sum_eq

theorem foldDown_dens_aux {θ : ℚ} (hθ : 0 < θ) :
    ∀ l : List ℚ, l.Pairwise (· ≥ ·) → (∀ x ∈ l, 0 < x) →
      ∀ x, l.head? = some x → θ < x →
        densityQ (foldDown θ l) ≤ densityQ l + 1 / θ - 1 / x := by
  refine foldDown_induct θ _ ?_ ?_ ?_ ?_ ?_
  · intro _ _ x h; simp at h
  · intro x l hx _ _ z hz hzθ
    simp only [List.head?_cons, Option.some.injEq] at hz
    subst hz; linarith
  · intro x hx _ _ z hz _
    simp only [List.head?_cons, Option.some.injEq] at hz
    subst hz
    rw [fd_single hx]; simp [densityQ]
  · intro x y l hx hy _ _ z hz _
    simp only [List.head?_cons, Option.some.injEq] at hz
    subst hz
    rw [fd_clamp l hx hy]; simp [densityQ_cons]; linarith
  · intro x y l hx hy ih hs hp z hz _
    simp only [List.head?_cons, Option.some.injEq] at hz
    subst hz
    rw [fd_step l hx hy]
    have hs' : (List.orderedInsert (· ≥ ·) (y / 2) l).Pairwise (· ≥ ·) :=
      List.Pairwise.orderedInsert _ _ hs.of_cons.of_cons
    have hp' : ∀ w ∈ List.orderedInsert (· ≥ ·) (y / 2) l, 0 < w := by
      intro w hw
      rcases (List.mem_orderedInsert _).mp hw with rfl | hw
      · have := hp y (by simp); linarith
      · exact hp w (by simp [hw])
    have hy0 : 0 < y := hp y (by simp)
    have hD : densityQ (List.orderedInsert (· ≥ ·) (y / 2) l) = 2 / y + densityQ l := by
      rw [densityQ_perm (List.perm_orderedInsert _ _ _), densityQ_cons]
      field_simp
    have hD0 : densityQ (x :: y :: l) = 1 / x + (1 / y + densityQ l) := by
      simp [densityQ_cons]
    rw [hD0]
    obtain ⟨x', t, hl⟩ : ∃ x' t, List.orderedInsert (· ≥ ·) (y / 2) l = x' :: t := by
      cases h : List.orderedInsert (· ≥ ·) (y / 2) l with
      | nil =>
        have := congrArg List.length h
        rw [List.orderedInsert_length] at this; simp at this
      | cons a b => exact ⟨a, b, rfl⟩
    have hmem : x' ∈ List.orderedInsert (· ≥ ·) (y / 2) l := by rw [hl]; simp
    have hx'y : x' ≤ y := by
      rcases (List.mem_orderedInsert _).mp hmem with h | h
      · rw [h]; linarith
      · exact List.rel_of_pairwise_cons hs.of_cons h
    have hx'0 : 0 < x' := hp' x' hmem
    by_cases hx' : x' ≤ θ
    · rw [hl, fd_le t hx']
      rw [hl] at hD
      have : 1 / y ≤ 1 / θ := one_div_le_one_div_of_le hθ hy.le
      have h2 : 2 / y = 1 / y + 1 / y := by ring
      linarith
    · have := ih hs' hp' x' (by rw [hl]; rfl) (not_le.mp hx')
      rw [hD] at this
      have h3 : 1 / y ≤ 1 / x' := one_div_le_one_div_of_le hx'0 hx'y
      have h2 : 2 / y = 1 / y + 1 / y := by ring
      linarith

/-- Lemma A.8 (c): `D(F_θ(l)) < D(l) + 1/θ`. -/
theorem foldDown_dens {θ : ℚ} (hθ : 0 < θ) (l : List ℚ) (hs : l.Pairwise (· ≥ ·))
    (hp : ∀ x ∈ l, 0 < x) : densityQ (foldDown θ l) < densityQ l + 1 / θ := by
  cases l with
  | nil => simp [fd_nil, densityQ, hθ]
  | cons x l =>
    have hx : 0 < x := hp x (by simp)
    by_cases h : x ≤ θ
    · rw [fd_le l h]
      have : 0 < 1 / θ := by positivity
      linarith
    · have := foldDown_dens_aux hθ (x :: l) hs hp x rfl (not_le.mp h)
      have : 0 < 1 / x := by positivity
      linarith

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

namespace PinwheelDensity.ExactRange.Dev.LB1

open PinwheelDensity.ExactRange PinwheelDensity.ExactRange.Dev.FoldAux
  PinwheelDensity.ExactRange.Dev.FoldDown

theorem leAll_map_left (b : List ℚ) (f : ℚ → ℚ) (h : ∀ z ∈ b, f z ≤ z) :
    leAll (b.map f) b = true := by
  induction b with
  | nil => simp [leAll]
  | cons a b ih =>
    simp only [List.map_cons, leAll, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h a (by simp), ih (fun z hz => h z (by simp [hz]))⟩

theorem leAll_map_right (b : List ℚ) (f : ℚ → ℚ) (h : ∀ z ∈ b, z ≤ f z) :
    leAll b (b.map f) = true := by
  induction b with
  | nil => simp [leAll]
  | cons a b ih =>
    simp only [List.map_cons, leAll, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h a (by simp), ih (fun z hz => h z (by simp [hz]))⟩

/-- Pointwise facts about the rounding `R_θ`, `θ = 2k`, on a positive rational `z` that is an
integer whenever `z ≤ k`. -/
theorem cell_pt (θ k : ℕ) (hθ : θ / 2 = k) (z : ℚ) (hz0 : 0 < z)
    (hint : z ≤ k → ∃ a : ℕ, z = a) :
    ((roundCell θ z : ℕ) : ℚ) ≤ z ∧
    z ≤ (if roundCell θ z < k then ((roundCell θ z : ℕ) : ℚ) else ((roundCell θ z : ℕ) : ℚ) + 1) ∧
    (roundCell θ z < k ↔ z < k) ∧
    (if roundCell θ z < k then (1 : ℚ) / ((roundCell θ z : ℕ) : ℚ)
      else 1 / (((roundCell θ z : ℕ) : ℚ) + 1)) ≤ 1 / z := by
  by_cases hzk : z ≤ k
  · obtain ⟨a, rfl⟩ := hint hzk
    have hr : roundCell θ (a : ℚ) = a := by
      unfold roundCell
      rw [hθ, if_pos hzk]; simp
    rw [hr]
    refine ⟨le_rfl, ?_, ?_, ?_⟩
    · split_ifs <;> linarith
    · simp
    · split_ifs
      · exact le_rfl
      · exact one_div_le_one_div_of_le hz0 (by linarith)
  · have hkz : (k : ℚ) < z := not_le.mp hzk
    have hr : roundCell θ z = ⌈z⌉₊ - 1 := by
      unfold roundCell
      rw [hθ, if_neg hzk]
    have hk1 : k + 1 ≤ ⌈z⌉₊ := Nat.lt_ceil.mpr hkz
    have hc : ¬ roundCell θ z < k := by omega
    have hcast : ((roundCell θ z : ℕ) : ℚ) = (⌈z⌉₊ : ℚ) - 1 := by
      rw [hr, Nat.cast_sub (by omega)]; simp
    have h1 : (⌈z⌉₊ : ℚ) < z + 1 := Nat.ceil_lt_add_one hz0.le
    have h2 : z ≤ (⌈z⌉₊ : ℚ) := Nat.le_ceil z
    simp only [if_neg hc, hcast]
    refine ⟨by linarith, by linarith, ?_, ?_⟩
    · constructor
      · intro h; exact absurd h hc
      · intro h; linarith
    · have : (⌈z⌉₊ : ℚ) - 1 + 1 = ⌈z⌉₊ := by ring
      rw [this]
      exact one_div_le_one_div_of_le hz0 h2

theorem densityQ_toQ (A : List ℕ) : densityQ (toQ A) = density A := by
  induction A with
  | nil => simp [densityQ, density, toQ]
  | cons a t ih =>
    have h1 : toQ (a :: t) = (a : ℚ) :: toQ t := by simp [toQ]
    have h2 : density (a :: t) = 1 / (a : ℚ) + density t := by simp [density]
    rw [h1, h2, densityQ_cons, ih]

theorem toQ_filter (k : ℕ) (A : List ℕ) :
    (toQ A).filter (fun z => decide (z < (k : ℚ))) = toQ (A.filter (fun a => decide (a < k))) := by
  induction A with
  | nil => rfl
  | cons a t ih =>
    simp only [toQ_eq, List.map_cons, List.filter_cons, Nat.cast_lt] at ih ⊢
    split_ifs <;> simp [ih]

theorem roundCell_natCast (θ k : ℕ) (hθ : θ / 2 = k) (a : ℕ) (ha : a < k) :
    roundCell θ (a : ℚ) = a := by
  unfold roundCell
  rw [hθ, if_pos (by exact_mod_cast ha.le)]; simp

theorem toQ_map_round (θ k : ℕ) (hθ : θ / 2 = k) :
    ∀ A' : List ℕ, (∀ a ∈ A', a < k) → (toQ A').map (roundCell θ) = A' := by
  intro A'
  induction A' with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    have := ih (fun x hx => h x (by simp [hx]))
    simp only [toQ_eq, List.map_cons] at this ⊢
    rw [roundCell_natCast θ k hθ a (h a (by simp)), this]

theorem main (m : ℕ) (hm : 1 ≤ m) (B : ℚ) (θ : ℕ) (hθ : Even θ) (hθ4 : 4 ≤ θ)
    (A : List ℕ) (hA : IsTarget m B A) :
    IsBoxMember (rootLo (cellOf θ A)) (rootUp θ (cellOf θ A)) (beta B θ) (foldOf θ A) ∧
    weight θ (cellOf θ A) < beta B θ ∧
    ((cellOf θ A).filter (fun x => x < θ / 2)).Perm (A.filter (fun x => x < θ / 2)) ∧
    (RatSchedulable (foldOf θ A) → RatSchedulable (toQ A)) := by
  obtain ⟨k, hk⟩ := hθ
  have hθk : θ / 2 = k := by omega
  have hθpos : (0 : ℚ) < θ := by exact_mod_cast (by omega : 0 < θ)
  have hθq : (θ : ℚ) / 2 = k := by
    have : (θ : ℚ) = k + k := by exact_mod_cast hk
    rw [this]; ring
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
  have hbdef : foldOf θ A = sortQ (foldDown (θ : ℚ) l) := rfl
  obtain ⟨hFs, hFp⟩ := foldDown_sorted_pos_le hθpos l hlsorted hlpos
  obtain ⟨N, hFN, hN⟩ := foldDown_orig hθpos l hlsorted
  set F := foldDown (θ : ℚ) l with hF
  set b := foldOf θ A with hb
  have hbF : b.Perm F := by rw [hbdef]; exact sortQ_perm F
  have hbmem : ∀ z ∈ b, z ∈ F := fun z hz => hbF.mem_iff.mp hz
  -- every entry of `b`
  have hz : ∀ z ∈ b, 0 < z ∧ (z ≤ k → ∃ a : ℕ, z = a) := by
    intro z zb
    have zF := hbmem z zb
    refine ⟨(hFp z zF).1, fun hzk => ?_⟩
    rcases List.mem_append.mp (hFN.mem_iff.mp zF) with h | h
    · obtain ⟨a, _, rfl⟩ := hmemA z (List.mem_filter.mp h).1
      exact ⟨a, rfl⟩
    · have := (hN z h).1
      rw [hθq] at this
      linarith
  have hpt := fun z (zb : z ∈ b) => cell_pt θ k hθk z (hz z zb).1 (hz z zb).2
  have hcell : cellOf θ A = b.map (roundCell θ) := rfl
  -- density bound
  have hdens : densityQ b < beta B θ := by
    rw [densityQ_perm hbF]
    have h1 := foldDown_dens hθpos l hlsorted hlpos
    have h2 : densityQ l = density A := by
      rw [densityQ_perm hlperm]
      exact densityQ_toQ A
    unfold beta
    have := hA.2
    linarith
  refine ⟨⟨?_, ?_, fun x hx => (hz x hx).1, hdens⟩, ?_, ?_, ?_⟩
  · -- lower bounds
    have : rootLo (cellOf θ A) = b.map (fun z => ((roundCell θ z : ℕ) : ℚ)) := by
      unfold rootLo; rw [toQ_eq, hcell, List.map_map]; rfl
    rw [this]
    exact leAll_map_left b _ (fun z zb => (hpt z zb).1)
  · have : rootUp θ (cellOf θ A) = b.map (fun z =>
        if roundCell θ z < k then ((roundCell θ z : ℕ) : ℚ) else ((roundCell θ z : ℕ) : ℚ) + 1) := by
      unfold rootUp; rw [hcell, List.map_map, hθk]; rfl
    rw [this]
    exact leAll_map_right b _ (fun z zb => (hpt z zb).2.1)
  · -- weight
    have : weight θ (cellOf θ A) = (b.map (fun z =>
        if roundCell θ z < k then (1 : ℚ) / ((roundCell θ z : ℕ) : ℚ)
        else 1 / (((roundCell θ z : ℕ) : ℚ) + 1))).sum := by
      unfold weight; rw [hcell, List.map_map, hθk]; rfl
    rw [this]
    have h2 : (b.map (fun z =>
        if roundCell θ z < k then (1 : ℚ) / ((roundCell θ z : ℕ) : ℚ)
        else 1 / (((roundCell θ z : ℕ) : ℚ) + 1))).sum ≤ densityQ b := by
      unfold densityQ
      exact List.sum_le_sum (fun z zb => (hpt z zb).2.2.2)
    linarith
  · -- small entries
    simp only [hθk]
    rw [hcell, List.filter_map]
    have hfc : b.filter ((fun x => decide (x < k)) ∘ roundCell θ) = b.filter (fun z => decide (z < (k : ℚ))) := by
      refine List.filter_congr (fun z zb => ?_)
      simp only [Function.comp_apply, decide_eq_decide]
      exact (hpt z zb).2.2.1
    rw [hfc]
    have hbk : (b.filter (fun z => decide (z < (k : ℚ)))).Perm (toQ (A.filter (fun a => decide (a < k)))) := by
      have h1 := (hbF.filter (fun z => decide (z < (k : ℚ)))).trans
        ((hFN.filter (fun z => decide (z < (k : ℚ)))))
      refine h1.trans ?_
      rw [List.filter_append]
      have hN0 : N.filter (fun z => decide (z < (k : ℚ))) = [] := by
        rw [List.filter_eq_nil_iff]
        intro z zN
        have := (hN z zN).1
        rw [hθq] at this
        simpa using this.le
      rw [hN0, List.append_nil, List.filter_filter]
      have : (l.filter (fun a => decide (a < (k : ℚ)) && decide (a ≤ (θ : ℚ)))) =
          l.filter (fun z => decide (z < (k : ℚ))) := by
        refine List.filter_congr (fun z zl => ?_)
        have hkθ : (k : ℚ) ≤ θ := by rw [← hθq]; linarith
        by_cases h : z < (k : ℚ)
        · simp [h, h.le.trans hkθ]
        · simp [h]
      rw [this]
      rw [← toQ_filter]
      exact hlperm.filter _
    have := hbk.map (roundCell θ)
    refine this.trans (List.Perm.of_eq ?_)
    exact toQ_map_round θ k hθk _ (fun a ha => by simpa using (List.mem_filter.mp ha).2)
  · intro h
    have h1 : RatSchedulable F := RatSchedulable.perm hbF h
    have h2 := foldDown_sched hθpos l hlsorted hlpos h1
    exact RatSchedulable.perm hlperm h2

end PinwheelDensity.ExactRange.Dev.LB1

namespace PinwheelDensity.ExactRange

theorem chk_lemma_B_1 (m : ℕ) (hm : 1 ≤ m) (B : ℚ) (hB0 : 0 ≤ B) (hB1 : B ≤ 1)
    (θ : ℕ) (hθ : Even θ) (hθ4 : 4 ≤ θ) (A : List ℕ) (hA : IsTarget m B A) :
    IsBoxMember (rootLo (cellOf θ A)) (rootUp θ (cellOf θ A)) (beta B θ) (foldOf θ A) ∧
    weight θ (cellOf θ A) < beta B θ ∧
    ((cellOf θ A).filter (fun x => x < θ / 2)).Perm (A.filter (fun x => x < θ / 2)) ∧
    (RatSchedulable (foldOf θ A) → RatSchedulable (toQ A)) :=
  Dev.LB1.main m hm B θ hθ hθ4 A hA

end PinwheelDensity.ExactRange
end

theorem solution : type_of% @PinwheelDensity.ExactRange.chk_lemma_B_1 := @PinwheelDensity.ExactRange.chk_lemma_B_1
