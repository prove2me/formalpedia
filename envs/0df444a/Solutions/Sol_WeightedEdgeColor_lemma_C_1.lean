-- Prove2me | solution 1 for WeightedEdgeColor.lemma_C_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T07:53:43.220089+00:00
-- url     : https://prove2.me/submissions/20481350-3b09-4bc4-98ed-7ef99f6fff18

import Mathlib
import Definitions.Def_WeightedEdgeColor_IsAvgOfFeasibleSets

set_option autoImplicit false
set_option maxHeartbeats 0

namespace WECC1

/-- Fractional transport for nested compatibility (Hall's condition at every threshold). -/
theorem transport_aux {I Sl : Type} [Fintype I] [Fintype Sl] [DecidableEq I]
    (d w : I → ℝ) (c b : Sl → ℝ) (hd : ∀ e, 0 ≤ d e) (hc : ∀ s, 0 ≤ c s) :
    ∀ (k : ℕ) (T : Finset I), T.card = k →
      (∀ e₀ ∈ T, ∑ e ∈ T.filter (fun e => w e₀ ≤ w e), d e ≤
        ∑ s ∈ Finset.univ.filter (fun s => w e₀ ≤ b s), c s) →
      ∃ a : I → Sl → ℝ, (∀ e s, 0 ≤ a e s) ∧ (∀ e ∈ T, ∑ s, a e s = d e) ∧
        (∀ e ∉ T, ∀ s, a e s = 0) ∧ (∀ s, ∑ e, a e s ≤ c s) ∧ (∀ e s, a e s ≠ 0 → w e ≤ b s) := by
  intro k
  induction k with
  | zero =>
    intro T hT _
    rw [Finset.card_eq_zero] at hT
    subst hT
    exact ⟨fun _ _ => 0, fun _ _ => le_refl _, by simp, fun _ _ _ => rfl,
      fun s => by simp [hc s], fun _ _ h => absurd rfl h⟩
  | succ k ih =>
    intro T hT hall
    have hne : T.Nonempty := by rw [← Finset.card_pos, hT]; omega
    obtain ⟨e₀, he₀, hmin⟩ := T.exists_min_image w hne
    set T' := T.erase e₀
    have hT' : T'.card = k := by rw [Finset.card_erase_of_mem he₀, hT]; rfl
    have hall' : ∀ e₁ ∈ T', ∑ e ∈ T'.filter (fun e => w e₁ ≤ w e), d e ≤
        ∑ s ∈ Finset.univ.filter (fun s => w e₁ ≤ b s), c s := by
      intro e₁ he₁
      refine le_trans ?_ (hall e₁ (Finset.mem_of_mem_erase he₁))
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro e he
        simp only [Finset.mem_filter] at he ⊢
        exact ⟨Finset.mem_of_mem_erase he.1, he.2⟩
      · intro e _ _; exact hd e
    obtain ⟨a', ha'0, ha'T, ha'out, ha'cap, ha'comp⟩ := ih T' hT' hall'
    -- residual capacities
    let r : Sl → ℝ := fun s => c s - ∑ e, a' e s
    have hr0 : ∀ s, 0 ≤ r s := fun s => by simp only [r]; linarith [ha'cap s]
    set Sl₀ := Finset.univ.filter (fun s => w e₀ ≤ b s)
    have hres : d e₀ ≤ ∑ s ∈ Sl₀, r s := by
      have h1 := hall e₀ he₀
      have hfilt : T.filter (fun e => w e₀ ≤ w e) = T := by
        rw [Finset.filter_true_of_mem]; intro e he; exact hmin e he
      rw [hfilt, ← Finset.add_sum_erase T d he₀] at h1
      have h2 : ∑ s ∈ Sl₀, ∑ e, a' e s ≤ ∑ e ∈ T', d e := by
        rw [Finset.sum_comm]
        calc ∑ e, ∑ s ∈ Sl₀, a' e s = ∑ e ∈ T', ∑ s ∈ Sl₀, a' e s := by
              rw [← Finset.sum_subset (Finset.subset_univ T')]
              intro e _ he
              exact Finset.sum_eq_zero (fun s _ => ha'out e he s)
          _ ≤ ∑ e ∈ T', ∑ s, a' e s := by
              apply Finset.sum_le_sum; intro e _
              exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                (fun s _ _ => ha'0 e s)
          _ = ∑ e ∈ T', d e := Finset.sum_congr rfl (fun e he => ha'T e he)
      have h3 : ∑ s ∈ Sl₀, r s = ∑ s ∈ Sl₀, c s - ∑ s ∈ Sl₀, ∑ e, a' e s := by
        rw [← Finset.sum_sub_distrib]
      linarith
    set ρ := ∑ s ∈ Sl₀, r s
    let a : I → Sl → ℝ := fun e s =>
      if e = e₀ then (if w e₀ ≤ b s then d e₀ * r s / ρ else 0) else a' e s
    refine ⟨a, ?_, ?_, ?_, ?_, ?_⟩
    · intro e s
      simp only [a]
      split_ifs
      · have hρ0 : 0 ≤ ρ := Finset.sum_nonneg (fun s _ => hr0 s)
        exact div_nonneg (mul_nonneg (hd e₀) (hr0 s)) hρ0
      · exact le_refl _
      · exact ha'0 e s
    · intro e he
      by_cases h : e = e₀
      · subst h
        simp only [a, if_true]
        rw [← Finset.sum_filter]
        change ∑ s ∈ Sl₀, d e * r s / ρ = d e
        rcases (Finset.sum_nonneg (fun s _ => hr0 s) : (0 : ℝ) ≤ ρ).lt_or_eq with hρ | hρ
        · rw [← Finset.sum_div, ← Finset.mul_sum]
          exact mul_div_cancel_right₀ (d e) (ne_of_gt hρ)
        · have : d e = 0 := le_antisymm (by rw [hρ]; exact hres) (hd e)
          simp [this]
      · simp only [a, h, if_false]
        exact ha'T e (Finset.mem_erase.mpr ⟨h, he⟩)
    · intro e he s
      have h : e ≠ e₀ := fun h => he (h ▸ he₀)
      simp only [a, h, if_false]
      exact ha'out e (fun h' => he (Finset.mem_of_mem_erase h')) s
    · intro s
      have hsplit : ∑ e, a e s = a e₀ s + ∑ e ∈ Finset.univ.erase e₀, a' e s := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e₀)]
        congr 1
        apply Finset.sum_congr rfl
        intro e he
        simp [a, Finset.ne_of_mem_erase he]
      have ha'e₀ : a' e₀ s = 0 := ha'out e₀ (Finset.notMem_erase e₀ T) s
      have hsum' : ∑ e ∈ Finset.univ.erase e₀, a' e s = ∑ e, a' e s := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e₀), ha'e₀, zero_add]
      rw [hsplit, hsum']
      simp only [a, if_true]
      split_ifs with hb
      · have hρ0 : 0 ≤ ρ := Finset.sum_nonneg (fun s _ => hr0 s)
        rcases hρ0.lt_or_eq with hρ | hρ
        · have : d e₀ * r s / ρ ≤ r s := by
            rw [div_le_iff₀ hρ]
            exact mul_le_mul_of_nonneg_right hres (hr0 s) |>.trans_eq (mul_comm _ _)
          simp only [r] at this ⊢
          linarith
        · have : d e₀ * r s / ρ = 0 := by rw [show ρ = 0 from hρ.symm]; simp
          rw [this, zero_add]; exact ha'cap s
      · simp only [zero_add]; exact ha'cap s
    · intro e s h
      by_cases he : e = e₀
      · subst he
        simp only [a, if_true] at h
        split_ifs at h with hb
        · exact hb
        · exact absurd rfl h
      · simp only [a, he, if_false] at h
        exact ha'comp e s h

theorem transport {I Sl : Type} [Fintype I] [Fintype Sl] [DecidableEq I]
    (d w : I → ℝ) (c b : Sl → ℝ) (hd : ∀ e, 0 ≤ d e) (hc : ∀ s, 0 ≤ c s)
    (hall : ∀ e₀, ∑ e ∈ Finset.univ.filter (fun e => w e₀ ≤ w e), d e ≤
        ∑ s ∈ Finset.univ.filter (fun s => w e₀ ≤ b s), c s) :
    ∃ a : I → Sl → ℝ, (∀ e s, 0 ≤ a e s) ∧ (∀ e, ∑ s, a e s = d e) ∧
      (∀ s, ∑ e, a e s ≤ c s) ∧ (∀ e s, a e s ≠ 0 → w e ≤ b s) := by
  obtain ⟨a, h0, hT, -, hcap, hcomp⟩ := transport_aux d w c b hd hc _ Finset.univ rfl
    (fun e₀ _ => hall e₀)
  exact ⟨a, h0, fun e => hT e (Finset.mem_univ e), hcap, hcomp⟩

/-- Kept sizes: boundedly many sizes such that rounding down loses mass at most `q` at every
threshold. -/
theorem kept_sizes {I : Type} [Fintype I] [DecidableEq I] (w m : I → ℝ) (hm : ∀ e, 0 ≤ m e)
    (q : ℝ) (hq : 0 < q) :
    ∃ Kept : Finset ℝ, Kept.card ≤ ⌊(∑ e, m e) / q⌋₊ + 2 ∧
      (∀ e, ∃ k ∈ Kept, k ≤ w e) ∧ (∀ k ∈ Kept, ∃ e, w e = k) ∧
      ∀ τ : ℝ, ∑ e ∈ Finset.univ.filter (fun e => τ ≤ w e ∧ ∀ k ∈ Kept, k ≤ w e → k < τ), m e ≤ q := by
  classical
  rcases isEmpty_or_nonempty I with hI | hI
  · refine ⟨∅, by simp, fun e => isEmptyElim e, by simp, fun τ => ?_⟩
    simp [hq.le]
  set Wset : Finset ℝ := Finset.univ.image w with hWset
  have hWne : Wset.Nonempty := Finset.univ_nonempty.image w
  set F : ℝ → ℝ := fun b => ∑ e ∈ Finset.univ.filter (fun e => b < w e), m e with hF
  set G : ℝ → ℝ := fun b => ∑ e ∈ Finset.univ.filter (fun e => b ≤ w e), m e with hG
  set X := ∑ e, m e
  have hF0 : ∀ b, 0 ≤ F b := fun b => Finset.sum_nonneg (fun e _ => hm e)
  have hGX : ∀ b, G b ≤ X := fun b =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun e _ _ => hm e)
  have hFG : ∀ b, F b ≤ G b := fun b =>
    Finset.sum_le_sum_of_subset_of_nonneg (fun e he => by
      simp only [Finset.mem_filter] at he ⊢; exact ⟨he.1, he.2.le⟩) (fun e _ _ => hm e)
  have hGanti : ∀ b b', b ≤ b' → G b' ≤ G b := fun b b' h =>
    Finset.sum_le_sum_of_subset_of_nonneg (fun e he => by
      simp only [Finset.mem_filter] at he ⊢; exact ⟨he.1, le_trans h he.2⟩) (fun e _ _ => hm e)
  have hFanti : ∀ b b', b ≤ b' → F b' ≤ F b := fun b b' h =>
    Finset.sum_le_sum_of_subset_of_nonneg (fun e he => by
      simp only [Finset.mem_filter] at he ⊢; exact ⟨he.1, lt_of_le_of_lt h he.2⟩) (fun e _ _ => hm e)
  have hGF : ∀ b b', b < b' → G b' ≤ F b := fun b b' h =>
    Finset.sum_le_sum_of_subset_of_nonneg (fun e he => by
      simp only [Finset.mem_filter] at he ⊢; exact ⟨he.1, lt_of_lt_of_le h he.2⟩) (fun e _ _ => hm e)
  set mx := Wset.max' hWne
  set mn := Wset.min' hWne
  set Kmid := Wset.filter (fun b => ∃ k : ℕ, F b < k * q ∧ k * q ≤ G b)
  set Kept := insert mx (insert mn Kmid)
  have hKeptW : ∀ k ∈ Kept, k ∈ Wset := by
    intro k hk
    simp only [Kept, Finset.mem_insert] at hk
    rcases hk with rfl | rfl | hk
    · exact Finset.max'_mem _ _
    · exact Finset.min'_mem _ _
    · exact (Finset.mem_filter.mp hk).1
  refine ⟨Kept, ?_, ?_, ?_, ?_⟩
  · -- the number of kept sizes
    have hmid : Kmid.card ≤ ⌊X / q⌋₊ := by
      have hmaps : ∀ b ∈ Kmid, ⌊G b / q⌋₊ ∈ Finset.Icc 1 ⌊X / q⌋₊ := by
        intro b hb
        obtain ⟨k, hk1, hk2⟩ := (Finset.mem_filter.mp hb).2
        rw [Finset.mem_Icc]
        constructor
        · have hk0 : 0 < (k : ℝ) * q := lt_of_le_of_lt (hF0 b) hk1
          have hk : 1 ≤ k := by
            rcases Nat.eq_zero_or_pos k with h | h
            · subst h; simp at hk0
            · exact h
          have : k ≤ ⌊G b / q⌋₊ := Nat.le_floor (by rw [le_div_iff₀ hq]; exact hk2)
          omega
        · exact Nat.floor_le_floor (div_le_div_of_nonneg_right (hGX b) hq.le)
      have hinj : Set.InjOn (fun b => ⌊G b / q⌋₊) Kmid := by
        intro b hb b' hb' h
        simp only at h
        by_contra hne
        have key : ∀ x y, x ∈ Kmid → y ∈ Kmid → x < y → ⌊G y / q⌋₊ < ⌊G x / q⌋₊ := by
          intro x y hx hy hxy
          obtain ⟨k, hk1, hk2⟩ := (Finset.mem_filter.mp hx).2
          have h1 : (⌊G y / q⌋₊ : ℝ) * q ≤ G y := by
            have := Nat.floor_le (div_nonneg (le_trans (hF0 y) (hFG y)) hq.le)
            rwa [le_div_iff₀ hq] at this
          have h2 : G y ≤ F x := hGF x y hxy
          have h3 : k ≤ ⌊G x / q⌋₊ := Nat.le_floor (by rw [le_div_iff₀ hq]; exact hk2)
          have h4 : (⌊G y / q⌋₊ : ℝ) * q < k * q := by linarith
          have h5 : ⌊G y / q⌋₊ < k := by
            have := (mul_lt_mul_iff_of_pos_right hq).mp h4
            exact_mod_cast this
          omega
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · exact absurd h (ne_of_gt (key b b' hb hb' hlt))
        · exact absurd h (ne_of_lt (key b' b hb' hb hlt))
      have := Finset.card_le_card_of_injOn _ hmaps hinj
      simpa using this
    calc Kept.card ≤ (insert mn Kmid).card + 1 := Finset.card_insert_le _ _
      _ ≤ Kmid.card + 1 + 1 := by gcongr; exact Finset.card_insert_le _ _
      _ ≤ ⌊X / q⌋₊ + 2 := by omega
  · intro e
    refine ⟨mn, by simp [Kept], ?_⟩
    exact Finset.min'_le _ _ (Finset.mem_image_of_mem w (Finset.mem_univ e))
  · intro k hk
    obtain ⟨e, -, he⟩ := Finset.mem_image.mp (hKeptW k hk)
    exact ⟨e, he⟩
  · intro τ
    set L := Finset.univ.filter (fun e => τ ≤ w e ∧ ∀ k ∈ Kept, k ≤ w e → k < τ)
    rcases L.eq_empty_or_nonempty with hL | ⟨e₁, he₁⟩
    · rw [hL]; simp [hq.le]
    have he₁' := (Finset.mem_filter.mp he₁).2
    -- the smallest kept size at least `τ`
    have hup : (Kept.filter (fun k => τ ≤ k)).Nonempty := by
      refine ⟨mx, Finset.mem_filter.mpr ⟨by simp [Kept], ?_⟩⟩
      exact le_trans he₁'.1 (Finset.le_max' _ _ (Finset.mem_image_of_mem w (Finset.mem_univ e₁)))
    set bp := (Kept.filter (fun k => τ ≤ k)).min' hup
    have hbp_mem := Finset.mem_filter.mp (Finset.min'_mem _ hup)
    have hbp_min : ∀ k ∈ Kept, τ ≤ k → bp ≤ k := fun k hk hτk =>
      Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hk, hτk⟩)
    -- the largest kept size below `τ`
    have hdown : (Kept.filter (fun k => k < τ)).Nonempty := by
      refine ⟨mn, Finset.mem_filter.mpr ⟨by simp [Kept], ?_⟩⟩
      exact he₁'.2 mn (by simp [Kept])
        (Finset.min'_le _ _ (Finset.mem_image_of_mem w (Finset.mem_univ e₁)))
    set bm := (Kept.filter (fun k => k < τ)).max' hdown
    have hbm_mem := Finset.mem_filter.mp (Finset.max'_mem _ hdown)
    have hbm_max : ∀ k ∈ Kept, k < τ → k ≤ bm := fun k hk hkτ =>
      Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hk, hkτ⟩)
    -- the lost items lie strictly between `bm` and `bp`
    have hLsub : L ⊆ Finset.univ.filter (fun e => bm < w e ∧ w e < bp) := by
      intro e he
      have he' := (Finset.mem_filter.mp he).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact lt_of_lt_of_le hbm_mem.2 he'.1
      · by_contra h
        push Not at h
        exact absurd (he'.2 bp hbp_mem.1 h) (not_lt.mpr hbp_mem.2)
    have hmassL : ∑ e ∈ L, m e ≤ F bm - G bp := by
      have h1 : ∑ e ∈ L, m e ≤ ∑ e ∈ Finset.univ.filter (fun e => bm < w e ∧ w e < bp), m e :=
        Finset.sum_le_sum_of_subset_of_nonneg hLsub (fun e _ _ => hm e)
      have h2 : F bm = ∑ e ∈ Finset.univ.filter (fun e => bm < w e ∧ w e < bp), m e + G bp := by
        simp only [hF, hG]
        rw [← Finset.sum_union]
        · apply Finset.sum_congr _ (fun _ _ => rfl)
          ext e
          simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
          constructor
          · intro h
            by_cases h' : w e < bp
            · exact Or.inl ⟨h, h'⟩
            · exact Or.inr (not_lt.mp h')
          · rintro (h | h)
            · exact h.1
            · exact lt_of_lt_of_le (lt_of_lt_of_le hbm_mem.2 hbp_mem.2) h
        · rw [Finset.disjoint_left]
          intro e h1 h2
          simp only [Finset.mem_filter] at h1 h2
          linarith [h1.2.2, h2.2]
      linarith
    -- the gap between consecutive kept sizes carries less than `q`
    by_contra hcon
    push Not at hcon
    have hgap : G bp + q ≤ F bm := by linarith
    set k : ℕ := ⌊G bp / q⌋₊ + 1 with hk
    have hk1 : G bp < k * q := by
      have := Nat.lt_floor_add_one (G bp / q)
      rw [div_lt_iff₀ hq] at this
      rw [hk]; push_cast; linarith
    have hk2 : (k : ℝ) * q ≤ F bm := by
      have := Nat.floor_le (div_nonneg (le_trans (hF0 bp) (hFG bp)) hq.le)
      rw [le_div_iff₀ hq] at this
      rw [hk]; push_cast; linarith
    have hset : (Wset.filter (fun b => (k : ℝ) * q ≤ G b)).Nonempty :=
      ⟨bm, Finset.mem_filter.mpr ⟨hKeptW bm hbm_mem.1, le_trans hk2 (hFG bm)⟩⟩
    set bs := (Wset.filter (fun b => (k : ℝ) * q ≤ G b)).max' hset
    have hbs_mem := Finset.mem_filter.mp (Finset.max'_mem _ hset)
    have hbs_max : ∀ b ∈ Wset, (k : ℝ) * q ≤ G b → b ≤ bs := fun b hb hb' =>
      Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hb, hb'⟩)
    have hFbs : F bs < k * q := by
      by_contra h
      push Not at h
      have hpos : 0 < F bs := lt_of_lt_of_le (by have := hk1; have := le_trans (hF0 bp) (hFG bp); nlinarith) h
      have hne : (Finset.univ.filter (fun e => bs < w e)).Nonempty := by
        by_contra h0
        rw [Finset.not_nonempty_iff_eq_empty] at h0
        have : F bs = 0 := by simp only [hF]; rw [h0, Finset.sum_empty]
        linarith
      set b' := ((Finset.univ.filter (fun e => bs < w e)).image w).min' (hne.image w)
      have hb'mem := Finset.mem_image.mp (Finset.min'_mem _ (hne.image w))
      obtain ⟨e', he', hwe0⟩ := hb'mem
      have hwe' : w e' = b' := hwe0
      have hb'gt : bs < b' := by rw [← hwe']; exact (Finset.mem_filter.mp he').2
      have hGb' : G b' = F bs := by
        simp only [hF, hG]
        apply Finset.sum_congr _ (fun _ _ => rfl)
        ext e
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h; exact lt_of_lt_of_le hb'gt h
        · intro h
          exact Finset.min'_le _ _ (Finset.mem_image_of_mem w (Finset.mem_filter.mpr
            ⟨Finset.mem_univ e, h⟩))
      have := hbs_max b' (by rw [← hwe']; exact Finset.mem_image_of_mem w (Finset.mem_univ e'))
        (by rw [hGb']; exact h)
      linarith
    have hbs_kept : bs ∈ Kept := by
      simp only [Kept, Finset.mem_insert]
      right; right
      exact Finset.mem_filter.mpr ⟨hbs_mem.1, k, hFbs, hbs_mem.2⟩
    have hbs_lt_bp : bs < bp := by
      by_contra h
      push Not at h
      have := hGanti bp bs h
      linarith [hbs_mem.2]
    have hbm_lt_bs : bm < bs := by
      by_contra h
      push Not at h
      have := hFanti bs bm h
      linarith
    have hτbs : τ ≤ bs := by
      by_contra h
      push Not at h
      have := hbm_max bs hbs_kept h
      linarith
    have := hbp_min bs hbs_kept hτbs
    linarith

end WECC1

open WeightedEdgeColor WECC1

theorem solution (δ β : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hβ0 : 0 < β) (hβ : β ≤ δ / 4) :
    ∃ M : ℕ, ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w x : ι → ℝ),
      (∀ e, 0 < w e) → (∀ e, w e ≤ 1) → IsAvgOfFeasibleSets w x →
      ∃ (lam : Fin M → ℝ) (b : Fin M → Fin ⌊1 / β⌋₊ → ℝ) (R : Fin M → ℝ)
        (aL : ι → Fin M → Fin ⌊1 / β⌋₊ → ℝ) (aS : ι → Fin M → ℝ),
        -- valid profiles
        (∀ P, (∀ i, 0 ≤ b P i) ∧ 0 ≤ R P ∧ ∑ i, b P i + R P ≤ 1) ∧
        -- probabilities
        (∀ P, 0 ≤ lam P) ∧ ∑ P, lam P = 1 ∧
        -- nonnegative assigned fractions
        (∀ e P i, 0 ≤ aL e P i) ∧ (∀ e P, 0 ≤ aS e P) ∧
        -- (C.1)
        (∀ e, ∑ P, (∑ i, aL e P i + aS e P) = (1 - δ) * x e) ∧
        -- (C.2)
        (∀ P i, ∑ e, aL e P i ≤ lam P) ∧
        -- (C.3)
        (∀ P, ∑ e ∈ Finset.univ.filter (fun e => w e < β), w e * aS e P ≤ lam P * R P) ∧
        -- large items only in slots that can hold their weight
        (∀ e P i, aL e P i ≠ 0 → β ≤ w e ∧ w e ≤ b P i) ∧
        -- small items only in positive reserved spaces
        (∀ e P, aS e P ≠ 0 → w e < β ∧ 0 < R P) ∧
        -- every positive reserved space has size at least r₀ = δ/4
        (∀ P, R P = 0 ∨ δ / 4 ≤ R P) ∧
        -- every individual assigned fraction is at most y_e = (1 - δ) x_e
        (∀ e P i, aL e P i ≤ (1 - δ) * x e) ∧ (∀ e P, aS e P ≤ (1 - δ) * x e) 
:= by
  classical
  -- fixed constants
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌊1 / β⌋₊ := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = δ / 4 := ⟨_, rfl⟩
  have hq0 : 0 < q := by rw [hq]; positivity
  have hβq : β ≤ q := by rw [hq]; exact hβ
  have hK1 : 1 ≤ K := by
    rw [hK]; apply Nat.le_floor; rw [Nat.cast_one, le_div_iff₀ hβ0]; linarith
  obtain ⟨Lk, hLk⟩ : ∃ L : ℕ, L = ⌊(K : ℝ) / q⌋₊ + 2 := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, J = ⌊1 / q⌋₊ := ⟨_, rfl⟩
  let TS := (Fin K → Fin (Lk + 1)) × Fin (J + 1)
  let Lbl := TS ⊕ Fin 3
  refine ⟨Fintype.card Lbl, ?_⟩
  intro ι _ _ w x hw0 hw1 hx
  obtain ⟨p, hp0, hp1, hpf, hpx⟩ := hx
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = 1 - δ := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; linarith
  have hs1 : s ≤ 1 := by rw [hs]; linarith
  let lg : ι → Prop := fun e => β ≤ w e
  have hx0 : ∀ e, 0 ≤ x e := fun e => by rw [hpx e]; exact Finset.sum_nonneg (fun S _ => hp0 S)
  -- exchanging items and sets
  have hswap : ∀ f : ι → ℝ, ∑ e, f e * x e = ∑ S, p S * ∑ e ∈ S, f e := by
    intro f
    simp_rw [hpx, Finset.mul_sum, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro S _
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    apply Finset.sum_congr rfl; intro e _; ring
  -- large items of a feasible set
  have hcardL : ∀ S : Finset ι, p S ≠ 0 → (S.filter lg).card ≤ K := by
    intro S hS
    have h1 := hpf S hS
    have h2 : ((S.filter lg).card : ℝ) * β ≤ ∑ e ∈ S, w e := by
      calc ((S.filter lg).card : ℝ) * β = ∑ e ∈ S.filter lg, β := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ e ∈ S.filter lg, w e := Finset.sum_le_sum (fun e he => (Finset.mem_filter.mp he).2)
        _ ≤ ∑ e ∈ S, w e := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun e _ _ => (hw0 e).le)
    rw [hK]; apply Nat.le_floor; rw [le_div_iff₀ hβ0]; linarith
  have hXK : ∑ e : {e // lg e}, x e ≤ K := by
    rw [← Finset.sum_subtype (p := lg) (Finset.univ.filter lg) (by simp) x]
    have := hswap (fun e => if lg e then 1 else 0)
    simp only [ite_mul, one_mul, zero_mul, ← Finset.sum_filter] at this
    rw [this]
    calc ∑ S, p S * ∑ e ∈ S.filter lg, (1 : ℝ) ≤ ∑ S, p S * K := by
          apply Finset.sum_le_sum; intro S _
          rcases eq_or_ne (p S) 0 with h | h
          · rw [h]; simp
          · apply mul_le_mul_of_nonneg_left _ (hp0 S)
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
            exact_mod_cast hcardL S h
      _ = K := by rw [← Finset.sum_mul, hp1, one_mul]
  -- kept sizes
  obtain ⟨Kept, hKcard, hKbelow, hKinW, hKlost⟩ :=
    kept_sizes (I := {e // lg e}) (fun e => w e) (fun e => x e) (fun e => hx0 e) q hq0
  have hKLk : Kept.card ≤ Lk := by
    refine le_trans hKcard ?_
    rw [hLk]
    have : ⌊(∑ e : {e // lg e}, x e) / q⌋₊ ≤ ⌊(K : ℝ) / q⌋₊ :=
      Nat.floor_le_floor (div_le_div_of_nonneg_right hXK hq0.le)
    omega
  have hKpos : ∀ k ∈ Kept, 0 < k := by
    intro k hk
    obtain ⟨e, he⟩ := hKinW k hk
    rw [← he]; exact hw0 e
  obtain ⟨eK, -⟩ : ∃ eK : Kept ≃ Fin Kept.card, True := ⟨Kept.equivFin, trivial⟩
  let sz : Fin (Lk + 1) → ℝ := fun j =>
    if h : 1 ≤ j.val ∧ j.val - 1 < Kept.card then ((eK.symm ⟨j.val - 1, h.2⟩ : Kept) : ℝ) else 0
  let idxv : ℝ → Fin (Lk + 1) := fun v =>
    if h : v ∈ Kept then ⟨(eK ⟨v, h⟩).val + 1, by have := (eK ⟨v, h⟩).isLt; omega⟩ else 0
  have hsz_idx : ∀ v ∈ Kept, sz (idxv v) = v := by
    intro v hv
    simp only [idxv, dif_pos hv, sz]
    rw [dif_pos ⟨by omega, by have := (eK ⟨v, hv⟩).isLt; omega⟩]
    simp
  have hsz0 : ∀ j, 0 ≤ sz j := by
    intro j
    simp only [sz]
    split_ifs with h
    · exact (hKpos _ (eK.symm ⟨j.val - 1, h.2⟩).2).le
    · exact le_refl _
  -- rounding a large weight down to a kept size
  let rd : ι → ℝ := fun e =>
    if h : (Kept.filter (· ≤ w e)).Nonempty then (Kept.filter (· ≤ w e)).max' h else 0
  have hrd : ∀ e, lg e → rd e ∈ Kept ∧ rd e ≤ w e ∧
      ∀ τ, (τ ≤ rd e ↔ ∃ k ∈ Kept, τ ≤ k ∧ k ≤ w e) := by
    intro e he
    have hne : (Kept.filter (· ≤ w e)).Nonempty := by
      obtain ⟨k, hk, hkw⟩ := hKbelow ⟨e, he⟩
      exact ⟨k, Finset.mem_filter.mpr ⟨hk, hkw⟩⟩
    have hmem := Finset.mem_filter.mp (Finset.max'_mem _ hne)
    simp only [rd, dif_pos hne]
    refine ⟨hmem.1, hmem.2, fun τ => ⟨fun h => ⟨_, hmem.1, h, hmem.2⟩, ?_⟩⟩
    rintro ⟨k, hk, hτk, hkw⟩
    exact le_trans hτk (Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hk, hkw⟩))
  -- reindexing slots of a set by its large items
  have hcast : ∀ (n : ℕ), n ≤ K → ∀ G : Fin n → ℝ,
      ∑ i : Fin K, (if h : i.val < n then G ⟨i.val, h⟩ else 0) = ∑ j, G j := by
    intro n hn G
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map (Fin.castLEEmb hn)))]
    · rw [Finset.sum_map]
      apply Finset.sum_congr rfl; intro j _
      simp
    · intro i _ hi
      rw [dif_neg]
      intro h
      apply hi
      exact Finset.mem_map.mpr ⟨⟨i.val, h⟩, Finset.mem_univ _, Fin.ext rfl⟩
  let SL : Finset ι → Finset ι := fun S => S.filter lg
  let slotItem : Finset ι → Fin K → Option ι := fun S i =>
    if h : i.val < (SL S).card then some ((SL S).equivFin.symm ⟨i.val, h⟩).1 else none
  have hslot_sum : ∀ S : Finset ι, p S ≠ 0 → ∀ Φ : Option ι → ℝ, Φ none = 0 →
      ∑ i, Φ (slotItem S i) = ∑ e ∈ SL S, Φ (some e) := by
    intro S hS Φ hΦ
    have h1 : ∀ i : Fin K, Φ (slotItem S i) = if h : i.val < (SL S).card then
        Φ (some ((SL S).equivFin.symm ⟨i.val, h⟩).1) else 0 := by
      intro i; simp only [slotItem]; split_ifs <;> simp [hΦ]
    simp_rw [h1]
    rw [hcast _ (hcardL S hS) (fun j => Φ (some ((SL S).equivFin.symm j).1))]
    rw [Equiv.sum_comp (SL S).equivFin.symm (fun e => Φ (some e.1))]
    exact Finset.sum_coe_sort (SL S) (fun e => Φ (some e))
  let RS : Finset ι → ℝ := fun S => 1 - ∑ e ∈ SL S, w e
  let typ : Finset ι → TS := fun S =>
    (fun i => (slotItem S i).elim 0 (fun e => idxv (rd e)),
      ⟨min ⌊max 0 (RS S) / q⌋₊ J, by omega⟩)
  -- profiles of the labels
  let valid : TS → Prop := fun T => ∑ i, sz (T.1 i) + ((T.2 : ℕ) : ℝ) * q ≤ 1
  let bL : Lbl → Fin K → ℝ := Sum.elim (fun T i => if valid T then sz (T.1 i) else 0)
    (fun j i => if j.val = 0 ∧ i.val = 0 then 1 else 0)
  let RL : Lbl → ℝ := Sum.elim (fun T => if valid T then ((T.2 : ℕ) : ℝ) * q else 0)
    (fun j => if j.val = 1 then 1 else 0)
  let lamL : Lbl → ℝ := Sum.elim (fun T => s * ∑ S ∈ Finset.univ.filter (fun S => typ S = T), p S)
    (fun j => if j.val = 0 then s * q else if j.val = 1 then s * q else 1 - s * (1 + 2 * q))
  have hsz00 : sz 0 = 0 := by simp [sz]
  -- the profile of a feasible set
  have hsz_slot : ∀ S : Finset ι, ∀ i : Fin K,
      sz ((typ S).1 i) = (slotItem S i).elim 0 (fun e => rd e) := by
    intro S i
    simp only [typ]
    cases h : slotItem S i with
    | none => simp [hsz00]
    | some e =>
      simp only [Option.elim]
      have he : e ∈ SL S := by
        simp only [slotItem] at h
        split_ifs at h with h'
        · simp only [Option.some.injEq] at h; rw [← h]; exact Finset.coe_mem _
      exact hsz_idx _ (hrd e (Finset.mem_filter.mp he).2).1
  have hRS : ∀ S : Finset ι, p S ≠ 0 → ∑ e ∈ S.filter (fun e => ¬ lg e), w e ≤ RS S := by
    intro S hS
    have h1 := hpf S hS
    have h2 := Finset.sum_filter_add_sum_filter_not S lg w
    simp only [RS, SL]
    linarith
  have hvalid : ∀ S : Finset ι, p S ≠ 0 → valid (typ S) := by
    intro S hS
    simp only [valid]
    have h1 : ∑ i, sz ((typ S).1 i) = ∑ e ∈ SL S, rd e := by
      simp_rw [hsz_slot S]
      exact hslot_sum S hS (fun o => o.elim 0 (fun e => rd e)) rfl
    have h2 : ∑ e ∈ SL S, rd e ≤ ∑ e ∈ SL S, w e :=
      Finset.sum_le_sum (fun e he => (hrd e (Finset.mem_filter.mp he).2).2.1)
    have hR0 : 0 ≤ RS S := le_trans (Finset.sum_nonneg (fun e _ => (hw0 e).le)) (hRS S hS)
    have h3 : (((typ S).2 : ℕ) : ℝ) * q ≤ RS S := by
      simp only [typ]
      have h4 : ((min ⌊max 0 (RS S) / q⌋₊ J : ℕ) : ℝ) ≤ ⌊max 0 (RS S) / q⌋₊ := by
        exact_mod_cast min_le_left _ _
      have h5 : (⌊max 0 (RS S) / q⌋₊ : ℝ) ≤ max 0 (RS S) / q := Nat.floor_le (by positivity)
      rw [max_eq_right hR0] at h4 h5 ⊢
      have := mul_le_mul_of_nonneg_right (le_trans h4 h5) hq0.le
      rwa [div_mul_cancel₀ _ hq0.ne'] at this
    rw [h1]
    simp only [RS] at h3
    linarith
  -- probabilities
  have hsq : s * (1 + 2 * q) ≤ 1 := by
    rw [hs, hq]; nlinarith only [hδ0, hδ1]
  have hlamL0 : ∀ P, 0 ≤ lamL P := by
    intro P
    rcases P with T | j
    · exact mul_nonneg hs0.le (Finset.sum_nonneg (fun S _ => hp0 S))
    · simp only [lamL, Sum.elim_inr]
      split_ifs
      · positivity
      · positivity
      · linarith
  have hlamL1 : ∑ P, lamL P = 1 := by
    rw [Fintype.sum_sum_type]
    simp only [lamL, Sum.elim_inl, Sum.elim_inr]
    rw [← Finset.mul_sum, Finset.sum_fiberwise Finset.univ typ p, hp1, Fin.sum_univ_three]
    simp
    ring
  -- Hall's condition for the large items
  let d : ι → ℝ := fun e => if lg e then s * x e else 0
  have hd0 : ∀ e, 0 ≤ d e := fun e => by
    simp only [d]; split_ifs
    · exact mul_nonneg hs0.le (hx0 e)
    · exact le_refl _
  have hall : ∀ e₀, ∑ e ∈ Finset.univ.filter (fun e => w e₀ ≤ w e), d e ≤
      ∑ sl ∈ Finset.univ.filter (fun sl : Lbl × Fin K => w e₀ ≤ bL sl.1 sl.2), lamL sl.1 := by
    intro e₀
    set τ := w e₀
    have hτ0 : 0 < τ := hw0 e₀
    have hτ1 : τ ≤ 1 := hw1 e₀
    obtain ⟨cnt, hcnt⟩ : ∃ f : Lbl → ℝ, ∀ P, f P = ∑ i, if τ ≤ bL P i then (1 : ℝ) else 0 :=
      ⟨_, fun _ => rfl⟩
    have hR1 : ∑ sl ∈ Finset.univ.filter (fun sl : Lbl × Fin K => τ ≤ bL sl.1 sl.2), lamL sl.1
        = ∑ P, lamL P * cnt P := by
      rw [Finset.sum_filter, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl; intro P _
      rw [hcnt, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      split_ifs <;> simp
    have hcnt0 : ∀ P, 0 ≤ cnt P := fun P => (hcnt P).symm ▸
      Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)
    have hcnt_full : 1 ≤ cnt (Sum.inr 0) := by
      have : (if τ ≤ bL (Sum.inr 0) ⟨0, hK1⟩ then (1 : ℝ) else 0) = 1 := by
        simp [bL, hτ1]
      calc (1 : ℝ) = (if τ ≤ bL (Sum.inr 0) ⟨0, hK1⟩ then (1 : ℝ) else 0) := this.symm
        _ ≤ cnt (Sum.inr 0) := (hcnt _).symm ▸ Finset.single_le_sum
            (f := fun i => if τ ≤ bL (Sum.inr 0) i then (1 : ℝ) else 0)
            (fun i _ => by split_ifs <;> norm_num) (Finset.mem_univ _)
    have hcntS : ∀ S, p S ≠ 0 →
        cnt (Sum.inl (typ S)) = ∑ e ∈ S, if lg e ∧ τ ≤ rd e then (1 : ℝ) else 0 := by
      intro S hS
      rw [hcnt]
      simp only [bL, Sum.elim_inl, if_pos (hvalid S hS), hsz_slot S]
      rw [hslot_sum S hS (fun o => if τ ≤ o.elim 0 (fun e => rd e) then (1 : ℝ) else 0)
        (by simp [not_le.mpr hτ0])]
      simp only [Option.elim, SL]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl; intro e _
      by_cases h : β ≤ w e
      · by_cases h2 : τ ≤ rd e <;> simp [lg, h, h2]
      · simp [lg, h]
    have hRHS : s * ∑ e, (if lg e ∧ τ ≤ rd e then (1 : ℝ) else 0) * x e + s * q
        ≤ ∑ P, lamL P * cnt P := by
      rw [Fintype.sum_sum_type, Fin.sum_univ_three]
      simp only [lamL, Sum.elim_inl, Sum.elim_inr]
      have h1 : ∑ T : TS, s * (∑ S ∈ Finset.univ.filter (fun S => typ S = T), p S) * cnt (Sum.inl T)
          = s * ∑ S, p S * cnt (Sum.inl (typ S)) := by
        rw [Finset.mul_sum, ← Finset.sum_fiberwise Finset.univ typ]
        apply Finset.sum_congr rfl; intro T _
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro S hS
        rw [(Finset.mem_filter.mp hS).2]; ring
      rw [h1, hswap]
      have h2 : ∑ S, p S * ∑ e ∈ S, (if lg e ∧ τ ≤ rd e then (1 : ℝ) else 0)
          = ∑ S, p S * cnt (Sum.inl (typ S)) := by
        apply Finset.sum_congr rfl; intro S _
        rcases eq_or_ne (p S) 0 with h | h
        · rw [h]; simp
        · rw [hcntS S h]
      rw [h2]
      have h3 : s * q ≤ s * q * cnt (Sum.inr 0) := le_mul_of_one_le_right (by positivity) hcnt_full
      have h4 : 0 ≤ (if (1 : Fin 3).val = 0 then s * q else if (1 : Fin 3).val = 1 then s * q
          else 1 - s * (1 + 2 * q)) * cnt (Sum.inr 1) :=
        mul_nonneg (hlamL0 (Sum.inr 1)) (hcnt0 _)
      have h5 : 0 ≤ (if (2 : Fin 3).val = 0 then s * q else if (2 : Fin 3).val = 1 then s * q
          else 1 - s * (1 + 2 * q)) * cnt (Sum.inr 2) :=
        mul_nonneg (hlamL0 (Sum.inr 2)) (hcnt0 _)
      simp only [Fin.val_zero, if_true] at h3 ⊢
      linarith
    -- the left side
    have hLHS : ∑ e ∈ Finset.univ.filter (fun e => τ ≤ w e), d e
        ≤ s * ∑ e, (if lg e ∧ τ ≤ rd e then (1 : ℝ) else 0) * x e + s * q := by
      have hlost : ∑ e ∈ Finset.univ.filter (fun e => lg e ∧ τ ≤ w e ∧ ¬ τ ≤ rd e), x e ≤ q := by
        have h0 := hKlost τ
        rw [Finset.sum_filter] at h0
        rw [← Finset.sum_subtype (p := lg) (Finset.univ.filter lg) (by simp)
          (fun e => if τ ≤ w e ∧ ∀ k ∈ Kept, k ≤ w e → k < τ then x e else 0)] at h0
        refine le_trans (le_of_eq ?_) h0
        rw [Finset.sum_filter, Finset.sum_filter]
        apply Finset.sum_congr rfl; intro e _
        by_cases hl : β ≤ w e
        · have h' := (hrd e hl).2.2 τ
          have : (τ ≤ w e ∧ ¬ τ ≤ rd e) ↔ (τ ≤ w e ∧ ∀ k ∈ Kept, k ≤ w e → k < τ) := by
            rw [h']
            constructor
            · rintro ⟨h1, h2⟩
              refine ⟨h1, fun k hk h3 => ?_⟩
              by_contra h4
              push Not at h4
              exact h2 ⟨k, hk, h4, h3⟩
            · rintro ⟨h1, h2⟩
              refine ⟨h1, ?_⟩
              rintro ⟨k, hk, h3, h4⟩
              exact absurd (h2 k hk h4) (not_lt.mpr h3)
          simp only [lg, hl, true_and, if_true]
          exact if_congr this rfl rfl
        · simp [lg, hl]
      have hsplit : ∑ e ∈ Finset.univ.filter (fun e => τ ≤ w e), d e
          = s * (∑ e, (if lg e ∧ τ ≤ w e ∧ τ ≤ rd e then (1 : ℝ) else 0) * x e
            + ∑ e ∈ Finset.univ.filter (fun e => lg e ∧ τ ≤ w e ∧ ¬ τ ≤ rd e), x e) := by
        rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro e _
        simp only [d]
        by_cases hl : lg e <;> by_cases h1 : τ ≤ w e <;> by_cases h2 : τ ≤ rd e <;> simp [hl, h1, h2]
      have hmono : ∑ e, (if lg e ∧ τ ≤ w e ∧ τ ≤ rd e then (1 : ℝ) else 0) * x e
          ≤ ∑ e, (if lg e ∧ τ ≤ rd e then (1 : ℝ) else 0) * x e := by
        apply Finset.sum_le_sum; intro e _
        apply mul_le_mul_of_nonneg_right _ (hx0 e)
        split_ifs with h1 h2 <;> first | exact absurd ⟨h1.1, h1.2.2⟩ h2 | norm_num
      rw [hsplit]
      nlinarith only [hlost, hmono, hs0]
    rw [hR1] at *
    linarith [hRHS, hLHS]
  obtain ⟨aT, haT0, haTsum, haTcap, haTcomp⟩ := transport d w (fun sl : Lbl × Fin K => lamL sl.1)
    (fun sl => bL sl.1 sl.2) hd0 (fun sl => hlamL0 sl.1) hall
  -- small items
  have hRL0 : ∀ P, 0 ≤ RL P := by
    intro P; rcases P with T | j
    · simp only [RL, Sum.elim_inl]; split_ifs
      · positivity
      · exact le_refl _
    · simp only [RL, Sum.elim_inr]; split_ifs <;> norm_num
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = ∑ P, lamL P * RL P := ⟨_, rfl⟩
  have hQsmall : s * ∑ e, (if lg e then (0 : ℝ) else w e) * x e ≤ Q := by
    rw [hQ, Fintype.sum_sum_type, Fin.sum_univ_three]
    simp only [lamL, RL, Sum.elim_inl, Sum.elim_inr]
    have h1 : ∑ T : TS, s * (∑ S ∈ Finset.univ.filter (fun S => typ S = T), p S) *
        (if valid T then ((T.2 : ℕ) : ℝ) * q else 0)
        = s * ∑ S, p S * (if valid (typ S) then (((typ S).2 : ℕ) : ℝ) * q else 0) := by
      rw [Finset.mul_sum, ← Finset.sum_fiberwise Finset.univ typ]
      apply Finset.sum_congr rfl; intro T _
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro S hS
      rw [(Finset.mem_filter.mp hS).2]; ring
    rw [h1]
    have h2 : ∀ S, p S * (RS S - q) ≤ p S * (if valid (typ S) then (((typ S).2 : ℕ) : ℝ) * q else 0) := by
      intro S
      rcases eq_or_ne (p S) 0 with h | h
      · rw [h]; simp
      apply mul_le_mul_of_nonneg_left _ (hp0 S)
      rw [if_pos (hvalid S h)]
      simp only [typ]
      have hR0 : 0 ≤ RS S := le_trans (Finset.sum_nonneg (fun e _ => (hw0 e).le)) (hRS S h)
      have hR1 : RS S ≤ 1 := by
        simp only [RS]; linarith [Finset.sum_nonneg (fun e (_ : e ∈ SL S) => (hw0 e).le)]
      rw [max_eq_right hR0]
      have hfl : ⌊RS S / q⌋₊ ≤ J := by
        rw [hJ]; exact Nat.floor_le_floor (div_le_div_of_nonneg_right hR1 hq0.le)
      rw [min_eq_left hfl]
      have := Nat.lt_floor_add_one (RS S / q)
      rw [div_lt_iff₀ hq0] at this
      linarith
    have h3 : ∑ e, (if lg e then (0 : ℝ) else w e) * x e ≤ ∑ S, p S * RS S := by
      rw [hswap]
      apply Finset.sum_le_sum; intro S _
      rcases eq_or_ne (p S) 0 with h | h
      · rw [h]; simp
      apply mul_le_mul_of_nonneg_left _ (hp0 S)
      refine le_trans (le_of_eq ?_) (hRS S h)
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl; intro e _
      by_cases hl : lg e <;> simp [hl]
    have h4 : ∑ S, p S * (RS S - q) = ∑ S, p S * RS S - q := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul]
    have h5 := Finset.sum_le_sum (fun S (_ : S ∈ Finset.univ) => h2 S)
    have h6 : ∑ e, (if lg e then (0 : ℝ) else w e) * x e
        ≤ ∑ S, p S * (if valid (typ S) then (((typ S).2 : ℕ) : ℝ) * q else 0) + q := by linarith
    have h7 := mul_le_mul_of_nonneg_left h6 hs0.le
    have h8 : (if (1 : Fin 3).val = 0 then s * q else if (1 : Fin 3).val = 1 then s * q
        else 1 - s * (1 + 2 * q)) * (if (1 : Fin 3).val = 1 then (1 : ℝ) else 0) = s * q := by
      simp
    have h9 : (if (0 : Fin 3).val = 0 then s * q else if (0 : Fin 3).val = 1 then s * q
        else 1 - s * (1 + 2 * q)) * (if (0 : Fin 3).val = 1 then (1 : ℝ) else 0) = 0 := by
      simp
    have h10 : (if (2 : Fin 3).val = 0 then s * q else if (2 : Fin 3).val = 1 then s * q
        else 1 - s * (1 + 2 * q)) * (if (2 : Fin 3).val = 1 then (1 : ℝ) else 0) = 0 := by
      simp
    rw [h8, h9, h10]
    linarith
  let aS' : ι → Lbl → ℝ := fun e P => if lg e then 0 else s * x e * (lamL P * RL P) / Q
  have hQ0 : 0 ≤ Q := by rw [hQ]; exact Finset.sum_nonneg (fun P _ => mul_nonneg (hlamL0 P) (hRL0 P))
  have haS'sum : ∀ e, ¬ lg e → ∑ P, aS' e P = s * x e := by
    intro e he
    simp only [aS', he, if_false]
    rcases hQ0.lt_or_eq with hQp | hQz
    · rw [← Finset.sum_div, ← Finset.mul_sum, ← hQ]; field_simp
    · -- no small mass at all
      have hz : s * ∑ e, (if lg e then (0 : ℝ) else w e) * x e ≤ 0 :=
        le_of_le_of_eq hQsmall hQz.symm
      have hterm : (if lg e then (0 : ℝ) else w e) * x e ≤ ∑ e, (if lg e then (0 : ℝ) else w e) * x e :=
        Finset.single_le_sum (f := fun e => (if lg e then (0 : ℝ) else w e) * x e)
          (fun e _ => mul_nonneg (by split_ifs <;> [exact le_refl _; exact (hw0 e).le]) (hx0 e))
          (Finset.mem_univ e)
      simp only [he, if_false] at hterm
      have : w e * x e ≤ 0 := by nlinarith only [hz, hterm, hs0]
      have hxe : x e = 0 := le_antisymm (by
        by_contra h; push Not at h; nlinarith only [this, h, hw0 e]) (hx0 e)
      simp [hxe]
  -- profile validity on labels
  have hprof : ∀ P : Lbl, (∀ i, 0 ≤ bL P i) ∧ 0 ≤ RL P ∧ ∑ i, bL P i + RL P ≤ 1 := by
    intro P
    rcases P with T | j
    · simp only [bL, RL, Sum.elim_inl]
      by_cases hv : valid T
      · simp only [hv, if_true]
        exact ⟨fun i => hsz0 _, by positivity, hv⟩
      · simp [hv]
    · fin_cases j
      · simp only [bL, RL, Sum.elim_inr]
        refine ⟨fun i => by split_ifs <;> norm_num, by norm_num, ?_⟩
        have : ∑ i : Fin K, (if ((0 : Fin 3) : ℕ) = 0 ∧ (i : ℕ) = 0 then (1 : ℝ) else 0) = 1 := by
          rw [Finset.sum_eq_single ⟨0, hK1⟩]
          · simp
          · intro i _ hi; rw [if_neg]; intro h; exact hi (Fin.ext h.2)
          · simp
        first | (rw [this]; norm_num) | (norm_num at this ⊢; linarith)
      · simp [bL, RL]
      · simp [bL, RL]
  have hRLq : ∀ P : Lbl, RL P = 0 ∨ δ / 4 ≤ RL P := by
    intro P
    rcases P with T | j
    · simp only [RL, Sum.elim_inl]
      split_ifs
      · rcases Nat.eq_zero_or_pos (T.2 : ℕ) with h | h
        · left; rw [h]; simp
        · right
          have : (1 : ℝ) ≤ ((T.2 : ℕ) : ℝ) := by exact_mod_cast h
          rw [← hq]; nlinarith only [this, hq0]
      · left; rfl
    · simp only [RL, Sum.elim_inr]
      split_ifs
      · right; linarith
      · left; rfl
  have haT_small : ∀ e, ¬ lg e → ∀ sl, aT e sl = 0 := by
    intro e he sl
    have h1 := haTsum e
    simp only [d, he, if_false] at h1
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun sl _ => haT0 e sl)).mp h1 sl (Finset.mem_univ _)
  have haT_le : ∀ e sl, aT e sl ≤ d e := by
    intro e sl
    rw [← haTsum e]
    exact Finset.single_le_sum (f := aT e) (fun sl _ => haT0 e sl) (Finset.mem_univ sl)
  have hd_le : ∀ e, d e ≤ s * x e := by
    intro e; simp only [d]; split_ifs
    · exact le_refl _
    · exact mul_nonneg hs0.le (hx0 e)
  have haS'0 : ∀ e P, 0 ≤ aS' e P := by
    intro e P; simp only [aS']; split_ifs
    · exact le_refl _
    · exact div_nonneg (mul_nonneg (mul_nonneg hs0.le (hx0 e)) (mul_nonneg (hlamL0 P) (hRL0 P))) hQ0
  have haS'large : ∀ e, lg e → ∀ P, aS' e P = 0 := fun e he P => by simp [aS', he]
  subst hK
  set φ : Fin (Fintype.card Lbl) ≃ Lbl := (Fintype.equivFin Lbl).symm
  refine ⟨fun P => lamL (φ P), fun P i => bL (φ P) i, fun P => RL (φ P),
    fun e P i => aT e (φ P, i), fun e P => aS' e (φ P),
    fun P => hprof (φ P), fun P => hlamL0 (φ P), ?_, fun e P i => haT0 e _,
    fun e P => haS'0 e _, ?_, fun P i => haTcap (φ P, i), ?_, ?_, ?_, fun P => hRLq (φ P), ?_, ?_⟩
  · rw [Equiv.sum_comp φ lamL]; exact hlamL1
  · intro e
    rw [Finset.sum_add_distrib, Equiv.sum_comp φ (fun P => ∑ i, aT e (P, i)),
      Equiv.sum_comp φ (fun P => aS' e P)]
    have h1 : ∑ P : Lbl, ∑ i, aT e (P, i) = d e := by
      rw [← haTsum e, Fintype.sum_prod_type]
    rw [h1, ← hs]
    by_cases he : lg e
    · simp [d, he, haS'large e he]
    · rw [haS'sum e he]; simp [d, he]
  · intro P
    rcases hQ0.lt_or_eq with hQp | hQz
    · have h1 : ∑ e ∈ Finset.univ.filter (fun e => w e < β), w e * aS' e (φ P)
          = (lamL (φ P) * RL (φ P) / Q) * (s * ∑ e, (if lg e then (0 : ℝ) else w e) * x e) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_filter]
        apply Finset.sum_congr rfl; intro e _
        by_cases he : β ≤ w e
        · have : ¬ w e < β := not_lt.mpr he
          simp only [this, if_false, lg, he, if_true, zero_mul, mul_zero]
        · have : w e < β := not_le.mp he
          simp only [this, if_true, aS', lg, he, if_false]
          field_simp
      rw [h1]
      have h2 : 0 ≤ lamL (φ P) * RL (φ P) := mul_nonneg (hlamL0 _) (hRL0 _)
      calc lamL (φ P) * RL (φ P) / Q * (s * ∑ e, (if lg e then (0 : ℝ) else w e) * x e)
          ≤ lamL (φ P) * RL (φ P) / Q * Q := mul_le_mul_of_nonneg_left hQsmall (by positivity)
        _ = lamL (φ P) * RL (φ P) := by field_simp
    · have : ∀ e, aS' e (φ P) = 0 := fun e => by simp [aS', ← hQz]
      simp only [this, mul_zero, Finset.sum_const_zero]
      exact mul_nonneg (hlamL0 _) (hRL0 _)
  · intro e P i h
    by_cases he : lg e
    · exact ⟨he, haTcomp e (φ P, i) h⟩
    · exact absurd (haT_small e he _) h
  · intro e P h
    have he : ¬ lg e := fun he => h (haS'large e he _)
    refine ⟨not_le.mp he, ?_⟩
    rcases (hRL0 (φ P)).lt_or_eq with hR | hR
    · exact hR
    · exfalso; apply h; simp [aS', he, ← hR]
  · intro e P i
    rw [← hs]; exact le_trans (haT_le e _) (hd_le e)
  · intro e P
    show aS' e (φ P) ≤ (1 - δ) * x e
    rw [← hs]
    by_cases he : lg e
    · rw [haS'large e he]; exact mul_nonneg hs0.le (hx0 e)
    · rw [← haS'sum e he]
      exact Finset.single_le_sum (f := aS' e) (fun P _ => haS'0 e P) (Finset.mem_univ _)
