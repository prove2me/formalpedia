-- Prove2me | solution 1 for TradingPostNSW.Leontief.theorem_4_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T17:08:33.357765+00:00
-- url     : https://prove2.me/submissions/7c91e68b-8f3a-4636-b27f-93d239fab5db

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Theorems.Thm_TradingPostNSW_Leontief_pne_bid_zero_or_ge_fee
import Theorems.Thm_TradingPostNSW_Leontief_pne_spend_off_tight_le

namespace TPgameAux
open TradingPostNSW.Leontief

variable {n m : ℕ}

lemma mem_D (I : Instance n m) (i : Fin n) (j : Fin m) : j ∈ D I i ↔ 0 < I.v i j := by
  simp [D]

lemma u_eq (I : Instance n m) (hI : Standing I) (i : Fin n) (y : Fin m → ℝ) :
    u I i y = (D I i).inf' (hI.D_nonempty i) (fun j => y j / I.v i j) := by
  simp [u, hI.D_nonempty i]

lemma u_le (I : Instance n m) (hI : Standing I) (i : Fin n) (y : Fin m → ℝ) (j : Fin m)
    (hj : j ∈ D I i) : u I i y ≤ y j / I.v i j := by
  rw [u_eq I hI]; exact Finset.inf'_le _ hj

lemma lt_u (I : Instance n m) (hI : Standing I) (i : Fin n) (y : Fin m → ℝ) (t : ℝ)
    (h : ∀ j ∈ D I i, t < y j / I.v i j) : t < u I i y := by
  rw [u_eq I hI]; exact (Finset.lt_inf'_iff _).2 h

lemma u_nonneg (I : Instance n m) (hI : Standing I) (i : Fin n) (y : Fin m → ℝ)
    (hy : ∀ j, 0 ≤ y j) : 0 ≤ u I i y := by
  rw [u_eq I hI]; exact (Finset.le_inf'_iff _ _).2 (fun j _ => div_nonneg (hy j) (hI.v_nonneg i j))

lemma u_mul_le (I : Instance n m) (hI : Standing I) (i : Fin n) (y : Fin m → ℝ)
    (hy : ∀ j, 0 ≤ y j) (j : Fin m) : u I i y * I.v i j ≤ y j := by
  by_cases hj : j ∈ D I i
  · have hv := (mem_D I i j).1 hj
    have := u_le I hI i y j hj
    rwa [le_div_iff₀ hv] at this
  · have hv : I.v i j = 0 := by
      have := hI.v_nonneg i j
      rw [mem_D] at hj; linarith
    rw [hv, mul_zero]; exact hy j

lemma u_mul_phi_le (I : Instance n m) (hI : Standing I) (i : Fin n) (p : Fin m → ℝ)
    (hp : ∀ j, 0 ≤ p j) (y : Fin m → ℝ) (hy : ∀ j, 0 ≤ y j) :
    u I i y * phi I i p ≤ ∑ j, p j * y j := by
  unfold phi
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have := u_mul_le I hI i y hy j
  nlinarith [hp j]

/-- effective bid of a single number. -/
noncomputable def eb (Δ β : ℝ) : ℝ := if Δ ≤ β then β else 0

/-- allocation of a bid `β` against effective opposing bids `O`. -/
noncomputable def g (Δ β O : ℝ) : ℝ := if 0 < eb Δ β then eb Δ β / (eb Δ β + O) else 0

/-- effective bids of the others. -/
noncomputable def oth (Δ : ℝ) (b : Fin n → Fin m → ℝ) (i : Fin n) (j : Fin m) : ℝ :=
  ∑ k ∈ Finset.univ.erase i, effBid Δ b k j

lemma tp_update (Δ : ℝ) (b : Fin n → Fin m → ℝ) (i : Fin n) (β : Fin m → ℝ) (j : Fin m) :
    tpAlloc Δ (Function.update b i β) i j = g Δ (β j) (oth Δ b i j) := by
  have hsum : ∑ k, effBid Δ (Function.update b i β) k j = eb Δ (β j) + oth Δ b i j := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    congr 1
    · simp [effBid, eb]
    · unfold oth
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hki : k ≠ i := Finset.ne_of_mem_erase hk
      simp [effBid, Function.update_of_ne hki]
  have he : effBid Δ (Function.update b i β) i j = eb Δ (β j) := by simp [effBid, eb]
  unfold tpAlloc g
  rw [he, hsum]

lemma tp_self (Δ : ℝ) (b : Fin n → Fin m → ℝ) (i : Fin n) (j : Fin m) :
    tpAlloc Δ b i j = g Δ (b i j) (oth Δ b i j) := by
  have := tp_update Δ b i (b i) j
  rwa [Function.update_eq_self] at this

lemma g_eq (Δ β O : ℝ) (hΔ : 0 < Δ) (hβ : Δ ≤ β) : g Δ β O = β / (β + O) := by
  have : eb Δ β = β := by simp [eb, hβ]
  unfold g; rw [this, if_pos (by linarith)]

lemma g_zero (Δ β O : ℝ) (hβ : β < Δ) : g Δ β O = 0 := by
  have : eb Δ β = 0 := by simp [eb, not_le.2 hβ]
  unfold g; rw [this]; simp

lemma g_pos (Δ β O : ℝ) (hΔ : 0 < Δ) (hβ : Δ ≤ β) (hO : 0 ≤ O) : 0 < g Δ β O := by
  rw [g_eq Δ β O hΔ hβ]; apply div_pos <;> linarith

lemma g_strict (Δ β β' O : ℝ) (hΔ : 0 < Δ) (hβ : Δ ≤ β) (hββ : β < β') (hO : 0 < O) :
    g Δ β O < g Δ β' O := by
  rw [g_eq Δ β O hΔ hβ, g_eq Δ β' O hΔ (by linarith)]
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

lemma effBid_nonneg (Δ : ℝ) (b : Fin n → Fin m → ℝ) (hb : ∀ k j, 0 ≤ b k j) (k : Fin n)
    (j : Fin m) : 0 ≤ effBid Δ b k j := by
  unfold effBid; split_ifs <;> simp [hb k j]

lemma oth_nonneg (Δ : ℝ) (b : Fin n → Fin m → ℝ) (hb : ∀ k j, 0 ≤ b k j) (i : Fin n)
    (j : Fin m) : 0 ≤ oth Δ b i j :=
  Finset.sum_nonneg (fun k _ => effBid_nonneg Δ b hb k j)

lemma tp_nonneg (Δ : ℝ) (b : Fin n → Fin m → ℝ) (hb : ∀ k j, 0 ≤ b k j) (i : Fin n)
    (j : Fin m) : 0 ≤ tpAlloc Δ b i j := by
  unfold tpAlloc
  split_ifs with h
  · exact div_nonneg h.le (Finset.sum_nonneg (fun k _ => effBid_nonneg Δ b hb k j))
  · exact le_refl 0

lemma strat_of (I : Instance n m) (i : Fin n) (bi : Fin m → ℝ) (h0 : ∀ j, 0 ≤ bi j)
    (hs : ∑ j, bi j = I.B i) : Strategy I i bi := by
  refine ⟨fun j => ⟨h0 j, ?_⟩, hs⟩
  rw [← hs]
  exact Finset.single_le_sum (fun k _ => h0 k) (Finset.mem_univ j)

section PNE

variable (I : Instance n m) (Δ : ℝ) (b : Fin n → Fin m → ℝ)

lemma bid_nonneg (hb : IsPNE I Δ b) : ∀ k j, 0 ≤ b k j := fun k j => ((hb.1 k).1 j).1

/-- Step A: utility is positive at a PNE. -/
lemma pne_u_pos (hI : Standing I) (hΔ : 0 < Δ) (hΔm : Δ < 1 / (m : ℝ)) (hb : IsPNE I Δ b)
    (i : Fin n) : 0 < u I i (tpAlloc Δ b i) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast hI.pos_m
  have hB1 := hI.one_le_B i
  set z : Fin m → ℝ := fun _ => I.B i / m
  have hz : Strategy I i z := by
    apply strat_of
    · intro j; exact div_nonneg (by linarith) hm.le
    · simp only [z, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
  have hΔz : Δ ≤ I.B i / m := by
    have : 1 / (m : ℝ) ≤ I.B i / m := div_le_div_of_nonneg_right hB1 hm.le
    linarith
  have hpos : 0 < u I i (tpAlloc Δ (Function.update b i z) i) := by
    apply lt_u I hI
    intro j hj
    rw [tp_update]
    exact div_pos (g_pos Δ _ _ hΔ hΔz (oth_nonneg Δ b (bid_nonneg I Δ b hb) i j))
      ((mem_D I i j).1 hj)
  exact lt_of_lt_of_le hpos (hb.2 i z hz)

/-- Step A': demanded bids are at least the fee. -/
lemma pne_ge_fee (hI : Standing I) (hΔ : 0 < Δ) (hΔm : Δ < 1 / (m : ℝ)) (hb : IsPNE I Δ b)
    (i : Fin n) (j : Fin m) (hj : j ∈ D I i) : Δ ≤ b i j := by
  by_contra h
  push_neg at h
  have h1 := u_le I hI i (tpAlloc Δ b i) j hj
  rw [tp_self, g_zero Δ _ _ h, zero_div] at h1
  have := pne_u_pos I Δ b hI hΔ hΔm hb i
  linarith

lemma oth_pos (hI : Standing I) (hPC : PerfectCompetition I) (hΔ : 0 < Δ)
    (hΔm : Δ < 1 / (m : ℝ)) (hb : IsPNE I Δ b) (i : Fin n) (j : Fin m) :
    0 < oth Δ b i j := by
  obtain ⟨i1, i2, hne, h1, h2⟩ := hPC j
  have key : ∃ l, l ≠ i ∧ 0 < I.v l j := by
    by_cases h : i1 = i
    · exact ⟨i2, fun h' => hne (h.trans h'.symm), h2⟩
    · exact ⟨i1, h, h1⟩
  obtain ⟨l, hl, hv⟩ := key
  have hge := pne_ge_fee I Δ b hI hΔ hΔm hb l j ((mem_D I l j).2 hv)
  have he : effBid Δ b l j = b l j := by simp [effBid, hge]
  have : effBid Δ b l j ≤ oth Δ b i j :=
    Finset.single_le_sum (f := fun k => effBid Δ b k j)
      (fun k _ => effBid_nonneg Δ b (bid_nonneg I Δ b hb) k j)
      (Finset.mem_erase.2 ⟨hl, Finset.mem_univ l⟩)
  linarith

/-- No strategy makes every demanded good strictly better than the current utility level. -/
lemma no_improve (hI : Standing I) (hb : IsPNE I Δ b) (i : Fin n) (b' : Fin m → ℝ)
    (hs : Strategy I i b')
    (h : ∀ j ∈ D I i, u I i (tpAlloc Δ b i) * I.v i j < tpAlloc Δ (Function.update b i b') i j) :
    False := by
  have : u I i (tpAlloc Δ b i) < u I i (tpAlloc Δ (Function.update b i b') i) := by
    apply lt_u I hI
    intro j hj
    rw [lt_div_iff₀ ((mem_D I i j).1 hj)]
    exact h j hj
  have := hb.2 i b' hs
  linarith

/-- Raising a demanded bid strictly raises the allocation above the utility level. -/
lemma raise_ok (hI : Standing I) (hPC : PerfectCompetition I) (hΔ : 0 < Δ)
    (hΔm : Δ < 1 / (m : ℝ)) (hb : IsPNE I Δ b) (i : Fin n) (b' : Fin m → ℝ) (j : Fin m)
    (hj : j ∈ D I i) (hr : b i j < b' j) :
    u I i (tpAlloc Δ b i) * I.v i j < tpAlloc Δ (Function.update b i b') i j := by
  have h1 := u_mul_le I hI i (tpAlloc Δ b i) (tp_nonneg Δ b (bid_nonneg I Δ b hb) i) j
  rw [tp_self] at h1
  rw [tp_update]
  exact lt_of_le_of_lt h1 (g_strict Δ _ _ _ hΔ (pne_ge_fee I Δ b hI hΔ hΔm hb i j hj) hr
    (oth_pos I Δ b hI hPC hΔ hΔm hb i j))

/-- Step D: no money on undemanded goods. -/
lemma pne_undemanded_zero (hI : Standing I) (hPC : PerfectCompetition I) (hΔ : 0 < Δ)
    (hΔm : Δ < 1 / (m : ℝ)) (hb : IsPNE I Δ b) (i : Fin n) (j : Fin m) (hj : j ∉ D I i) :
    b i j = 0 := by
  have h0 := bid_nonneg I Δ b hb i j
  by_contra hne
  have hpos : 0 < b i j := lt_of_le_of_ne h0 (Ne.symm hne)
  have hDc : (0 : ℝ) < ((D I i).card : ℝ) := by
    exact_mod_cast (hI.D_nonempty i).card_pos
  set c := b i j / ((D I i).card : ℝ)
  have hc : 0 < c := div_pos hpos hDc
  set b' : Fin m → ℝ := fun k =>
    b i k - (if k = j then b i j else 0) + (if k ∈ D I i then c else 0)
  have hs : Strategy I i b' := by
    apply strat_of
    · intro k
      simp only [b']
      by_cases hk : k = j
      · subst hk; simp [hj]
      · rw [if_neg hk]
        have := bid_nonneg I Δ b hb i k
        split_ifs <;> linarith
    · simp only [b']
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq']
      rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
      simp only [c, Finset.mem_univ, if_true]
      rw [mul_div_cancel₀ _ hDc.ne', (hb.1 i).2]
      ring
  apply no_improve I Δ b hI hb i b' hs
  intro k hk
  apply raise_ok I Δ b hI hPC hΔ hΔm hb i b' k hk
  have hkj : k ≠ j := fun h => hj (h ▸ hk)
  simp only [b', if_neg hkj, if_pos hk]
  linarith

/-- Milestone: every bid is `0` or at least `Δ`. -/
lemma pne_zero_or_ge (hI : Standing I) (hPC : PerfectCompetition I) (hΔ : 0 < Δ)
    (hΔm : Δ < 1 / (m : ℝ)) (hb : IsPNE I Δ b) (i : Fin n) (j : Fin m) :
    b i j = 0 ∨ Δ ≤ b i j := by
  by_cases hj : j ∈ D I i
  · exact Or.inr (pne_ge_fee I Δ b hI hΔ hΔm hb i j hj)
  · exact Or.inl (pne_undemanded_zero I Δ b hI hPC hΔ hΔm hb i j hj)

lemma tight_nonempty (hI : Standing I) (i : Fin n) : (tight I Δ b i).Nonempty := by
  obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_inf' (hI.D_nonempty i)
    (fun j => tpAlloc Δ b i j / I.v i j)
  refine ⟨j, Finset.mem_filter.2 ⟨hj, ?_⟩⟩
  unfold frac
  rw [u_eq I hI, he]

lemma lt_of_not_tight (hI : Standing I) (hb : IsPNE I Δ b) (i : Fin n) (j : Fin m)
    (hj : j ∈ D I i) (hnt : j ∉ tight I Δ b i) :
    u I i (tpAlloc Δ b i) * I.v i j < tpAlloc Δ b i j := by
  have hv := (mem_D I i j).1 hj
  have hle := u_le I hI i (tpAlloc Δ b i) j hj
  have hne : frac I Δ b i j ≠ u I i (tpAlloc Δ b i) := by
    intro h; exact hnt (Finset.mem_filter.2 ⟨hj, h⟩)
  have hlt : u I i (tpAlloc Δ b i) < tpAlloc Δ b i j / I.v i j :=
    lt_of_le_of_ne hle (fun h => hne (by unfold frac; exact h.symm))
  rwa [lt_div_iff₀ hv] at hlt

/-- Step C: bids on demanded, non-tight goods equal the fee. -/
lemma pne_eq_fee_off_tight (hI : Standing I) (hPC : PerfectCompetition I) (hΔ : 0 < Δ)
    (hΔm : Δ < 1 / (m : ℝ)) (hb : IsPNE I Δ b) (i : Fin n) (j : Fin m) (hj : j ∈ D I i)
    (hnt : j ∉ tight I Δ b i) : b i j = Δ := by
  have hge := pne_ge_fee I Δ b hI hΔ hΔm hb i j hj
  by_contra hne
  have hgt : Δ < b i j := lt_of_le_of_ne hge (Ne.symm hne)
  set T := tight I Δ b i
  have hT := tight_nonempty I Δ b hI i
  have hTc : (0 : ℝ) < (T.card : ℝ) := by exact_mod_cast hT.card_pos
  set U := u I i (tpAlloc Δ b i)
  set O := oth Δ b i j
  have hO : 0 < O := oth_pos I Δ b hI hPC hΔ hΔm hb i j
  have hcur := lt_of_not_tight I Δ b hI hb i j hj hnt
  rw [tp_self, g_eq Δ _ _ hΔ hge] at hcur
  -- choose δ
  have hcont : ContinuousAt (fun δ : ℝ => (b i j - δ) / (b i j - δ + O)) 0 := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simp; linarith
  have hev1 : ∀ᶠ δ in nhds (0 : ℝ), U * I.v i j < (b i j - δ) / (b i j - δ + O) := by
    apply hcont.eventually (p := fun t => U * I.v i j < t)
    simp only [sub_zero]
    exact lt_mem_nhds hcur
  have hev2 : ∀ᶠ δ in nhds (0 : ℝ), δ < b i j - Δ := gt_mem_nhds (by linarith)
  obtain ⟨δ, ⟨h1, h2⟩, hδ⟩ :=
    (((hev1.and hev2).filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)))).exists
  have hδ0 : 0 < δ := hδ
  set c := δ / (T.card : ℝ)
  have hc : 0 < c := div_pos hδ0 hTc
  have hjT : j ∉ T := hnt
  set b' : Fin m → ℝ := fun k =>
    b i k - (if k = j then δ else 0) + (if k ∈ T then c else 0)
  have hs : Strategy I i b' := by
    apply strat_of
    · intro k
      simp only [b']
      by_cases hk : k = j
      · subst hk; simp [hjT]; linarith
      · rw [if_neg hk]
        have := bid_nonneg I Δ b hb i k
        split_ifs <;> linarith
    · simp only [b']
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq']
      rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
      simp only [c, Finset.mem_univ, if_true]
      rw [mul_div_cancel₀ _ hTc.ne', (hb.1 i).2]
      ring
  apply no_improve I Δ b hI hb i b' hs
  intro k hk
  by_cases hkj : k = j
  · subst hkj
    rw [tp_update]
    have : b' k = b i k - δ := by simp [b', hjT]
    rw [this, g_eq Δ _ _ hΔ (by linarith)]
    exact h1
  · by_cases hkT : k ∈ T
    · apply raise_ok I Δ b hI hPC hΔ hΔm hb i b' k hk
      simp only [b', if_neg hkj, if_pos hkT]
      linarith
    · have hb'k : b' k = b i k := by simp [b', hkj, hkT]
      rw [tp_update, hb'k, ← tp_self]
      exact lt_of_not_tight I Δ b hI hb i k hk hkT

/-- Milestone: spending outside the tight set is at most `(m-1)Δ`. -/
lemma pne_spend_off (hI : Standing I) (hPC : PerfectCompetition I) (hΔ : 0 < Δ)
    (hΔm : Δ < 1 / (m : ℝ)) (hb : IsPNE I Δ b) (i : Fin n) :
    ∑ j ∈ Finset.univ \ tight I Δ b i, b i j ≤ ((m : ℝ) - 1) * Δ := by
  have hle : ∀ j ∈ Finset.univ \ tight I Δ b i, b i j ≤ Δ := by
    intro j hj
    have hnt : j ∉ tight I Δ b i := (Finset.mem_sdiff.1 hj).2
    by_cases hjD : j ∈ D I i
    · rw [pne_eq_fee_off_tight I Δ b hI hPC hΔ hΔm hb i j hjD hnt]
    · rw [pne_undemanded_zero I Δ b hI hPC hΔ hΔm hb i j hjD]; exact hΔ.le
  have h1 := Finset.sum_le_card_nsmul _ _ _ hle
  rw [nsmul_eq_mul] at h1
  have hT := (tight_nonempty I Δ b hI i).card_pos
  have hcard : (Finset.univ \ tight I Δ b i).card = m - (tight I Δ b i).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
  have hTle : (tight I Δ b i).card ≤ m := by
    have := Finset.card_le_univ (tight I Δ b i); simpa using this
  have hc : (((Finset.univ \ tight I Δ b i).card : ℕ) : ℝ) ≤ (m : ℝ) - 1 := by
    rw [hcard, Nat.cast_sub hTle]
    have : (1 : ℝ) ≤ ((tight I Δ b i).card : ℝ) := by exact_mod_cast hT
    linarith
  calc ∑ j ∈ Finset.univ \ tight I Δ b i, b i j
      ≤ ((Finset.univ \ tight I Δ b i).card : ℝ) * Δ := h1
    _ ≤ ((m : ℝ) - 1) * Δ := mul_le_mul_of_nonneg_right hc hΔ.le

end PNE

end TPgameAux

open TradingPostNSW.Leontief TPgameAux

theorem solution {n m : ℕ} (I : Instance n m) (ε Δ : ℝ) (b : Fin n → Fin m → ℝ)
    (hI : Standing I) (hPC : PerfectCompetition I) (hε : 0 < ε) (hΔ : 0 < Δ)
    (hΔε : Δ < ε / (m : ℝ) ^ 2) (hΔm : Δ < 1 / (m : ℝ)) (hb : IsPNE I Δ b) :
    IsEpsME I ε (bidPrice b) (tpAlloc Δ b) := by
  have hz := pne_bid_zero_or_ge_fee I Δ b hI hPC hΔ hΔm hb
  have hsp := pne_spend_off_tight_le I Δ b hI hPC hΔ hΔm hb
  have hb0 := bid_nonneg I Δ b hb
  have he : ∀ k j, effBid Δ b k j = b k j := by
    intro k j
    rcases hz k j with h | h
    · simp [effBid, h]
    · simp [effBid, h]
  have hp0 : ∀ j, 0 ≤ bidPrice b j := fun j => Finset.sum_nonneg (fun k _ => hb0 k j)
  have hx : ∀ i j, tpAlloc Δ b i j = b i j / bidPrice b j := by
    intro i j
    unfold tpAlloc
    simp only [he]
    split_ifs with h
    · rfl
    · have : b i j = 0 := le_antisymm (not_lt.1 h) (hb0 i j)
      rw [this, zero_div]
  have hpz : ∀ j, bidPrice b j = 0 → ∀ k, b k j = 0 := by
    intro j h k
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hb0 k j)).1 h k (Finset.mem_univ k)
  have hxp : ∀ i j, tpAlloc Δ b i j * bidPrice b j = b i j := by
    intro i j
    rw [hx]
    by_cases h : bidPrice b j = 0
    · rw [h, hpz j h i]; simp
    · exact div_mul_cancel₀ _ h
  have hsumx : ∀ j, ∑ i, tpAlloc Δ b i j = bidPrice b j / bidPrice b j := by
    intro j; simp only [hx]; rw [← Finset.sum_div]; rfl
  have hM : (1 : ℝ) ≤ m := by exact_mod_cast hI.pos_m
  refine ⟨hp0, fun i j => tp_nonneg Δ b hb0 i j, ?_, ?_, ?_, ?_⟩
  · intro j; rw [hsumx]; exact div_self_le_one _
  · intro j h; rw [hsumx]; exact div_self h.ne'
  · intro i; simp only [hxp]; exact (hb.1 i).2
  · intro i y hy0 hc
    set U := u I i (tpAlloc Δ b i)
    set T := tight I Δ b i
    have hU0 : 0 ≤ U := u_nonneg I hI i _ (tp_nonneg Δ b hb0 i)
    have hT : ∀ j ∈ T, b i j = U * (I.v i j * bidPrice b j) := by
      intro j hj
      rcases Finset.mem_filter.1 hj with ⟨hjD, hfr⟩
      have hv := (mem_D I i j).1 hjD
      unfold frac at hfr
      have : tpAlloc Δ b i j = U * I.v i j := by
        rw [div_eq_iff hv.ne'] at hfr; exact hfr
      rw [← hxp, this]; ring
    have hTD : T ⊆ Finset.univ := Finset.subset_univ _
    have hsplit : ∑ j ∈ Finset.univ \ T, b i j + ∑ j ∈ T, b i j = I.B i := by
      rw [Finset.sum_sdiff hTD]; exact (hb.1 i).2
    have hTsum : ∑ j ∈ T, b i j ≤ U * phi I i (bidPrice b) := by
      rw [Finset.sum_congr rfl hT, ← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ hU0
      unfold phi
      exact Finset.sum_le_sum_of_subset_of_nonneg hTD
        (fun j _ _ => mul_nonneg (hI.v_nonneg i j) (hp0 j))
    have hspi := hsp i
    have hB1 := hI.one_le_B i
    -- arithmetic on the fee
    have hM2 : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
    have hA : Δ * (m : ℝ) ^ 2 < ε := by rwa [lt_div_iff₀ hM2] at hΔε
    have hA' : Δ * (m : ℝ) < 1 := by rwa [lt_div_iff₀ (by linarith)] at hΔm
    have hkey : (1 + ε) * (((m : ℝ) - 1) * Δ) ≤ ε := by
      have h1 : ((m : ℝ) - 1) * (Δ * (m : ℝ) ^ 2) ≤ ((m : ℝ) - 1) * ε :=
        mul_le_mul_of_nonneg_left hA.le (by linarith)
      have h2 : ε * ((m : ℝ) - 1) * (m : ℝ) * (Δ * (m : ℝ)) ≤ ε * ((m : ℝ) - 1) * (m : ℝ) := by
        have : 0 ≤ ε * ((m : ℝ) - 1) * (m : ℝ) := by
          apply mul_nonneg (mul_nonneg hε.le (by linarith)) (by linarith)
        nlinarith
      have h3 : (m : ℝ) ^ 2 * ((1 + ε) * (((m : ℝ) - 1) * Δ)) ≤ (m : ℝ) ^ 2 * ε := by
        nlinarith
      exact le_of_mul_le_mul_left h3 hM2
    have hL : I.B i ≤ (1 + ε) * (I.B i - ((m : ℝ) - 1) * Δ) := by nlinarith
    have hLpos : 0 < I.B i - ((m : ℝ) - 1) * Δ := by nlinarith
    have hUφ : I.B i - ((m : ℝ) - 1) * Δ ≤ U * phi I i (bidPrice b) := by linarith
    have hφ : 0 < phi I i (bidPrice b) := by
      by_contra h
      push_neg at h
      have : U * phi I i (bidPrice b) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hU0 h
      linarith
    have hy := u_mul_phi_le I hI i (bidPrice b) hp0 y hy0
    have : u I i y * phi I i (bidPrice b) ≤ (U * (1 + ε)) * phi I i (bidPrice b) := by
      nlinarith
    exact le_of_mul_le_mul_right this hφ
