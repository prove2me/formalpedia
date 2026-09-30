-- Prove2me | solution 1 for SupplyChainTheory.nearest_neighbor_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T21:29:09.39071+00:00
-- url     : https://prove2.me/submissions/39b7435f-b386-4e95-8bee-e59fea6b4650

import Mathlib
import Definitions.Def_SupplyChainTheory_tsp

open Classical SupplyChainTheory

private lemma rot_eq {m : ℕ} (k : Fin (m + 1)) : finRotate (m + 1) k = k + 1 := finRotate_apply k

/-- `z*` is the length of some tour. -/
private lemma exists_opt_tour {n : ℕ} (c : Fin n → Fin n → ℝ) :
    ∃ τ : Equiv.Perm (Fin n), tourLength c τ = optTourLength c := by
  obtain ⟨τ, hτ⟩ := (Set.range_nonempty (tourLength c)).csInf_mem (Set.finite_range _)
  exact ⟨τ, hτ⟩

/-! ### Majorization: threshold counts control sums -/

/-- If at every threshold `x` at most as many `a`-values as `b`-values reach `x`, and the
`b`-values are nonnegative, then `∑ a ≤ ∑ b`. -/
private lemma sum_le_of_count_le {α β : Type*} (a : α → ℝ) (b : β → ℝ) :
    ∀ (s : Finset α) (t : Finset β), (∀ j ∈ t, 0 ≤ b j) →
      (∀ x : ℝ, (s.filter (fun i => x ≤ a i)).card ≤ (t.filter (fun j => x ≤ b j)).card) →
      ∑ i ∈ s, a i ≤ ∑ j ∈ t, b j := by
  classical
  intro s
  induction hs : s.card generalizing s with
  | zero =>
    intro t hb _
    rw [Finset.card_eq_zero.mp hs, Finset.sum_empty]
    exact Finset.sum_nonneg hb
  | succ N ih =>
    intro t hb hcount
    have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
    -- The largest `a`-value is matched with the largest `b`-value.
    obtain ⟨i₀, hi₀, hmax⟩ := s.exists_max_image a hsne
    have hpos : 0 < (t.filter (fun j => a i₀ ≤ b j)).card :=
      lt_of_lt_of_le (Finset.card_pos.mpr ⟨i₀, by simp [hi₀]⟩) (hcount (a i₀))
    obtain ⟨j₀, hj₀⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter] at hj₀
    obtain ⟨j₁, hj₁, hbmax⟩ := t.exists_max_image b ⟨j₀, hj₀.1⟩
    have hj₁a : a i₀ ≤ b j₁ := hj₀.2.trans (hbmax j₀ hj₀.1)
    rw [← Finset.add_sum_erase s a hi₀, ← Finset.add_sum_erase t b hj₁]
    have hrest : ∑ i ∈ s.erase i₀, a i ≤ ∑ j ∈ t.erase j₁, b j := by
      refine ih (s.erase i₀) (by rw [Finset.card_erase_of_mem hi₀]; omega) (t.erase j₁)
        (fun j hj => hb j (Finset.mem_of_mem_erase hj)) (fun x => ?_)
      by_cases hx : x ≤ a i₀
      · have h1 : ((s.erase i₀).filter (fun i => x ≤ a i)).card + 1
            = (s.filter (fun i => x ≤ a i)).card := by
          rw [Finset.filter_erase, Finset.card_erase_add_one (by simp [hi₀, hx])]
        have h2 : ((t.erase j₁).filter (fun j => x ≤ b j)).card + 1
            = (t.filter (fun j => x ≤ b j)).card := by
          rw [Finset.filter_erase, Finset.card_erase_add_one (by simp [hj₁, hx.trans hj₁a])]
        have := hcount x
        omega
      · have : (s.erase i₀).filter (fun i => x ≤ a i) = ∅ := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_erase, Finset.notMem_empty, iff_false]
          rintro ⟨⟨-, hi⟩, hxi⟩
          exact hx (hxi.trans (hmax i hi))
        rw [this, Finset.card_empty]; exact Nat.zero_le _
    linarith
/-! ### Chains of triangle inequalities -/

/-- One segment: `c(h a, h b) ≤ ∑_{a ≤ i < b} c(h i, h (i+1))`. -/
private lemma segment_le {α : Type*} (c : α → α → ℝ) (hrefl : ∀ x, c x x = 0)
    (htri : ∀ x y z, c x z ≤ c x y + c y z) (h : ℕ → α) (a : ℕ) :
    ∀ b, a ≤ b → c (h a) (h b) ≤ ∑ i ∈ Finset.Ico a b, c (h i) (h (i + 1)) := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => simp [hrefl]
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab]
    linarith [htri (h a) (h b) (h (b + 1))]

private lemma mono_chain (q : ℕ → ℕ) (K : ℕ) (hq : ∀ j < K, q j ≤ q (j + 1)) : q 0 ≤ q K := by
  induction K with
  | zero => exact le_refl _
  | succ K ih => exact (ih (fun j hj => hq j (by omega))).trans (hq K (by omega))

/-- Visiting the points `h (q 0), h (q 1), …, h (q K)` directly is no longer than following
`h` step by step from `q 0` to `q K`. -/
private lemma chain_le {α : Type*} (c : α → α → ℝ) (hrefl : ∀ x, c x x = 0)
    (htri : ∀ x y z, c x z ≤ c x y + c y z) (h : ℕ → α) (q : ℕ → ℕ) (K : ℕ)
    (hq : ∀ j < K, q j ≤ q (j + 1)) :
    ∑ j ∈ Finset.range K, c (h (q j)) (h (q (j + 1)))
      ≤ ∑ i ∈ Finset.Ico (q 0) (q K), c (h i) (h (i + 1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ← Finset.sum_Ico_consecutive _
      (mono_chain q K (fun j hj => hq j (by omega))) (hq K (by omega))]
    have := segment_le c hrefl htri h (q K) (q (K + 1)) (hq K (by omega))
    linarith [ih (fun j hj => hq j (by omega))]
/-! ### The optimal tour shortcut to any node set -/

/-- Cyclic successor and predecessor on `Fin K`. -/
private def succC {K : ℕ} (hK : 0 < K) (j : Fin K) : Fin K :=
  ⟨if j.val + 1 = K then 0 else j.val + 1, by split_ifs <;> omega⟩

private def predC {K : ℕ} (hK : 0 < K) (j : Fin K) : Fin K :=
  ⟨if j.val = 0 then K - 1 else j.val - 1, by split_ifs <;> omega⟩

private lemma predC_succC {K : ℕ} (hK : 0 < K) (j : Fin K) : predC hK (succC hK j) = j := by
  ext; simp only [predC, succC]; have := j.isLt; split_ifs <;> simp_all <;> omega

private lemma succC_predC {K : ℕ} (hK : 0 < K) (j : Fin K) : succC hK (predC hK j) = j := by
  ext; simp only [predC, succC]; have := j.isLt; split_ifs <;> simp_all <;> omega

/-- The cyclic successor as a bijection. -/
private def succE {K : ℕ} (hK : 0 < K) : Fin K ≃ Fin K :=
  ⟨succC hK, predC hK, predC_succC hK, succC_predC hK⟩

/-- A periodic sum over any window of one period is the sum over `[0, N)`. -/
private lemma sum_Ico_period (f : ℕ → ℝ) (N : ℕ) (hf : ∀ i, f (i + N) = f i) :
    ∀ a, ∑ i ∈ Finset.Ico a (a + N), f i = ∑ i ∈ Finset.range N, f i := by
  intro a
  induction a with
  | zero => rw [Nat.zero_add, Finset.range_eq_Ico]
  | succ a ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp only [Nat.add_zero, Finset.Ico_self, Finset.sum_empty, Finset.range_zero]
    rw [← ih, Finset.sum_eq_sum_Ico_succ_bot (by omega : a < a + N),
      show a + 1 + N = a + N + 1 by omega, Finset.sum_Ico_succ_top (by omega : a + 1 ≤ a + N), hf]
    ring

/-- **Shortcut cycle.** The nodes of any nonempty set `O`, listed in the order an optimal tour
visits them, form a closed tour of length at most `z*`. -/
private lemma exists_subcycle_le {m : ℕ} (c : Fin (m + 1) → Fin (m + 1) → ℝ) (hc : IsMetric c)
    (O : Finset (Fin (m + 1))) {K : ℕ} (hK : 0 < K) (hOK : O.card = K) :
    ∃ o : Fin K → Fin (m + 1), Function.Injective o ∧ Finset.univ.image o = O ∧
      ∑ j, c (o j) (o (succC hK j)) ≤ optTourLength c := by
  obtain ⟨τ, hτ⟩ := exists_opt_tour c
  set P := O.image τ.symm with hP
  have hPcard : P.card = K := by
    rw [hP, Finset.card_image_of_injective _ τ.symm.injective]; omega
  set e := P.orderEmbOfFin hPcard with he
  set o : Fin K → Fin (m + 1) := fun j => τ (e j) with ho
  have hoinj : Function.Injective o := fun a b h => e.injective (τ.injective h)
  have hoimg : Finset.univ.image o = O := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, ho]
    constructor
    · rintro ⟨j, rfl⟩
      have hmem : e j ∈ P := P.orderEmbOfFin_mem hPcard j
      rw [hP, Finset.mem_image] at hmem
      obtain ⟨y, hy, hye⟩ := hmem
      rw [← hye, Equiv.apply_symm_apply]; exact hy
    · intro hx
      have : τ.symm x ∈ Set.range e := by
        rw [he, Finset.range_orderEmbOfFin]; exact Finset.mem_image_of_mem _ hx
      obtain ⟨j, hj⟩ := this
      exact ⟨j, by rw [hj, Equiv.apply_symm_apply]⟩
  refine ⟨o, hoinj, hoimg, ?_⟩
  set h : ℕ → Fin (m + 1) := fun i => τ ⟨i % (m + 1), Nat.mod_lt _ (by omega)⟩ with hh
  set q : ℕ → ℕ := fun j => if hj : j < K then (e ⟨j, hj⟩).val else (e ⟨0, hK⟩).val + (m + 1)
    with hq
  have hqmono : ∀ j < K, q j ≤ q (j + 1) := by
    intro j hj
    simp only [hq, dif_pos hj]
    by_cases hj' : j + 1 < K
    · rw [dif_pos hj']
      exact (e.strictMono (show (⟨j, hj⟩ : Fin K) < ⟨j + 1, hj'⟩ from
        Fin.mk_lt_mk.mpr (by omega))).le
    · rw [dif_neg hj']; have := (e ⟨j, hj⟩).isLt; omega
  have hchain := chain_le c hc.refl (fun x y z => hc.triangle x z y) h q K hqmono
  have hq0 : q 0 = (e ⟨0, hK⟩).val := by simp only [hq, dif_pos hK]
  have hqK : q K = (e ⟨0, hK⟩).val + (m + 1) := by simp only [hq, dif_neg (lt_irrefl K)]
  rw [hq0, hqK, sum_Ico_period (fun i => c (h i) (h (i + 1))) (m + 1) (by
    intro i; simp only [hh, Nat.add_mod_right, show i + (m + 1) + 1 = i + 1 + (m + 1) by omega])]
    at hchain
  have htour : ∑ i ∈ Finset.range (m + 1), c (h i) (h (i + 1)) = tourLength c τ := by
    rw [tourLength, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hh, rot_eq]
    congr 2
    · ext; simp [Nat.mod_eq_of_lt i.isLt]
    · ext; simp [Fin.val_add, Nat.add_mod_mod]
  have hleft : ∑ j ∈ Finset.range K, c (h (q j)) (h (q (j + 1)))
      = ∑ j, c (o j) (o (succC hK j)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => c (h (q j)) (h (q (j + 1))))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hj := j.isLt
    have hqj : h (q j) = o j := by
      simp only [hh, hq, dif_pos hj, ho]
      congr 1; ext; simp [Nat.mod_eq_of_lt (e j).isLt]
    have hqs : h (q (j + 1)) = o (succC hK j) := by
      by_cases hj' : j.val + 1 = K
      · have hs : succC hK j = ⟨0, hK⟩ := by ext; simp [succC, hj']
        rw [hs]
        simp only [hh, hq, ho, dif_neg (show ¬ (j.val + 1 < K) by omega)]
        congr 1; ext
        simp [Nat.add_mod_right, Nat.mod_eq_of_lt (e _).isLt]
      · have hs : succC hK j = ⟨j.val + 1, by omega⟩ := by ext; simp [succC, hj']
        rw [hs]
        simp only [hh, hq, ho, dif_pos (show j.val + 1 < K by omega)]
        congr 1; ext
        simp [Nat.mod_eq_of_lt (e _).isLt]
    rw [hqj, hqs]
  rw [← hleft, ← hτ, ← htour]
  exact hchain

/-- Telescoping a sum over consecutive windows `[q j, q (j+1))`. -/
private lemma sum_windows (f : ℕ → ℝ) (q : ℕ → ℕ) (K : ℕ) (hq : ∀ j < K, q j ≤ q (j + 1)) :
    ∑ j ∈ Finset.range K, ∑ i ∈ Finset.Ico (q j) (q (j + 1)), f i
      = ∑ i ∈ Finset.Ico (q 0) (q K), f i := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih (fun j hj => hq j (by omega)),
      Finset.sum_Ico_consecutive _ (mono_chain q K (fun j hj => hq j (by omega))) (hq K (by omega))]

theorem solution {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : IsMetric c) (hn : 1 ≤ n)
    (τ : Equiv.Perm (Fin n)) (hτ : IsNearestNeighborTour c τ) :
    tourLength c τ ≤ (1 / 2 : ℝ) * (Nat.clog 2 n + 1) * optTourLength c := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- `l p` is the length of the tour edge leaving `p`.
  set l : Fin (m + 1) → ℝ := fun p => c p (τ (finRotate (m + 1) (τ.symm p))) with hl
  have hl0 : ∀ p, 0 ≤ l p := fun p => hc.nonneg _ _
  have hsum : tourLength c τ = ∑ p, l p := by
    rw [tourLength, ← Equiv.sum_comp τ l]
    simp only [hl, Equiv.symm_apply_apply]
  have hz : 0 ≤ optTourLength c := by
    obtain ⟨σ, hσ⟩ := exists_opt_tour c
    rw [← hσ]; exact Finset.sum_nonneg (fun k _ => hc.nonneg _ _)
  -- Any distance is at most half the optimal tour.
  have htwo : ∀ p q, 2 * c p q ≤ optTourLength c := by
    intro p q
    by_cases hpq : p = q
    · rw [hpq, hc.refl]; linarith
    have hcard : ({p, q} : Finset (Fin (m + 1))).card = 2 := Finset.card_pair hpq
    obtain ⟨o, hoinj, hoimg, hcyc⟩ := exists_subcycle_le c hc {p, q} (by norm_num) hcard
    have hs0 : succC (by norm_num : 0 < 2) 0 = 1 := by ext; simp [succC]
    have hs1 : succC (by norm_num : 0 < 2) 1 = 0 := by ext; simp [succC]
    rw [Fin.sum_univ_two, hs0, hs1, hc.symm (o 1) (o 0)] at hcyc
    have hmem : ∀ j, o j ∈ ({p, q} : Finset (Fin (m + 1))) := fun j => by
      rw [← hoimg]; exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
    have h01 : o 0 ≠ o 1 := fun h => absurd (hoinj h) (by decide)
    have h0 := hmem 0; have h1 := hmem 1
    simp only [Finset.mem_insert, Finset.mem_singleton] at h0 h1
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rw [h0, h1] at hcyc h01
    · exact absurd rfl h01
    · linarith
    · rw [hc.symm] at hcyc; linarith
    · exact absurd rfl h01
  -- The nearest neighbor rule: `min(l p, l q) ≤ c(p, q)` for distinct nodes.
  have hmin : ∀ p q, p ≠ q → min (l p) (l q) ≤ c p q := by
    have key : ∀ p q, τ.symm p < τ.symm q → l p ≤ c p q := by
      intro p q hab
      have hb := (τ.symm q).isLt
      have := hτ (τ.symm p) q (by rw [Fin.lt_def] at hab; omega) (fun k hk hkq => by
        rw [← hkq, Equiv.symm_apply_apply] at hab
        exact absurd hk (not_le.mpr hab))
      simpa only [hl, Equiv.apply_symm_apply] using this
    intro p q hpq
    rcases lt_or_gt_of_ne (fun h => hpq (τ.symm.injective h)) with h | h
    · exact (min_le_left _ _).trans (key p q h)
    · exact (min_le_right _ _).trans ((key q p h).trans (hc.symm q p).le)
  -- Sort the nodes by decreasing `l`.
  set σ := Tuple.sort (fun p => -l p) with hσ
  have hanti : ∀ i j : Fin (m + 1), i ≤ j → l (σ j) ≤ l (σ i) := by
    intro i j hij
    have := Tuple.monotone_sort (fun p => -l p) hij
    simp only [Function.comp_apply] at this
    linarith
  set lσ : ℕ → ℝ := fun i => if h : i < m + 1 then l (σ ⟨i, h⟩) else 0 with hlσ
  -- **Block bound.** For `1 ≤ k < n`, the `k+1`-st to `2k`-th largest values sum to at most `z*/2`.
  have hblock : ∀ k, 1 ≤ k → k < m + 1 →
      2 * ∑ i ∈ Finset.Ico k (min (2 * k) (m + 1)), lσ i ≤ optTourLength c := by
    intro k hk1 hkn
    set s := min (2 * k) (m + 1) with hs
    have hs2 : 2 ≤ s := by omega
    have hsn : s ≤ m + 1 := min_le_right _ _
    have hsk : s ≤ 2 * k := min_le_left _ _
    have hs0 : 0 < s := by omega
    -- The `s` nodes with the largest values.
    set f : Fin s → Fin (m + 1) := fun i => σ (Fin.castLE hsn i) with hf
    have hfinj : Function.Injective f := fun a b h =>
      Fin.castLE_injective hsn (σ.injective h)
    set O := Finset.univ.image f with hO
    have hOcard : O.card = s := by
      rw [hO, Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_fin]
    obtain ⟨o, hoinj, hoimg, hcyc⟩ := exists_subcycle_le c hc O hs0 hOcard
    have hsucc_ne : ∀ j, succC hs0 j ≠ j := by
      intro j h; have hv := congrArg Fin.val h; simp only [succC] at hv
      have hj := j.isLt; split_ifs at hv <;> omega
    -- Each edge of the shortcut cycle is at least the smaller value at its ends.
    have hge : ∑ j, min (l (o j)) (l (o (succC hs0 j))) ≤ ∑ j, c (o j) (o (succC hs0 j)) :=
      Finset.sum_le_sum (fun j _ => hmin _ _ (fun h => hsucc_ne j (hoinj h).symm))
    -- Threshold counting shows the cycle's minima dominate two copies of the lower half.
    have hmaj : ∑ pr ∈ Finset.Ico k s ×ˢ (Finset.univ : Finset (Fin 2)), lσ pr.1
        ≤ ∑ j, min (l (o j)) (l (o (succC hs0 j))) := by
      refine sum_le_of_count_le (fun pr : ℕ × Fin 2 => lσ pr.1)
        (fun j => min (l (o j)) (l (o (succC hs0 j)))) _ _
        (fun j _ => le_min (hl0 _) (hl0 _)) (fun x => ?_)
      set bc := ((Finset.Ico k s).filter (fun i => x ≤ lσ i)).card with hbc
      have hA : ((Finset.Ico k s ×ˢ (Finset.univ : Finset (Fin 2))).filter
          (fun pr => x ≤ lσ pr.1)).card = 2 * bc := by
        have : (Finset.Ico k s ×ˢ (Finset.univ : Finset (Fin 2))).filter (fun pr => x ≤ lσ pr.1)
            = ((Finset.Ico k s).filter (fun i => x ≤ lσ i)) ×ˢ (Finset.univ : Finset (Fin 2)) := by
          ext ⟨i, e⟩; simp
        rw [this, Finset.card_product, Finset.card_univ, Fintype.card_fin, mul_comm]
      rw [hA]
      rcases Nat.eq_zero_or_pos bc with hb0 | hbpos
      · rw [hb0]; exact Nat.zero_le _
      obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp hbpos
      simp only [Finset.mem_filter, Finset.mem_Ico] at hi₀
      -- Values above `x` among the top `s`: all of the top `k`, plus `bc` of the rest.
      set U := O.filter (fun p => x ≤ l p) with hU
      have hW : k + bc ≤ U.card := by
        set W := (Finset.range s).filter (fun i => x ≤ lσ i) with hW
        have hWsup : Finset.range k ∪ (Finset.Ico k s).filter (fun i => x ≤ lσ i) ⊆ W := by
          intro i hi
          simp only [Finset.mem_union, Finset.mem_range, Finset.mem_filter, Finset.mem_Ico] at hi
          simp only [hW, Finset.mem_filter, Finset.mem_range]
          rcases hi with hi | hi
          · refine ⟨by omega, hi₀.2.trans ?_⟩
            simp only [hlσ, dif_pos (show i < m + 1 by omega), dif_pos (show i₀ < m + 1 by omega)]
            exact hanti _ _ (Fin.mk_le_mk.mpr (by omega))
          · exact ⟨by omega, hi.2⟩
        have hdisj : Disjoint (Finset.range k) ((Finset.Ico k s).filter (fun i => x ≤ lσ i)) := by
          rw [Finset.disjoint_left]; intro i hi hi'
          simp only [Finset.mem_range, Finset.mem_filter, Finset.mem_Ico] at hi hi'; omega
        have h1 := Finset.card_le_card hWsup
        rw [Finset.card_union_of_disjoint hdisj, Finset.card_range] at h1
        have h2 : W.card ≤ U.card := by
          refine Finset.card_le_card_of_injOn
            (fun i => σ ⟨i % (m + 1), Nat.mod_lt _ (by omega)⟩) (fun i hi => ?_) (fun i hi j hj h => ?_)
          · simp only [hW, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi
            simp only [hU, Finset.coe_filter, Set.mem_ofPred_eq, hO, Finset.mem_image,
              Finset.mem_univ, true_and]
            refine ⟨⟨⟨i, hi.1⟩, ?_⟩, ?_⟩
            · simp only [hf]; congr 1; ext; simp [Nat.mod_eq_of_lt (show i < m + 1 by omega)]
            · have := hi.2
              simp only [hlσ, dif_pos (show i < m + 1 by omega)] at this
              convert this using 3; ext; simp [Nat.mod_eq_of_lt (show i < m + 1 by omega)]
          · simp only [hW, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi hj
            have := congrArg Fin.val (σ.injective h)
            simp only [Nat.mod_eq_of_lt (show i < m + 1 by omega),
              Nat.mod_eq_of_lt (show j < m + 1 by omega)] at this
            exact this
        omega
      -- Positions of the cycle whose node, resp. successor, is above `x`.
      set X := Finset.univ.filter (fun j : Fin s => x ≤ l (o j)) with hX
      set Y := Finset.univ.filter (fun j : Fin s => x ≤ l (o (succC hs0 j))) with hY
      have hXU : X.card = U.card := by
        rw [← Finset.card_image_of_injective X hoinj, hU, ← hoimg, Finset.filter_image]
      have hYX : Y.card = X.card := by
        simp only [hX, hY, Finset.card_filter]
        exact Equiv.sum_comp (succE hs0) (fun j => if x ≤ l (o j) then 1 else 0)
      have hinter : (Finset.univ.filter
          (fun j : Fin s => x ≤ min (l (o j)) (l (o (succC hs0 j))))) = X ∩ Y := by
        ext j; simp [hX, hY]
      rw [hinter]
      have hunion : (X ∪ Y).card ≤ s := by
        calc (X ∪ Y).card ≤ (Finset.univ : Finset (Fin s)).card := Finset.card_le_univ _
          _ = s := by rw [Finset.card_univ, Fintype.card_fin]
      have := Finset.card_union_add_card_inter X Y
      omega
    have hA2 : ∑ pr ∈ Finset.Ico k s ×ˢ (Finset.univ : Finset (Fin 2)), lσ pr.1
        = 2 * ∑ i ∈ Finset.Ico k s, lσ i := by
      rw [Finset.sum_product]
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.mul_sum, two_mul]
    linarith
  -- Sum the blocks `[2^j, 2^(j+1))` for `j < ⌈log₂ n⌉`.
  set L := Nat.clog 2 (m + 1) with hL
  have hsorted : ∑ p, l p = lσ 0 + ∑ i ∈ Finset.Ico 1 (m + 1), lσ i := by
    calc ∑ p, l p = ∑ i : Fin (m + 1), l (σ i) := (Equiv.sum_comp σ l).symm
      _ = ∑ i : Fin (m + 1), lσ i.val := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          simp only [hlσ, dif_pos i.isLt, Fin.eta]
      _ = ∑ i ∈ Finset.range (m + 1), lσ i := Fin.sum_univ_eq_sum_range lσ (m + 1)
      _ = lσ 0 + ∑ i ∈ Finset.Ico 1 (m + 1), lσ i := by
          rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  set q : ℕ → ℕ := fun j => min (2 ^ j) (m + 1) with hq
  have hqmono : ∀ j < L, q j ≤ q (j + 1) := by
    intro j _
    simp only [hq]
    exact min_le_min_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hq0 : q 0 = 1 := by simp [hq]
  have hqL : q L = m + 1 := by
    simp only [hq, hL]
    exact min_eq_right (Nat.le_pow_clog (by norm_num) _)
  have hwin := sum_windows lσ q L hqmono
  rw [hq0, hqL] at hwin
  -- Each window contributes at most `z*/2`.
  have hwinle : ∀ j ∈ Finset.range L,
      2 * ∑ i ∈ Finset.Ico (q j) (q (j + 1)), lσ i ≤ optTourLength c := by
    intro j _
    by_cases hj : 2 ^ j < m + 1
    · have hqj : q j = 2 ^ j := by simp only [hq]; exact min_eq_left hj.le
      have hqj1 : q (j + 1) = min (2 * 2 ^ j) (m + 1) := by simp only [hq, pow_succ, mul_comm]
      rw [hqj, hqj1]
      exact hblock (2 ^ j) (Nat.one_le_two_pow) hj
    · have hqj : q j = m + 1 := by simp only [hq]; exact min_eq_right (by omega)
      have hqj1 : q (j + 1) = m + 1 := by
        simp only [hq]; exact min_eq_right ((by omega : m + 1 ≤ 2 ^ j).trans
          (Nat.pow_le_pow_right (by norm_num) (by omega)))
      rw [hqj, hqj1, Finset.Ico_self, Finset.sum_empty]; linarith
  have hfirst : 2 * lσ 0 ≤ optTourLength c := by
    simp only [hlσ, dif_pos (show 0 < m + 1 by omega)]
    exact htwo _ _
  have hwsum : 2 * ∑ j ∈ Finset.range L, ∑ i ∈ Finset.Ico (q j) (q (j + 1)), lσ i
      ≤ L * optTourLength c := by
    rw [Finset.mul_sum]
    calc ∑ j ∈ Finset.range L, 2 * ∑ i ∈ Finset.Ico (q j) (q (j + 1)), lσ i
        ≤ ∑ j ∈ Finset.range L, optTourLength c := Finset.sum_le_sum hwinle
      _ = L * optTourLength c := by simp
  rw [hsum, hsorted, ← hwin]
  have : (Nat.clog 2 (m + 1) : ℝ) = (L : ℝ) := by rw [hL]
  rw [this]
  nlinarith
