-- Prove2me | solution 1 for ReentrantScheduling.FBFS.gamma1_busy_period_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T08:22:42.367211+00:00
-- url     : https://prove2.me/submissions/44e5b9ec-c33a-4083-95bc-dec3878915b9

import Mathlib
import Definitions.Def_ReentrantScheduling_FBFS_Model
import Definitions.Def_ReentrantScheduling_FBFS_Constants

open ReentrantScheduling.FBFS Finset

theorem solution
    (L : Line) (lam γ : ℝ) (hlam : 0 ≤ lam) (hγ : 0 ≤ γ) (hload : L.load lam < 1)
    (R : Run L) (hR : R.Admissible L.fbfs) (harr : R.Arrivals lam γ)
    (T₁ T₂ : ℝ) (hT₁ : 0 < T₁) (hT₁₂ : T₁ ≤ T₂)
    (hcommence : ∃ δ > 0, ∀ t : ℝ, T₁ - δ < t → t < T₁ →
      ∀ q, ¬ R.Waiting q ⟨0, L.l_pos⟩ t)
    (hbusy : ∀ t : ℝ, T₁ ≤ t → t ≤ T₂ → R.Busy ⟨0, L.l_pos⟩ t) :
    T₂ - T₁ ≤ L.Gamma lam γ ⟨0, L.l_pos⟩ := by
  set i0 : Fin L.l := ⟨0, L.l_pos⟩ with hi0
  set σ := L.center i0 with hσ
  set m : ℝ := (L.m σ : ℝ) with hm_def
  set τ1 := L.τ i0 with hτ1
  obtain ⟨δ, hδ, hcom⟩ := hcommence
  have hm : 0 < m := by rw [hm_def]; exact_mod_cast L.m_pos σ
  have hτ1p : 0 < τ1 := L.τ_pos i0
  have hle0 : ∀ j : Fin L.l, j ≤ i0 ↔ j = i0 := by
    intro j; constructor
    · intro h; exact Fin.ext (by rw [Fin.le_def] at h; simp [hi0] at h ⊢; omega)
    · intro h; rw [h]
  have hτbar : ∀ j, L.τ j ≤ L.τbar := fun j => by
    unfold Line.τbar; exact le_sup' L.τ (mem_univ _)
  have hτbarp : 0 < L.τbar := lt_of_lt_of_le hτ1p (hτbar i0)
  -- the load of buffer b_1 alone is below one
  have hc : lam * τ1 / m < 1 := by
    have h1 : τ1 / m ≤ L.w σ := by
      unfold Line.w
      exact single_le_sum (f := fun i => L.τ i / (L.m σ : ℝ))
        (fun i _ => div_nonneg (L.τ_pos i).le hm.le) (by simp [hσ])
    have h2 : L.w σ ≤ L.wbar := by unfold Line.wbar; exact le_sup' L.w (mem_univ _)
    have h3 : lam * L.wbar < 1 := hload
    have : lam * (τ1 / m) ≤ lam * L.wbar := mul_le_mul_of_nonneg_left (h1.trans h2) hlam
    rw [mul_div_assoc]; linarith
  -- Γ^(1) in closed form
  have hfilt : univ.filter (fun j => j ≤ i0 ∧ L.center j = L.center i0) = {i0} := by
    ext j; simp only [mem_filter, mem_univ, true_and, mem_singleton, hle0]
    constructor
    · exact fun h => h.1
    · intro h; exact ⟨h, by rw [h]⟩
  have hGB : L.GammaBar lam γ i0 = 0 := by
    unfold Line.GammaBar
    apply sum_eq_zero
    intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj
    exact absurd hj (by rw [Fin.lt_def]; simp [hi0])
  have hGam : L.Gamma lam γ i0 = (2 * L.τbar + γ * τ1 / m) / (1 - lam * τ1 / m) := by
    rw [Line.Gamma_eq, hfilt, sum_singleton, sum_singleton, hGB]
    congr 2; ring
  rw [hGam]
  -- reduce to the counting inequality
  set D := T₂ - T₁ with hD
  set ε := min T₁ L.τbar with hε
  have hεp : 0 < ε := lt_min hT₁ hτbarp
  have hεle : ε ≤ L.τbar := min_le_right _ _
  have hεT : ε ≤ T₁ := min_le_left _ _
  suffices hcount : m * (D - L.τbar) ≤ τ1 * (lam * (D + ε) + γ) by
    have hden : 0 < 1 - lam * τ1 / m := by linarith
    rw [le_div_iff₀ hden]
    have hcε : lam * τ1 / m * ε ≤ L.τbar := by
      have : lam * τ1 / m * ε ≤ 1 * ε :=
        mul_le_mul_of_nonneg_right hc.le hεp.le
      linarith
    have e1 : D - L.τbar ≤ lam * τ1 / m * (D + ε) + γ * τ1 / m := by
      have : D - L.τbar ≤ τ1 * (lam * (D + ε) + γ) / m := by
        rw [le_div_iff₀ hm]; linarith
      calc D - L.τbar ≤ τ1 * (lam * (D + ε) + γ) / m := this
        _ = lam * τ1 / m * (D + ε) + γ * τ1 / m := by field_simp
    nlinarith
  by_cases hsmall : D < L.τbar
  · have : 0 ≤ τ1 * (lam * (D + ε) + γ) := by
      apply mul_nonneg hτ1p.le; have : 0 ≤ D := by linarith
      positivity
    nlinarith
  push Not at hsmall
  -- grid points
  set K := ⌊(D - L.τbar) / τ1⌋₊ with hK
  have hKlt : (D - L.τbar) / τ1 < (K : ℝ) + 1 := Nat.lt_floor_add_one _
  have hKle : (K : ℝ) * τ1 ≤ D - L.τbar := by
    have := Nat.floor_le (div_nonneg (by linarith : 0 ≤ D - L.τbar) hτ1p.le)
    rw [← hK] at this; rwa [le_div_iff₀ hτ1p] at this
  set t : ℕ → ℝ := fun k => T₁ + L.τbar + k * τ1 with ht
  have ht_lo : ∀ k, T₁ + L.τbar ≤ t k := fun k => by
    simp only [ht]; have : (0 : ℝ) ≤ k * τ1 := by positivity
    linarith
  have ht_hi : ∀ k ≤ K, t k ≤ T₂ := fun k hk => by
    simp only [ht]
    have : (k : ℝ) * τ1 ≤ K * τ1 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hτ1p.le
    linarith
  -- real start times
  have real_of_le : ∀ (x : WithTop ℝ) (r : ℝ), x ≤ (r : WithTop ℝ) → ∃ s : ℝ, x = s ∧ s ≤ r := by
    intro x r h
    cases x with
    | top => exact absurd h (by simp)
    | coe s => exact ⟨s, rfl, by exact_mod_cast h⟩
  -- busy at time u gives a waiting part in b_1
  have busy_wait : ∀ u, T₁ ≤ u → u ≤ T₂ → ∃ q, R.Waiting q i0 u := by
    intro u h1 h2
    obtain ⟨q, j, -, hj, hw⟩ := hbusy u h1 h2
    rw [hle0] at hj; subst hj; exact ⟨q, hw⟩
  -- every slot in service at center σ at a time u ∈ [T₁ + τ̄, T₂] is at buffer b_1
  have slot_b1 : ∀ u, T₁ + L.τbar ≤ u → u ≤ T₂ → ∀ x ∈ R.busySlots σ u, x.2 = i0 := by
    intro u hu1 hu2 x hx
    obtain ⟨hcx, hentry, hst, hfin⟩ := hx
    obtain ⟨s, hs, hsu⟩ := real_of_le _ _ hst
    by_contra hne
    by_cases hsT : s < T₁
    · rw [hs] at hfin
      have : u < s + L.τ x.2 := by exact_mod_cast hfin
      linarith [hτbar x.2]
    · push Not at hsT
      obtain ⟨q', hq'⟩ := busy_wait s hsT (by linarith)
      have hpos : i0 < x.2 := lt_of_le_of_ne (Fin.mk_le_mk.mpr (Nat.zero_le _)) (Ne.symm hne)
      exact hR.priority x.1 x.2 s (by linarith) hentry hs q' i0 (by rw [hcx]) hpos hq'
  -- the sets of parts in service at b_1 at the grid times
  set B : ℕ → Set R.Part := fun k => {q | R.InService q i0 (t k)} with hB
  have B_card : ∀ k ≤ K, (L.m σ : ℕ∞) ≤ (B k).encard := by
    intro k hk
    obtain ⟨q, hq⟩ := busy_wait (t k) (by linarith [ht_lo k]) (ht_hi k hk)
    have hfull := hR.nonidling σ (t k) (by linarith [ht_lo k]) ⟨q, i0, rfl, hq⟩
    rw [← hfull]
    have hinj : Set.InjOn Prod.fst (R.busySlots σ (t k)) := by
      intro x hx y hy hxy
      have h1 := slot_b1 (t k) (ht_lo k) (ht_hi k hk) x hx
      have h2 := slot_b1 (t k) (ht_lo k) (ht_hi k hk) y hy
      exact Prod.ext hxy (h1.trans h2.symm)
    rw [← hinj.encard_image]
    apply Set.encard_le_encard
    rintro _ ⟨x, hx, rfl⟩
    have h1 := slot_b1 (t k) (ht_lo k) (ht_hi k hk) x hx
    have := hx.2
    rw [h1] at this
    exact this
  -- service window
  have B_real : ∀ k q, q ∈ B k → ∃ s : ℝ, R.start q i0 = s ∧ s ≤ t k ∧ t k < s + τ1 := by
    intro k q hq
    obtain ⟨-, hst, hfin⟩ := hq
    obtain ⟨s, hs, hsu⟩ := real_of_le _ _ hst
    rw [hs] at hfin
    exact ⟨s, hs, hsu, by exact_mod_cast hfin⟩
  have B_disj : ∀ k k', k < k' → Disjoint (B k) (B k') := by
    intro k k' hkk
    rw [Set.disjoint_left]
    intro q hq hq'
    obtain ⟨s, hs, h1, h2⟩ := B_real k q hq
    obtain ⟨s', hs', h1', h2'⟩ := B_real k' q hq'
    rw [hs] at hs'
    have hss : s = s' := by exact_mod_cast hs'
    have : (k : ℝ) + 1 ≤ k' := by exact_mod_cast hkk
    have : t k + τ1 ≤ t k' := by simp only [ht]; nlinarith
    linarith
  -- union of the first n+1 grid sets
  set U : ℕ → Set R.Part := fun n => {q | ∃ k ≤ n, q ∈ B k} with hU
  have U_card : ∀ n ≤ K, (((n + 1) * L.m σ : ℕ) : ℕ∞) ≤ (U n).encard := by
    intro n
    induction n with
    | zero =>
      intro _
      have hU0 : U 0 = B 0 := by
        ext q; simp only [hU, Set.mem_setOf_eq, Nat.le_zero]
        constructor
        · rintro ⟨k, rfl, h⟩; exact h
        · intro h; exact ⟨0, rfl, h⟩
      rw [hU0]; simpa using B_card 0 (Nat.zero_le _)
    | succ n ih =>
      intro hn
      have hsplit : U (n + 1) = U n ∪ B (n + 1) := by
        ext q; simp only [hU, Set.mem_setOf_eq, Set.mem_union]
        constructor
        · rintro ⟨k, hk, h⟩
          rcases Nat.lt_or_ge k (n + 1) with hk' | hk'
          · exact Or.inl ⟨k, by omega, h⟩
          · right; have : k = n + 1 := by omega
            rw [← this]; exact h
        · rintro (⟨k, hk, h⟩ | h)
          · exact ⟨k, by omega, h⟩
          · exact ⟨n + 1, le_refl _, h⟩
      have hdisj : Disjoint (U n) (B (n + 1)) := by
        rw [Set.disjoint_left]
        rintro q ⟨k, hk, hq⟩ hq'
        exact Set.disjoint_left.mp (B_disj k (n + 1) (by omega)) hq hq'
      rw [hsplit, Set.encard_union_eq hdisj]
      have h1 := ih (by omega)
      have h2 := B_card (n + 1) hn
      calc ((((n + 1 + 1) * L.m σ : ℕ)) : ℕ∞)
          = (((n + 1) * L.m σ : ℕ) : ℕ∞) + (L.m σ : ℕ∞) := by push_cast; ring
        _ ≤ (U n).encard + (B (n + 1)).encard := add_le_add h1 h2
  -- every part of U K is a part released in (T₁ - ε, T₂]
  have hsub : U K ⊆ {p | ¬ R.initial p ∧ T₁ - ε < R.α p ∧ R.α p ≤ T₂} := by
    rintro q ⟨k, hk, hq⟩
    have hentry : R.entry q = i0 := (hle0 _).mp hq.1
    obtain ⟨s, hs, h1, h2⟩ := B_real k q hq
    have hsT : T₁ < s := by linarith [ht_lo k, hτbar i0]
    have harrq : R.arrive q i0 = ((R.α q : ℝ) : WithTop ℝ) := by
      unfold Run.arrive; rw [if_pos hentry.symm]
    have hprec := hR.precedence q i0 hq.1
    have hαs : R.α q ≤ s := by
      rcases hprec with h | h
      · rw [harrq, hs] at h; exact_mod_cast h
      · exfalso; rw [hs] at h
        have : s ≤ 0 := by exact_mod_cast h.2.2.2
        linarith
    have hαT : T₁ ≤ R.α q := by
      by_contra hlt; push Not at hlt
      set u := max (R.α q) (T₁ - δ / 2)
      refine hcom u (lt_of_lt_of_le (by linarith) (le_max_right _ _))
        (max_lt hlt (by linarith)) q ⟨hq.1, ?_, ?_⟩
      · rw [harrq]; exact_mod_cast le_max_left _ _
      · rw [hs]; exact_mod_cast (show u < s from max_lt (by linarith) (by linarith))
    have hni : ¬ R.initial q := by
      intro hi; rw [R.α_initial q hi] at hαT; linarith
    exact ⟨hni, by linarith, by linarith [ht_hi k hk]⟩
  have harrK := harr (T₁ - ε) T₂ (by linarith) (by linarith)
  have hcK : ((((K + 1) * L.m σ : ℕ) : ℕ∞) : ENNReal) ≤
      ENNReal.ofReal (lam * (T₂ - (T₁ - ε)) + γ) :=
    le_trans (ENat.toENNReal_le.mpr ((U_card K le_rfl).trans (Set.encard_le_encard hsub))) harrK
  rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast,
    ENNReal.ofReal_le_ofReal_iff (by nlinarith)] at hcK
  push_cast at hcK
  have hK1 : D - L.τbar < ((K : ℝ) + 1) * τ1 := by rwa [div_lt_iff₀ hτ1p] at hKlt
  have : T₂ - (T₁ - ε) = D + ε := by rw [hD]; ring
  rw [this] at hcK
  have : m * (D - L.τbar) ≤ m * (((K : ℝ) + 1) * τ1) := by nlinarith
  nlinarith
