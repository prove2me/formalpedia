-- Prove2me | solution 1 for TeschlODE.IntervalMaps.tent_topEquiv_shift
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:57:19.77809+00:00
-- url     : https://prove2.me/submissions/aaaa77f2-3419-444d-b780-df812833f935

import Mathlib
import Definitions.Def_TeschlODE_Shared_tentRepellor
import Definitions.Def_TeschlODE_Shared_tentMap
import Definitions.Def_TeschlODE_Shared_itinerary
import Definitions.Def_TeschlODE_Shared_shift
import Definitions.Def_TeschlODE_Shared_symDist

open TeschlODE.Shared

lemma tent_le_half_core (μ x : ℝ) (hx : x ≤ 1 / 2) : tentMap μ x = μ * x := by
  unfold tentMap
  rw [abs_of_nonpos (by linarith)]; ring

lemma tent_ge_half_core (μ x : ℝ) (hx : 1 / 2 ≤ x) : tentMap μ x = μ * (1 - x) := by
  unfold tentMap
  rw [abs_of_nonneg (by linarith)]; ring

lemma tent_mem_iff_core (μ z : ℝ) :
    z ∈ tentRepellor μ ↔ z ∈ Set.Icc (0 : ℝ) 1 ∧ tentMap μ z ∈ tentRepellor μ := by
  constructor
  · intro h
    exact ⟨by simpa using h 0, fun n => by
      have := h (n + 1); rwa [Function.iterate_succ_apply] at this⟩
  · rintro ⟨h0, h1⟩ n
    cases n with
    | zero => simpa using h0
    | succ n => rw [Function.iterate_succ_apply]; exact h1 n

lemma tent_zero_mem_core (μ : ℝ) : (0 : ℝ) ∈ tentRepellor μ := by
  have hfix : tentMap μ 0 = 0 := by unfold tentMap; norm_num
  intro n
  rw [Function.iterate_fixed hfix]
  simp

lemma tent_one_mem_core (μ : ℝ) : (1 : ℝ) ∈ tentRepellor μ := by
  rw [tent_mem_iff_core]
  refine ⟨by simp, ?_⟩
  have : tentMap μ 1 = 0 := by unfold tentMap; norm_num
  rw [this]; exact tent_zero_mem_core μ

/-- points of `Λ` lie in `I₀ ∪ I₁` -/
lemma tent_gap_core (μ : ℝ) (hμ : 2 < μ) (z : ℝ) (hz : z ∈ tentRepellor μ) :
    z ≤ 1 / μ ∨ 1 - 1 / μ ≤ z := by
  rw [tent_mem_iff_core] at hz
  obtain ⟨⟨h0, h1⟩, hT⟩ := hz
  have hT1 : tentMap μ z ≤ 1 := (hT 0).2
  have hμ0 : 0 < μ := by linarith
  by_contra hc
  push Not at hc
  rcases le_total z (1 / 2) with hz2 | hz2
  · rw [tent_le_half_core μ z hz2] at hT1
    have : 1 / μ * μ < z * μ := mul_lt_mul_of_pos_right hc.1 hμ0
    rw [div_mul_cancel₀ _ hμ0.ne'] at this
    linarith
  · rw [tent_ge_half_core μ z hz2] at hT1
    have : 1 / μ * μ < (1 - z) * μ := mul_lt_mul_of_pos_right (by linarith) hμ0
    rw [div_mul_cancel₀ _ hμ0.ne'] at this
    linarith

lemma tent_no_interval_core (μ : ℝ) (hμ : 2 < μ) :
    ∀ n : ℕ, ∀ x y : ℝ, x < y → Set.Icc x y ⊆ tentRepellor μ → μ ^ n * (y - x) ≤ 1 := by
  have hμ0 : 0 < μ := by linarith
  have hhalf : 1 / μ < 1 / 2 := by
    rw [div_lt_div_iff₀ hμ0 (by norm_num)]; linarith
  intro n
  induction n with
  | zero =>
    intro x y hxy hsub
    have hx := (hsub ⟨le_rfl, hxy.le⟩ 0)
    have hy := (hsub ⟨hxy.le, le_rfl⟩ 0)
    simp at hx hy
    simp; linarith
  | succ n ih =>
    intro x y hxy hsub
    have hxL := hsub ⟨le_rfl, hxy.le⟩
    have hyL := hsub ⟨hxy.le, le_rfl⟩
    -- the interval lies in `I₀` or in `I₁`
    by_cases hI0 : y ≤ 1 / μ
    · have hsub' : Set.Icc (μ * x) (μ * y) ⊆ tentRepellor μ := by
        intro w hw
        have hwx : x ≤ w / μ := by rw [le_div_iff₀ hμ0]; linarith [hw.1]
        have hwy : w / μ ≤ y := by rw [div_le_iff₀ hμ0]; linarith [hw.2]
        have hm := hsub ⟨hwx, hwy⟩
        rw [tent_mem_iff_core] at hm
        have : tentMap μ (w / μ) = w := by
          rw [tent_le_half_core μ _ (by linarith)]; field_simp
        rw [← this]; exact hm.2
      have := ih (μ * x) (μ * y) (by nlinarith) hsub'
      rw [pow_succ]; nlinarith
    · by_cases hI1 : 1 - 1 / μ ≤ x
      · have hsub' : Set.Icc (μ * (1 - y)) (μ * (1 - x)) ⊆ tentRepellor μ := by
          intro w hw
          have hwx : x ≤ 1 - w / μ := by
            have : w / μ ≤ 1 - x := by rw [div_le_iff₀ hμ0]; linarith [hw.2]
            linarith
          have hwy : 1 - w / μ ≤ y := by
            have : 1 - y ≤ w / μ := by rw [le_div_iff₀ hμ0]; linarith [hw.1]
            linarith
          have hm := hsub ⟨hwx, hwy⟩
          rw [tent_mem_iff_core] at hm
          have : tentMap μ (1 - w / μ) = w := by
            rw [tent_ge_half_core μ _ (by linarith)]; field_simp; ring
          rw [← this]; exact hm.2
        have := ih (μ * (1 - y)) (μ * (1 - x)) (by nlinarith) hsub'
        rw [pow_succ]; nlinarith
      · exfalso
        push Not at hI0 hI1
        -- a point of the gap lies in the interval
        set w := max x (1 / μ + (1 - 2 / μ) / 4) with hw
        have hgap : 1 / μ < w ∧ w < 1 - 1 / μ := by
          constructor
          · have : 1 / μ < 1 / μ + (1 - 2 / μ) / 4 := by
              have : 2 / μ < 1 := by rw [div_lt_one hμ0]; linarith
              linarith
            exact lt_of_lt_of_le this (le_max_right _ _)
          · rcases le_total x (1 / μ + (1 - 2 / μ) / 4) with h | h
            · rw [hw, max_eq_right h]
              have : 2 / μ < 1 := by rw [div_lt_one hμ0]; linarith
              have e : 2 / μ = 2 * (1 / μ) := by ring
              linarith
            · rw [hw, max_eq_left h]; exact hI1
        have hwmem : w ∈ Set.Icc x y := by
          refine ⟨le_max_left _ _, ?_⟩
          rcases le_total x (1 / μ + (1 - 2 / μ) / 4) with h | h
          · rw [hw, max_eq_right h]
            by_contra hc; push Not at hc
            have := tent_gap_core μ hμ y hyL
            have h2 : 2 / μ < 1 := by rw [div_lt_one hμ0]; linarith
            have e : 2 / μ = 2 * (1 / μ) := by ring
            rcases this with h' | h' <;> linarith
          · rw [hw, max_eq_left h]; exact hxy.le
        rcases tent_gap_core μ hμ w (hsub hwmem) with h' | h' <;> linarith [hgap.1, hgap.2]

lemma tent_exists_gap_core (μ : ℝ) (hμ : 2 < μ) (x y : ℝ) (hxy : x < y) :
    ¬ Set.Icc x y ⊆ tentRepellor μ := by
  intro hsub
  have h1 : 1 < μ := by linarith
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / (y - x)) h1
  have := tent_no_interval_core μ hμ n x y hxy hsub
  have hpos : 0 < y - x := by linarith
  rw [div_lt_iff₀ hpos] at hn
  linarith

lemma tent_levels_core (μ : ℝ) (hμ : 2 < μ) :
    ∀ n : ℕ, ∀ x ∈ tentRepellor μ, ∃ a b : ℝ, a ≤ x ∧ x ≤ b ∧ b - a = (1 / μ) ^ n ∧
      a ∈ tentRepellor μ ∧ b ∈ tentRepellor μ := by
  have hμ0 : 0 < μ := by linarith
  have hhalf : 1 / μ < 1 / 2 := by
    rw [div_lt_div_iff₀ hμ0 (by norm_num)]; linarith
  intro n
  induction n with
  | zero =>
    intro x hx
    have := hx 0
    simp at this
    exact ⟨0, 1, this.1, this.2, by simp, tent_zero_mem_core μ, tent_one_mem_core μ⟩
  | succ n ih =>
    intro x hx
    have hx' := (tent_mem_iff_core μ x).mp hx
    obtain ⟨a', b', ha', hb', hlen, haL, hbL⟩ := ih _ hx'.2
    have hbounds : ∀ z ∈ tentRepellor μ, 0 ≤ z ∧ z ≤ 1 := fun z hz => by
      have := hz 0; simpa using this
    have hpow : (0 : ℝ) ≤ (1 / μ) ^ n := by positivity
    rcases tent_gap_core μ hμ x hx with hI | hI
    · have hTx : tentMap μ x = μ * x := tent_le_half_core μ x (by linarith)
      rw [hTx] at ha' hb'
      refine ⟨a' / μ, b' / μ, ?_, ?_, ?_, ?_, ?_⟩
      · rw [div_le_iff₀ hμ0]; linarith
      · rw [le_div_iff₀ hμ0]; linarith
      · rw [← sub_div, hlen, pow_succ]; field_simp
      · rw [tent_mem_iff_core]
        have ha0 := hbounds a' haL
        refine ⟨⟨div_nonneg ha0.1 hμ0.le, ?_⟩, ?_⟩
        · rw [div_le_iff₀ hμ0]; linarith
        · have : tentMap μ (a' / μ) = a' := by
            rw [tent_le_half_core μ _ ?_]
            · field_simp
            · have : a' / μ ≤ 1 / μ := by
                rw [div_le_div_iff_of_pos_right hμ0]; exact ha0.2
              linarith
          rw [this]; exact haL
      · rw [tent_mem_iff_core]
        have hb0 := hbounds b' hbL
        refine ⟨⟨div_nonneg hb0.1 hμ0.le, ?_⟩, ?_⟩
        · rw [div_le_iff₀ hμ0]; linarith
        · have : tentMap μ (b' / μ) = b' := by
            rw [tent_le_half_core μ _ ?_]
            · field_simp
            · have : b' / μ ≤ 1 / μ := by
                rw [div_le_div_iff_of_pos_right hμ0]; exact hb0.2
              linarith
          rw [this]; exact hbL
    · have hTx : tentMap μ x = μ * (1 - x) := tent_ge_half_core μ x (by linarith)
      rw [hTx] at ha' hb'
      refine ⟨1 - b' / μ, 1 - a' / μ, ?_, ?_, ?_, ?_, ?_⟩
      · have : μ * (1 - x) ≤ b' := hb'
        have : 1 - x ≤ b' / μ := by rw [le_div_iff₀ hμ0]; linarith
        linarith
      · have : a' / μ ≤ 1 - x := by rw [div_le_iff₀ hμ0]; linarith
        linarith
      · have : 1 - a' / μ - (1 - b' / μ) = (b' - a') / μ := by ring
        rw [this, hlen, pow_succ]; field_simp
      · rw [tent_mem_iff_core]
        have hb0 := hbounds b' hbL
        have hle : b' / μ ≤ 1 / μ := by rw [div_le_div_iff_of_pos_right hμ0]; exact hb0.2
        refine ⟨⟨by linarith, by linarith [div_nonneg hb0.1 hμ0.le]⟩, ?_⟩
        have : tentMap μ (1 - b' / μ) = b' := by
          rw [tent_ge_half_core μ _ (by linarith)]; field_simp; ring
        rw [this]; exact hbL
      · rw [tent_mem_iff_core]
        have ha0 := hbounds a' haL
        have hle : a' / μ ≤ 1 / μ := by rw [div_le_div_iff_of_pos_right hμ0]; exact ha0.2
        refine ⟨⟨by linarith, by linarith [div_nonneg ha0.1 hμ0.le]⟩, ?_⟩
        have : tentMap μ (1 - a' / μ) = a' := by
          rw [tent_ge_half_core μ _ (by linarith)]; field_simp; ring
        rw [this]; exact haL

lemma tent_compact_core (μ : ℝ) : IsCompact (tentRepellor μ) := by
  have hcont : Continuous (tentMap μ) := by unfold tentMap; fun_prop
  apply Metric.isCompact_of_isClosed_isBounded
  · have : tentRepellor μ = ⋂ n : ℕ, (tentMap μ)^[n] ⁻¹' Set.Icc 0 1 := by
      ext x; simp [tentRepellor]
    rw [this]
    exact isClosed_iInter fun n => isClosed_Icc.preimage (hcont.iterate n)
  · apply (Metric.isBounded_Icc (0 : ℝ) 1).subset
    intro x hx; simpa using hx 0

lemma tent_preperfect_core (μ : ℝ) (hμ : 2 < μ) : Preperfect (tentRepellor μ) := by
  rw [preperfect_iff_nhds]
  intro x hx U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hμ0 : 0 < μ := by linarith
  have hr : 1 / μ < 1 := by rw [div_lt_one hμ0]; linarith
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hr
  obtain ⟨a, b, hax, hxb, hlen, haL, hbL⟩ := tent_levels_core μ hμ n x hx
  have hpos : 0 < (1 / μ) ^ n := by positivity
  by_cases hxa : a = x
  · refine ⟨b, ⟨hball ?_, hbL⟩, ?_⟩
    · rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith)]; linarith
    · intro h; subst hxa; linarith
  · refine ⟨a, ⟨hball ?_, haL⟩, hxa⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (by linarith)]; linarith

lemma tent_iter_mem_core (μ : ℝ) (x : ℝ) (hx : x ∈ tentRepellor μ) (n : ℕ) :
    (tentMap μ)^[n] x ∈ tentRepellor μ := by
  intro m
  rw [← Function.iterate_add_apply]
  exact hx (m + n)

lemma tent_itin_iff_core (μ : ℝ) (x : ℝ) (hx : x ∈ tentRepellor μ) (n : ℕ) :
    itinerary μ x n = 0 ↔ (tentMap μ)^[n] x ≤ 1 / μ := by
  have h0 := (hx n).1
  unfold itinerary
  constructor
  · intro h
    by_contra hc
    rw [if_neg (fun hm => hc hm.2)] at h
    exact absurd h (by decide)
  · intro h
    rw [if_pos ⟨h0, h⟩]

lemma tent_same_branch_core (μ : ℝ) (hμ : 2 < μ) (x y : ℝ) (hx : x ∈ tentRepellor μ)
    (hy : y ∈ tentRepellor μ) (h : x ≤ 1 / μ ↔ y ≤ 1 / μ) :
    |tentMap μ x - tentMap μ y| = μ * |x - y| := by
  have hμ0 : 0 < μ := by linarith
  have hhalf : 1 / μ < 1 / 2 := by
    rw [div_lt_div_iff₀ hμ0 (by norm_num)]; linarith
  by_cases hxl : x ≤ 1 / μ
  · have hyl := h.mp hxl
    rw [tent_le_half_core μ x (by linarith), tent_le_half_core μ y (by linarith), ← mul_sub,
      abs_mul, abs_of_pos hμ0]
  · have hyl : ¬ y ≤ 1 / μ := fun hh => hxl (h.mpr hh)
    have hx1 := (tent_gap_core μ hμ x hx).resolve_left hxl
    have hy1 := (tent_gap_core μ hμ y hy).resolve_left hyl
    rw [tent_ge_half_core μ x (by linarith), tent_ge_half_core μ y (by linarith),
      show μ * (1 - x) - μ * (1 - y) = μ * (y - x) by ring, abs_mul, abs_of_pos hμ0, abs_sub_comm]

lemma tent_iter_dist_core (μ : ℝ) (hμ : 2 < μ) (x y : ℝ) (hx : x ∈ tentRepellor μ)
    (hy : y ∈ tentRepellor μ) :
    ∀ n : ℕ, (∀ k < n, itinerary μ x k = itinerary μ y k) →
      |(tentMap μ)^[n] x - (tentMap μ)^[n] y| = μ ^ n * |x - y| := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hag
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      tent_same_branch_core μ hμ _ _ (tent_iter_mem_core μ x hx n) (tent_iter_mem_core μ y hy n),
      ih (fun k hk => hag k (by omega)), pow_succ]
    · ring
    · rw [← tent_itin_iff_core μ x hx n, ← tent_itin_iff_core μ y hy n, hag n (by omega)]

lemma tent_agree_bound_core (μ : ℝ) (hμ : 2 < μ) (x y : ℝ) (hx : x ∈ tentRepellor μ)
    (hy : y ∈ tentRepellor μ) (n : ℕ) (hag : ∀ k < n, itinerary μ x k = itinerary μ y k) :
    μ ^ n * |x - y| ≤ 1 := by
  rw [← tent_iter_dist_core μ hμ x y hx hy n hag]
  have h1 := hx n
  have h2 := hy n
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

lemma tent_close_agree_core (μ : ℝ) (hμ : 2 < μ) (x y : ℝ) (hx : x ∈ tentRepellor μ)
    (hy : y ∈ tentRepellor μ) (N : ℕ) (hxy : μ ^ N * |x - y| < 1 - 2 / μ) :
    ∀ k ≤ N, itinerary μ x k = itinerary μ y k := by
  have hμ0 : 0 < μ := by linarith
  have h1 : 1 ≤ μ := by linarith
  have key : ∀ k ≤ N + 1, ∀ j < k, itinerary μ x j = itinerary μ y j := by
    intro k
    induction k with
    | zero => intro _ j hj; omega
    | succ k ih =>
      intro hk j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
      · exact ih (by omega) j hj'
      · subst hj'
        have hd := tent_iter_dist_core μ hμ x y hx hy j (ih (by omega))
        have hle : μ ^ j * |x - y| ≤ μ ^ N * |x - y| :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h1 (by omega)) (abs_nonneg _)
        have hclose : |(tentMap μ)^[j] x - (tentMap μ)^[j] y| < 1 - 2 / μ := by
          rw [hd]; linarith
        have hxj := tent_iter_mem_core μ x hx j
        have hyj := tent_iter_mem_core μ y hy j
        have e : 2 / μ = 2 * (1 / μ) := by ring
        rw [abs_lt] at hclose
        by_cases hxl : (tentMap μ)^[j] x ≤ 1 / μ
        · have : (tentMap μ)^[j] y ≤ 1 / μ := by
            by_contra hc
            have := (tent_gap_core μ hμ _ hyj).resolve_left hc
            linarith [hclose.1]
          rw [(tent_itin_iff_core μ x hx j).mpr hxl, (tent_itin_iff_core μ y hy j).mpr this]
        · have hyl : ¬ (tentMap μ)^[j] y ≤ 1 / μ := by
            intro hc
            have := (tent_gap_core μ hμ _ hxj).resolve_left hxl
            linarith [hclose.2]
          have h1x : itinerary μ x j = 1 := by
            have := (tent_itin_iff_core μ x hx j).not.mpr hxl
            revert this; generalize itinerary μ x j = a; fin_cases a <;> simp
          have h1y : itinerary μ y j = 1 := by
            have := (tent_itin_iff_core μ y hy j).not.mpr hyl
            revert this; generalize itinerary μ y j = a; fin_cases a <;> simp
          rw [h1x, h1y]
  intro k hk
  exact key (k + 1) (by omega) k (by omega)

lemma symDist_term_le_core (s t : ℕ → Fin 2) (n : ℕ) :
    |((s n : ℕ) : ℝ) - ((t n : ℕ) : ℝ)| / (2 : ℝ) ^ n ≤ (1 / 2) ^ n := by
  have : |((s n : ℕ) : ℝ) - ((t n : ℕ) : ℝ)| ≤ 1 := by
    have hs := (s n).isLt
    have ht := (t n).isLt
    rw [abs_le]
    constructor
    · have : ((t n : ℕ) : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp ht
      have : (0 : ℝ) ≤ ((s n : ℕ) : ℝ) := by positivity
      linarith
    · have : ((s n : ℕ) : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp hs
      have : (0 : ℝ) ≤ ((t n : ℕ) : ℝ) := by positivity
      linarith
  rw [div_le_iff₀ (by positivity), one_div_pow, div_mul_cancel₀ _ (by positivity)]
  exact this

lemma symDist_summable_core (s t : ℕ → Fin 2) :
    Summable (fun n : ℕ => |((s n : ℕ) : ℝ) - ((t n : ℕ) : ℝ)| / (2 : ℝ) ^ n) :=
  Summable.of_nonneg_of_le (fun n => by positivity) (symDist_term_le_core s t)
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))

lemma symDist_small_core (s t : ℕ → Fin 2) (N : ℕ) (h : ∀ n < N, s n = t n) :
    symDist 2 s t ≤ 2 * (1 / 2) ^ N := by
  unfold symDist
  push_cast
  rw [← (symDist_summable_core s t).sum_add_tsum_nat_add N]
  have h0 : ∑ i ∈ Finset.range N, |((s i : ℕ) : ℝ) - ((t i : ℕ) : ℝ)| / (2 : ℝ) ^ i = 0 :=
    Finset.sum_eq_zero fun i hi => by rw [h i (Finset.mem_range.mp hi)]; simp
  rw [h0, zero_add]
  have hg : Summable (fun i : ℕ => (1 / 2 : ℝ) ^ (i + N)) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
      (add_left_injective N)
  calc ∑' i, |((s (i + N) : ℕ) : ℝ) - ((t (i + N) : ℕ) : ℝ)| / (2 : ℝ) ^ (i + N)
      ≤ ∑' i : ℕ, (1 / 2 : ℝ) ^ (i + N) :=
        Summable.tsum_le_tsum (fun i => symDist_term_le_core s t (i + N))
          ((symDist_summable_core s t).comp_injective (add_left_injective N)) hg
    _ = 2 * (1 / 2) ^ N := by
        simp_rw [pow_add]
        rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num

lemma symDist_large_core (s t : ℕ → Fin 2) (n : ℕ) (h : s n ≠ t n) :
    (1 / 2 : ℝ) ^ n ≤ symDist 2 s t := by
  unfold symDist
  push_cast
  have hterm : (1 / 2 : ℝ) ^ n = |((s n : ℕ) : ℝ) - ((t n : ℕ) : ℝ)| / (2 : ℝ) ^ n := by
    have : |((s n : ℕ) : ℝ) - ((t n : ℕ) : ℝ)| = 1 := by
      revert h; generalize s n = a; generalize t n = b
      fin_cases a <;> fin_cases b <;> simp
    rw [this, one_div_pow, one_div]
  rw [hterm]
  exact (symDist_summable_core s t).le_tsum n (fun j _ => by positivity)

theorem solution (μ : ℝ) (hμ : 2 < μ) :
    Set.MapsTo (TeschlODE.Shared.tentMap μ) (TeschlODE.Shared.tentRepellor μ) (TeschlODE.Shared.tentRepellor μ) ∧
      Set.BijOn (TeschlODE.Shared.itinerary μ) (TeschlODE.Shared.tentRepellor μ) Set.univ ∧
      (∀ x ∈ TeschlODE.Shared.tentRepellor μ, TeschlODE.Shared.shift (TeschlODE.Shared.itinerary μ x) = TeschlODE.Shared.itinerary μ (TeschlODE.Shared.tentMap μ x)) ∧
      (∀ x ∈ TeschlODE.Shared.tentRepellor μ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ y ∈ TeschlODE.Shared.tentRepellor μ, |y - x| < δ →
          TeschlODE.Shared.symDist 2 (TeschlODE.Shared.itinerary μ y) (TeschlODE.Shared.itinerary μ x) < ε) ∧
      (∀ x ∈ TeschlODE.Shared.tentRepellor μ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ y ∈ TeschlODE.Shared.tentRepellor μ, TeschlODE.Shared.symDist 2 (TeschlODE.Shared.itinerary μ y) (TeschlODE.Shared.itinerary μ x) < δ →
          |y - x| < ε) := by
  have hμ0 : 0 < μ := by linarith
  have hμ1 : 1 < μ := by linarith
  have hgap0 : 0 < 1 - 2 / μ := by
    have : 2 / μ < 1 := by rw [div_lt_one hμ0]; linarith
    linarith
  have hhalf : 1 / μ < 1 / 2 := by
    rw [div_lt_div_iff₀ hμ0 (by norm_num)]; linarith
  have hshift : ∀ x k, itinerary μ x (k + 1) = itinerary μ (tentMap μ x) k := by
    intro x k; unfold itinerary; rw [Function.iterate_succ_apply]
  -- finite words are realized
  have hword : ∀ n : ℕ, ∀ s : ℕ → Fin 2, ∃ x ∈ tentRepellor μ,
      ∀ k < n, itinerary μ x k = s k := by
    intro n
    induction n with
    | zero => intro s; exact ⟨0, tent_zero_mem_core μ, fun k hk => by omega⟩
    | succ n ih =>
      intro s
      obtain ⟨y, hy, hys⟩ := ih (fun k => s (k + 1))
      have hy01 : 0 ≤ y ∧ y ≤ 1 := by have := hy 0; simpa using this
      have hyμ : y / μ ≤ 1 / μ := by rw [div_le_div_iff_of_pos_right hμ0]; exact hy01.2
      have hyμ0 : 0 ≤ y / μ := div_nonneg hy01.1 hμ0.le
      by_cases hs0 : s 0 = 0
      · have hT : tentMap μ (y / μ) = y := by
          rw [tent_le_half_core μ _ (by linarith)]; field_simp
        have hxL : y / μ ∈ tentRepellor μ := by
          rw [tent_mem_iff_core, hT]; exact ⟨⟨hyμ0, by linarith⟩, hy⟩
        refine ⟨y / μ, hxL, fun k hk => ?_⟩
        cases k with
        | zero => rw [hs0]; exact (tent_itin_iff_core μ _ hxL 0).mpr (by simpa using hyμ)
        | succ k => rw [hshift, hT]; exact hys k (by omega)
      · have hT : tentMap μ (1 - y / μ) = y := by
          rw [tent_ge_half_core μ _ (by linarith)]; field_simp; ring
        have hxL : 1 - y / μ ∈ tentRepellor μ := by
          rw [tent_mem_iff_core, hT]; exact ⟨⟨by linarith, by linarith⟩, hy⟩
        refine ⟨1 - y / μ, hxL, fun k hk => ?_⟩
        cases k with
        | zero =>
          have hn : ¬ (1 - y / μ ≤ 1 / μ) := by
            intro h
            have : 1 / μ + 1 / μ < 1 := by linarith
            linarith
          have h1 : itinerary μ (1 - y / μ) 0 ≠ 0 := fun h =>
            hn (by simpa using (tent_itin_iff_core μ _ hxL 0).mp h)
          revert h1 hs0; generalize itinerary μ (1 - y / μ) 0 = a; generalize s 0 = b
          fin_cases a <;> fin_cases b <;> simp
        | succ k => rw [hshift, hT]; exact hys k (by omega)
  refine ⟨fun x hx => ((tent_mem_iff_core μ x).mp hx).2, ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩,
    ?_, ?_, ?_⟩
  · -- injectivity
    intro x hx y hy hxy
    by_contra hne
    have hpos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hne)
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / |x - y|) hμ1
    have := tent_agree_bound_core μ hμ x y hx hy n (fun k _ => congrFun hxy k)
    rw [div_lt_iff₀ hpos] at hn
    linarith
  · -- surjectivity
    intro s _
    choose xs hxsL hxss using fun n => hword n s
    obtain ⟨x, hxL, φ, hφ, hlim⟩ := (tent_compact_core μ).tendsto_subseq hxsL
    refine ⟨x, hxL, funext fun k => ?_⟩
    have hδ : 0 < (1 - 2 / μ) / μ ^ k := by positivity
    obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hlim _ hδ
    set m := max M (k + 1)
    have hm := hM m (le_max_left _ _)
    rw [Real.dist_eq] at hm
    simp only [Function.comp_apply] at hm
    have hclose : μ ^ k * |x - xs (φ m)| < 1 - 2 / μ := by
      rw [abs_sub_comm]
      rw [lt_div_iff₀ (by positivity)] at hm
      linarith
    have hag := tent_close_agree_core μ hμ x (xs (φ m)) hxL (hxsL _) k hclose k le_rfl
    rw [hag]
    have h1 : k + 1 ≤ m := le_max_right _ _
    have h2 : m ≤ φ m := hφ.id_le m
    exact hxss (φ m) k (by omega)
  · -- conjugacy
    intro x _
    funext n
    exact hshift x n
  · -- continuity of the itinerary
    intro x hx ε hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 2 by positivity)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    refine ⟨(1 - 2 / μ) / μ ^ N, by positivity, fun y hy hyx => ?_⟩
    have hclose : μ ^ N * |y - x| < 1 - 2 / μ := by
      rw [lt_div_iff₀ (by positivity)] at hyx; linarith
    have hag := tent_close_agree_core μ hμ y x hy hx N hclose
    have := symDist_small_core (itinerary μ y) (itinerary μ x) N (fun n hn => hag n hn.le)
    linarith
  · -- continuity of the inverse
    intro x hx ε hε
    have hr : 1 / μ < 1 := by rw [div_lt_one hμ0]; linarith
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hr
    refine ⟨(1 / 2) ^ N, by positivity, fun y hy hyx => ?_⟩
    have hag : ∀ k < N, itinerary μ y k = itinerary μ x k := by
      intro k hk
      by_contra hne
      have h1 := symDist_large_core _ _ k hne
      have h2 : (1 / 2 : ℝ) ^ N ≤ (1 / 2) ^ k :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hk.le
      linarith
    have hb := tent_agree_bound_core μ hμ y x hy hx N hag
    have hpow : (1 / μ) ^ N * μ ^ N = 1 := by
      rw [← mul_pow, div_mul_cancel₀ _ hμ0.ne', one_pow]
    have : |y - x| ≤ (1 / μ) ^ N := by
      have hp : 0 < μ ^ N := by positivity
      calc |y - x| = (1 / μ) ^ N * (μ ^ N * |y - x|) := by rw [← mul_assoc, hpow, one_mul]
        _ ≤ (1 / μ) ^ N * 1 := by gcongr
        _ = (1 / μ) ^ N := mul_one _
    linarith

#print axioms solution
