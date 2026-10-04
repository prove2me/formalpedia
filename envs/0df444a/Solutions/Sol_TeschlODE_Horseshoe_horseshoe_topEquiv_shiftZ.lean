-- Prove2me | solution 1 for TeschlODE.Horseshoe.horseshoe_topEquiv_shiftZ
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:10:21.172733+00:00
-- url     : https://prove2.me/submissions/911a6cda-732e-456d-808f-270a0691a355

import Mathlib
import Definitions.Def_TeschlODE_Shared_tentRepellor
import Definitions.Def_TeschlODE_Shared_tentMap
import Definitions.Def_TeschlODE_Shared_itinerary
import Definitions.Def_TeschlODE_Shared_shift
import Definitions.Def_TeschlODE_Shared_symDist
import Definitions.Def_TeschlODE_Horseshoe_IsHorseshoeMap
import Definitions.Def_TeschlODE_Horseshoe_horseshoeSet
import Definitions.Def_TeschlODE_Horseshoe_horseshoeItinerary
import Definitions.Def_TeschlODE_Horseshoe_shiftZ
import Definitions.Def_TeschlODE_Horseshoe_symDistZ
import Definitions.Def_TeschlODE_Horseshoe_IsCantorSet
import Definitions.Def_TeschlODE_Shared_IsChaotic

namespace C5A32A60

lemma one_le_abs_sub {a b : ℕ} (h : a ≠ b) : (1 : ℝ) ≤ |(a : ℝ) - b| := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · have : (a : ℝ) + 1 ≤ b := by exact_mod_cast h
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
  · have : (b : ℝ) + 1 ≤ a := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]; linarith

lemma abs_sub_le_N {N : ℕ} (a b : Fin N) : |((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)| ≤ (N : ℝ) - 1 := by
  have ha' : (a : ℕ) + 1 ≤ N := a.isLt
  have hb' : (b : ℕ) + 1 ≤ N := b.isLt
  have ha : ((a : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast ha'
  have hb : ((b : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast hb'
  have h0a := Nat.cast_nonneg (α := ℝ) (a : ℕ)
  have h0b := Nat.cast_nonneg (α := ℝ) (b : ℕ)
  rw [abs_sub_le_iff]; constructor <;> linarith

end C5A32A60

open TeschlODE.Horseshoe in
theorem symDistZ_agree_core (N : ℕ) (hN : 2 ≤ N) (x y : ℤ → Fin N) (n : ℕ) :
    ((∀ j : ℤ, |j| ≤ n → x j = y j) → symDistZ N x y ≤ 1 / (N : ℝ) ^ n) ∧
      ((∃ j : ℤ, |j| ≤ n ∧ x j ≠ y j) → 1 / (2 * (N : ℝ) ^ n) ≤ symDistZ N x y) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  set r : ℝ := 1 / (N : ℝ) with hrdef
  have hr0 : 0 ≤ r := by rw [hrdef]; positivity
  have hr1 : r < 1 := by rw [hrdef, div_lt_one hNpos]; linarith
  set f : ℕ → ℝ := fun k =>
    (|((x k : ℕ) : ℝ) - ((y k : ℕ) : ℝ)| + |((x (-(k : ℤ)) : ℕ) : ℝ) - ((y (-(k : ℤ)) : ℕ) : ℝ)|) /
      (N : ℝ) ^ k with hf
  have hfnn : ∀ k, 0 ≤ f k := fun k => by rw [hf]; positivity
  have hfb : ∀ k, f k ≤ (2 * ((N : ℝ) - 1)) * r ^ k := by
    intro k
    rw [hf, hrdef]
    simp only
    rw [div_pow, one_pow, ← div_eq_mul_one_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have := C5A32A60.abs_sub_le_N (x k) (y k)
    have := C5A32A60.abs_sub_le_N (x (-(k : ℤ))) (y (-(k : ℤ)))
    linarith
  have hgs : Summable (fun k : ℕ => (2 * ((N : ℝ) - 1)) * r ^ k) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hfs : Summable f := Summable.of_nonneg_of_le hfnn hfb hgs
  have hd : symDistZ N x y = 1 / 2 * ∑' k, f k := rfl
  constructor
  · intro hag
    have hzero : ∀ k, k < n + 1 → f k = 0 := by
      intro k hk
      have hkn : (k : ℤ) ≤ (n : ℤ) := by exact_mod_cast (by omega : k ≤ n)
      have h1 : x k = y k := hag k (by rw [abs_of_nonneg (by positivity)]; exact hkn)
      have h2 : x (-(k : ℤ)) = y (-(k : ℤ)) :=
        hag _ (by rw [abs_neg, abs_of_nonneg (by positivity)]; exact hkn)
      rw [hf]
      simp only
      rw [h1, h2]
      simp
    have hsplit := hfs.sum_add_tsum_nat_add (n + 1)
    have hsum0 : ∑ i ∈ Finset.range (n + 1), f i = 0 :=
      Finset.sum_eq_zero (fun i hi => hzero i (Finset.mem_range.1 hi))
    rw [hsum0, zero_add] at hsplit
    have htail : ∀ i, f (i + (n + 1)) ≤ ((2 * ((N : ℝ) - 1)) * r ^ (n + 1)) * r ^ i := by
      intro i
      calc f (i + (n + 1)) ≤ (2 * ((N : ℝ) - 1)) * r ^ (i + (n + 1)) := hfb _
        _ = ((2 * ((N : ℝ) - 1)) * r ^ (n + 1)) * r ^ i := by rw [pow_add]; ring
    have hts : Summable (fun i => f (i + (n + 1))) := (summable_nat_add_iff (n + 1)).2 hfs
    have hgs2 : Summable (fun i : ℕ => ((2 * ((N : ℝ) - 1)) * r ^ (n + 1)) * r ^ i) :=
      (summable_geometric_of_lt_one hr0 hr1).mul_left _
    have hle := Summable.tsum_le_tsum htail hts hgs2
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1] at hle
    have key : (2 * ((N : ℝ) - 1)) * r ^ (n + 1) * (1 - r)⁻¹ = 2 * (1 / (N : ℝ) ^ n) := by
      have hN1 : (N : ℝ) - 1 ≠ 0 := by linarith
      have hNne : (N : ℝ) ≠ 0 := by linarith
      have hpow : (N : ℝ) ^ n ≠ 0 := pow_ne_zero _ hNne
      rw [hrdef, one_div, inv_pow, pow_succ]
      field_simp
    rw [hd, ← hsplit]
    linarith
  · rintro ⟨j, hj, hne⟩
    obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg j
    · have hk : k ≤ n := by
        rw [abs_of_nonneg (by positivity)] at hj; exact_mod_cast hj
      have hfk : 1 / (N : ℝ) ^ k ≤ f k := by
        rw [hf]
        simp only
        apply div_le_div_of_nonneg_right _ (by positivity)
        have := C5A32A60.one_le_abs_sub (fun h => hne (Fin.ext h))
        have := abs_nonneg (((x (-(k : ℤ)) : ℕ) : ℝ) - ((y (-(k : ℤ)) : ℕ) : ℝ))
        linarith
      have h1 : f k ≤ ∑' i, f i := hfs.le_tsum k (fun i _ => hfnn i)
      have h2 : 1 / (N : ℝ) ^ n ≤ 1 / (N : ℝ) ^ k :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by linarith) hk)
      rw [hd, ← one_div_mul_one_div]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      linarith
    · have hk : k ≤ n := by
        rw [abs_neg, abs_of_nonneg (by positivity)] at hj; exact_mod_cast hj
      have hfk : 1 / (N : ℝ) ^ k ≤ f k := by
        rw [hf]
        simp only
        apply div_le_div_of_nonneg_right _ (by positivity)
        have := C5A32A60.one_le_abs_sub (fun h => hne (Fin.ext h))
        have := abs_nonneg (((x (k : ℤ) : ℕ) : ℝ) - ((y (k : ℤ) : ℕ) : ℝ))
        linarith
      have h1 : f k ≤ ∑' i, f i := hfs.le_tsum k (fun i _ => hfnn i)
      have h2 : 1 / (N : ℝ) ^ n ≤ 1 / (N : ℝ) ^ k :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by linarith) hk)
      rw [hd, ← one_div_mul_one_div]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      linarith

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

lemma tent_inj_core (μ : ℝ) (hμ : 2 < μ) (x y : ℝ) (hx : x ∈ tentRepellor μ)
    (hy : y ∈ tentRepellor μ) (h : itinerary μ x = itinerary μ y) : x = y := by
  have hμ1 : 1 < μ := by linarith
  by_contra hne
  have hpos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / |x - y|) hμ1
  have := tent_agree_bound_core μ hμ x y hx hy n (fun k _ => congrFun h k)
  rw [div_lt_iff₀ hpos] at hn
  linarith

lemma tent_surj_core (μ : ℝ) (hμ : 2 < μ) (s : ℕ → Fin 2) :
    ∃ x ∈ tentRepellor μ, itinerary μ x = s := by
  have hμ0 : 0 < μ := by linarith
  have hgap0 : 0 < 1 - 2 / μ := by
    have : 2 / μ < 1 := by rw [div_lt_one hμ0]; linarith
    linarith
  have hhalf : 1 / μ < 1 / 2 := by
    rw [div_lt_div_iff₀ hμ0 (by norm_num)]; linarith
  have hshift : ∀ x k, itinerary μ x (k + 1) = itinerary μ (tentMap μ x) k := by
    intro x k; unfold itinerary; rw [Function.iterate_succ_apply]
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

section Horseshoe
open TeschlODE.Horseshoe

variable (lam μ : ℝ) (F : ℝ × ℝ → ℝ × ℝ)

lemma hs_F_core (hlam₀ : 0 < lam) (hlam : lam < 1 / 2) (hμ : 2 < μ)
    (hF : IsHorseshoeMap lam μ F) (p : ℝ × ℝ) (hp : p ∈ horseshoeSet lam μ) :
    (F p).2 = tentMap μ p.2 ∧ (F p).1 ∈ tentRepellor (1 / lam) ∧
      tentMap (1 / lam) (F p).1 = p.1 ∧ ((F p).1 ≤ lam ↔ p.2 ≤ 1 / μ) := by
  obtain ⟨hx, hy⟩ := hp
  have hx01 : 0 ≤ p.1 ∧ p.1 ≤ 1 := by have := hx 0; simpa using this
  have hy01 : 0 ≤ p.2 ∧ p.2 ≤ 1 := by have := hy 0; simpa using this
  have hμ0 : 0 < μ := by linarith
  have hhalf : 1 / μ < 1 / 2 := by
    rw [div_lt_div_iff₀ hμ0 (by norm_num)]; linarith
  rcases tent_gap_core μ hμ p.2 hy with hy0 | hy1
  · have hFp : F p = (lam * p.1, μ * p.2) := hF.1 p ⟨⟨hx01.1, hx01.2⟩, ⟨hy01.1, hy0⟩⟩
    have hT : tentMap (1 / lam) (lam * p.1) = p.1 := by
      rw [tent_le_half_core _ _ (by nlinarith)]; field_simp
    rw [hFp]
    refine ⟨(tent_le_half_core μ p.2 (by linarith)).symm, ?_, hT, ?_⟩
    · rw [tent_mem_iff_core, hT]
      exact ⟨⟨mul_nonneg hlam₀.le hx01.1, by nlinarith⟩, hx⟩
    · simp only
      constructor
      · intro _; exact hy0
      · intro _; nlinarith
  · have hgt : ¬ p.2 ≤ 1 / μ := by
      intro h; have : 1 / μ + 1 / μ < 1 := by linarith
      linarith
    have hFp : F p = (1 - lam * p.1, μ * (1 - p.2)) := hF.2 p ⟨⟨hx01.1, hx01.2⟩, ⟨hy1, hy01.2⟩⟩
    have hT : tentMap (1 / lam) (1 - lam * p.1) = p.1 := by
      rw [tent_ge_half_core _ _ (by nlinarith)]; field_simp; ring
    rw [hFp]
    refine ⟨(tent_ge_half_core μ p.2 (by linarith)).symm, ?_, hT, ?_⟩
    · rw [tent_mem_iff_core, hT]
      exact ⟨⟨by nlinarith, by nlinarith⟩, hx⟩
    · simp only
      constructor
      · intro h; nlinarith
      · intro h; exact absurd h hgt

lemma hs_F_mem_core (hlam₀ : 0 < lam) (hlam : lam < 1 / 2) (hμ : 2 < μ)
    (hF : IsHorseshoeMap lam μ F) (p : ℝ × ℝ) (hp : p ∈ horseshoeSet lam μ) :
    F p ∈ horseshoeSet lam μ := by
  obtain ⟨h2, h1, -, -⟩ := hs_F_core lam μ F hlam₀ hlam hμ hF p hp
  refine ⟨h1, ?_⟩
  rw [h2]
  exact ((tent_mem_iff_core μ p.2).mp hp.2).2

lemma hs_inv_core (hlam₀ : 0 < lam) (hlam : lam < 1 / 2) (hμ : 2 < μ)
    (hF : IsHorseshoeMap lam μ F) (q : ℝ × ℝ) (hq : q ∈ horseshoeSet lam μ) :
    horseshoeInv lam μ q ∈ horseshoeSet lam μ ∧
      (horseshoeInv lam μ q).1 = tentMap (1 / lam) q.1 ∧ F (horseshoeInv lam μ q) = q := by
  obtain ⟨hu, hv⟩ := hq
  have hν : 2 < 1 / lam := by
    rw [lt_div_iff₀ hlam₀]; linarith
  have hu01 : 0 ≤ q.1 ∧ q.1 ≤ 1 := by have := hu 0; simpa using this
  have hv01 : 0 ≤ q.2 ∧ q.2 ≤ 1 := by have := hv 0; simpa using this
  have hμ0 : 0 < μ := by linarith
  have hvμ : q.2 / μ ≤ 1 / μ := by rw [div_le_div_iff_of_pos_right hμ0]; exact hv01.2
  have hvμ0 : 0 ≤ q.2 / μ := div_nonneg hv01.1 hμ0.le
  have hhalf : 1 / μ < 1 / 2 := by
    rw [div_lt_div_iff₀ hμ0 (by norm_num)]; linarith
  by_cases hul : q.1 ≤ lam
  · have hinv : horseshoeInv lam μ q = (lam⁻¹ * q.1, μ⁻¹ * q.2) := by
      simp [horseshoeInv, hul]
    have hT1 : tentMap (1 / lam) q.1 = lam⁻¹ * q.1 := by
      rw [tent_le_half_core _ _ (by linarith)]; ring
    have hy : μ⁻¹ * q.2 ∈ tentRepellor μ := by
      rw [tent_mem_iff_core]
      refine ⟨⟨mul_nonneg (inv_nonneg.mpr hμ0.le) hv01.1, ?_⟩, ?_⟩
      · rw [← div_eq_inv_mul]; linarith
      · rw [tent_le_half_core μ _ ?_]
        · field_simp; exact hv
        · rw [← div_eq_inv_mul]; linarith
    refine ⟨?_, by rw [hinv, hT1], ?_⟩
    · rw [hinv]
      refine ⟨?_, hy⟩
      rw [← hT1]; exact ((tent_mem_iff_core _ q.1).mp hu).2
    · rw [hinv, hF.1 _ ⟨⟨mul_nonneg (inv_nonneg.mpr hlam₀.le) hu01.1, ?_⟩,
        ⟨mul_nonneg (inv_nonneg.mpr hμ0.le) hv01.1, ?_⟩⟩]
      · ext <;> simp <;> field_simp
      · rw [← div_eq_inv_mul, div_le_one hlam₀]; exact hul
      · show μ⁻¹ * q.2 ≤ 1 / μ
        rw [← div_eq_inv_mul]; exact hvμ
  · have hu1 := (tent_gap_core (1 / lam) hν q.1 hu).resolve_left (by
      rw [one_div_one_div]; exact hul)
    rw [one_div_one_div] at hu1
    have hinv : horseshoeInv lam μ q = (lam⁻¹ * (1 - q.1), 1 - μ⁻¹ * q.2) := by
      simp [horseshoeInv, hul]
    have hT1 : tentMap (1 / lam) q.1 = lam⁻¹ * (1 - q.1) := by
      rw [tent_ge_half_core _ _ (by linarith)]; ring
    have hy : 1 - μ⁻¹ * q.2 ∈ tentRepellor μ := by
      rw [tent_mem_iff_core]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [← div_eq_inv_mul]; linarith
      · have : 0 ≤ μ⁻¹ * q.2 := mul_nonneg (inv_nonneg.mpr hμ0.le) hv01.1
        linarith
      · rw [tent_ge_half_core μ _ ?_]
        · field_simp; ring_nf; exact hv
        · rw [← div_eq_inv_mul]; linarith
    refine ⟨?_, by rw [hinv, hT1], ?_⟩
    · rw [hinv]
      refine ⟨?_, hy⟩
      rw [← hT1]; exact ((tent_mem_iff_core _ q.1).mp hu).2
    · have h1 : 0 ≤ lam⁻¹ * (1 - q.1) := by
        have : 0 ≤ 1 - q.1 := by linarith
        positivity
      have h2 : lam⁻¹ * (1 - q.1) ≤ 1 := by
        rw [← div_eq_inv_mul, div_le_one hlam₀]; linarith
      have h3 : 1 - 1 / μ ≤ 1 - μ⁻¹ * q.2 := by rw [← div_eq_inv_mul]; linarith
      have h4 : 1 - μ⁻¹ * q.2 ≤ 1 := by
        have : 0 ≤ μ⁻¹ * q.2 := mul_nonneg (inv_nonneg.mpr hμ0.le) hv01.1
        linarith
      rw [hinv, hF.2 _ ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩]
      ext <;> simp <;> field_simp <;> ring

lemma hs_iterF_core (hlam₀ : 0 < lam) (hlam : lam < 1 / 2) (hμ : 2 < μ)
    (hF : IsHorseshoeMap lam μ F) :
    ∀ k : ℕ, ∀ p ∈ horseshoeSet lam μ,
      F^[k] p ∈ horseshoeSet lam μ ∧ (F^[k] p).2 = (tentMap μ)^[k] p.2 := by
  intro k
  induction k with
  | zero => intro p hp; exact ⟨hp, rfl⟩
  | succ k ih =>
    intro p hp
    obtain ⟨hm, he⟩ := ih p hp
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    refine ⟨hs_F_mem_core lam μ F hlam₀ hlam hμ hF _ hm, ?_⟩
    rw [(hs_F_core lam μ F hlam₀ hlam hμ hF _ hm).1, he]

lemma hs_iterInv_core (hlam₀ : 0 < lam) (hlam : lam < 1 / 2) (hμ : 2 < μ)
    (hF : IsHorseshoeMap lam μ F) :
    ∀ k : ℕ, ∀ q ∈ horseshoeSet lam μ, (horseshoeInv lam μ)^[k] q ∈ horseshoeSet lam μ ∧
      ((horseshoeInv lam μ)^[k] q).1 = (tentMap (1 / lam))^[k] q.1 := by
  intro k
  induction k with
  | zero => intro q hq; exact ⟨hq, rfl⟩
  | succ k ih =>
    intro q hq
    obtain ⟨hm, he⟩ := ih q hq
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    obtain ⟨h1, h2, -⟩ := hs_inv_core lam μ F hlam₀ hlam hμ hF _ hm
    exact ⟨h1, by rw [h2, he]⟩

lemma hs_itin_pos_core (hlam₀ : 0 < lam) (hlam : lam < 1 / 2) (hμ : 2 < μ)
    (hF : IsHorseshoeMap lam μ F) (p : ℝ × ℝ) (hp : p ∈ horseshoeSet lam μ) (k : ℕ) :
    horseshoeItinerary lam μ F p (k : ℤ) = itinerary μ p.2 k := by
  obtain ⟨hm, he⟩ := hs_iterF_core lam μ F hlam₀ hlam hμ hF k p hp
  have h01 : 0 ≤ (F^[k] p).1 ∧ (F^[k] p).1 ≤ 1 := by have := hm.1 0; simpa using this
  simp only [horseshoeItinerary, Nat.cast_nonneg, if_true, Int.toNat_natCast, itinerary]
  rw [← he]
  congr 1
  apply propext
  simp only [Set.mem_prod, Set.mem_Icc]
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨h01, h⟩

lemma hs_itin_neg_core (hlam₀ : 0 < lam) (hlam : lam < 1 / 2) (hμ : 2 < μ)
    (hF : IsHorseshoeMap lam μ F) (p : ℝ × ℝ) (hp : p ∈ horseshoeSet lam μ) (k : ℕ) :
    horseshoeItinerary lam μ F p (Int.negSucc k) = itinerary (1 / lam) p.1 k := by
  obtain ⟨hm, he⟩ := hs_iterInv_core lam μ F hlam₀ hlam hμ hF k p hp
  have h01 : 0 ≤ ((horseshoeInv lam μ)^[k] p).2 ∧ ((horseshoeInv lam μ)^[k] p).2 ≤ 1 := by
    have := hm.2 0; simpa using this
  have hneg : ¬ (0 ≤ Int.negSucc k) := by simp [Int.negSucc_lt_zero]
  have htn : (-Int.negSucc k - 1).toNat = k := by omega
  simp only [horseshoeItinerary, hneg, if_false, htn, itinerary]
  rw [← he, one_div_one_div]
  congr 1
  apply propext
  simp only [Set.mem_prod, Set.mem_Icc]
  constructor
  · intro h; exact h.1
  · intro h; exact ⟨h, h01⟩

end Horseshoe

open TeschlODE.Horseshoe in
theorem solution (lam μ : ℝ) (hlam₀ : 0 < lam) (hlam : lam < 1 / 2)
    (hμ : 2 < μ) (F : ℝ × ℝ → ℝ × ℝ) (hF : IsHorseshoeMap lam μ F) :
    IsCantorSet (horseshoeSet lam μ) ∧
      F '' horseshoeSet lam μ = horseshoeSet lam μ ∧
      Set.BijOn (horseshoeItinerary lam μ F) (horseshoeSet lam μ) Set.univ ∧
      (∀ p ∈ horseshoeSet lam μ,
        shiftZ (horseshoeItinerary lam μ F p) = horseshoeItinerary lam μ F (F p)) ∧
      (∀ p ∈ horseshoeSet lam μ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ q ∈ horseshoeSet lam μ, dist q p < δ →
          symDistZ 2 (horseshoeItinerary lam μ F q) (horseshoeItinerary lam μ F p) < ε) ∧
      (∀ p ∈ horseshoeSet lam μ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ q ∈ horseshoeSet lam μ,
          symDistZ 2 (horseshoeItinerary lam μ F q) (horseshoeItinerary lam μ F p) < δ →
            dist q p < ε) ∧
      ∃ h : Set.MapsTo F (horseshoeSet lam μ) (horseshoeSet lam μ),
        TeschlODE.Shared.IsChaotic (h.restrict F (horseshoeSet lam μ) (horseshoeSet lam μ)) := by
  have hν : 2 < (1 / lam) := by rw [lt_div_iff₀ hlam₀]; linarith
  have hμ0 : 0 < μ := by linarith
  have hν0 : 0 < (1 / lam) := by linarith
  have hνinv : 1 / (1 / lam) = lam := by rw [one_div_one_div]
  have hpos := hs_itin_pos_core lam μ F hlam₀ hlam hμ hF
  have hneg := hs_itin_neg_core lam μ F hlam₀ hlam hμ hF
  have hFc := hs_F_core lam μ F hlam₀ hlam hμ hF
  have hFm := hs_F_mem_core lam μ F hlam₀ hlam hμ hF
  have hinv := hs_inv_core lam μ F hlam₀ hlam hμ hF
  have habsneg : ∀ k : ℕ, |Int.negSucc k| = (k : ℤ) + 1 := by
    intro k; rw [Int.negSucc_eq, abs_neg, abs_of_nonneg (by positivity)]
  have hshift : ∀ (c : ℝ) x k, itinerary c x (k + 1) = itinerary c (tentMap c x) k := by
    intro c x k; unfold itinerary; rw [Function.iterate_succ_apply]
  -- gaps in the two factors
  have hsep : ∀ c : ℝ, 2 < c → ∀ a ∈ tentRepellor c, ∀ b ∈ tentRepellor c, a < b →
      ∃ z, a < z ∧ z < b ∧ z ∉ tentRepellor c := by
    intro c hc a ha b hb hab
    obtain ⟨z, hz, hzn⟩ := Set.not_subset.mp (tent_exists_gap_core c hc a b hab)
    exact ⟨z, lt_of_le_of_ne hz.1 (by rintro rfl; exact hzn ha),
      lt_of_le_of_ne hz.2 (by rintro rfl; exact hzn hb), hzn⟩
  -- injectivity / surjectivity of the itinerary
  have hinj : Set.InjOn (horseshoeItinerary lam μ F) (horseshoeSet lam μ) := by
    intro p hp q hq hpq
    have h2 : p.2 = q.2 := tent_inj_core μ hμ p.2 q.2 hp.2 hq.2 (funext fun k => by
      rw [← hpos p hp k, ← hpos q hq k, hpq])
    have h1 : p.1 = q.1 := tent_inj_core (1 / lam) hν p.1 q.1 hp.1 hq.1 (funext fun k => by
      rw [← hneg p hp k, ← hneg q hq k, hpq])
    exact Prod.ext h1 h2
  have hsurj : ∀ s : ℤ → Fin 2, ∃ p ∈ (horseshoeSet lam μ), (horseshoeItinerary lam μ F) p = s := by
    intro s
    obtain ⟨y, hy, hys⟩ := tent_surj_core μ hμ (fun k => s k)
    obtain ⟨x, hx, hxs⟩ := tent_surj_core (1 / lam) hν (fun k => s (Int.negSucc k))
    refine ⟨(x, y), ⟨hx, hy⟩, funext fun n => ?_⟩
    rcases n with k | k
    · rw [Int.ofNat_eq_coe, hpos (x, y) ⟨hx, hy⟩ k]; simp [hys]
    · rw [hneg (x, y) ⟨hx, hy⟩ k]; exact congrFun hxs k
  -- conjugacy
  have hconj : ∀ p ∈ (horseshoeSet lam μ), shiftZ ((horseshoeItinerary lam μ F) p) = (horseshoeItinerary lam μ F) (F p) := by
    intro p hp
    have hFp := hFm p hp
    obtain ⟨h2, h1m, h1T, hiff⟩ := hFc p hp
    funext n
    simp only [shiftZ]
    rcases n with k | k
    · rw [Int.ofNat_eq_coe, show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by push_cast; ring,
        hpos p hp, hpos (F p) hFp, hshift, h2]
    · rcases k with _ | k
      · rw [show Int.negSucc 0 + 1 = ((0 : ℕ) : ℤ) by rfl, hpos p hp, hneg (F p) hFp]
        have e1 := tent_itin_iff_core μ p.2 hp.2 0
        have e2 := tent_itin_iff_core (1 / lam) (F p).1 h1m 0
        simp only [Function.iterate_zero, id] at e1 e2
        rw [hνinv] at e2
        have : itinerary μ p.2 0 = 0 ↔ itinerary (1 / lam) (F p).1 0 = 0 := by
          rw [e1, e2, hiff]
        revert this
        generalize itinerary μ p.2 0 = a; generalize itinerary (1 / lam) (F p).1 0 = b
        fin_cases a <;> fin_cases b <;> simp
      · rw [show Int.negSucc (k + 1) + 1 = Int.negSucc k by omega, hneg p hp,
          hneg (F p) hFp, hshift, h1T]
  -- closeness from agreement of itineraries
  have hclose : ∀ p ∈ (horseshoeSet lam μ), ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ q ∈ (horseshoeSet lam μ),
      (∀ j : ℤ, |j| ≤ N → (horseshoeItinerary lam μ F) q j = (horseshoeItinerary lam μ F) p j) → dist q p < ε := by
    intro p hp ε hε
    have hr1 : 1 / μ < 1 := by rw [div_lt_one hμ0]; linarith
    have hr2 : 1 / (1 / lam) < 1 := by rw [div_lt_one hν0]; linarith
    obtain ⟨N1, hN1⟩ := exists_pow_lt_of_lt_one hε hr1
    obtain ⟨N2, hN2⟩ := exists_pow_lt_of_lt_one hε hr2
    refine ⟨max N1 N2, fun q hq hag => ?_⟩
    set N := max N1 N2
    have hagy : ∀ k < N, itinerary μ q.2 k = itinerary μ p.2 k := by
      intro k hk
      rw [← hpos q hq, ← hpos p hp]
      exact hag k (by rw [abs_of_nonneg (by positivity)]; exact_mod_cast hk.le)
    have hagx : ∀ k < N, itinerary (1 / lam) q.1 k = itinerary (1 / lam) p.1 k := by
      intro k hk
      rw [← hneg q hq, ← hneg p hp]
      apply hag
      rw [habsneg]; push_cast; exact_mod_cast hk
    have bound : ∀ c : ℝ, 2 < c → ∀ a ∈ tentRepellor c, ∀ b ∈ tentRepellor c,
        (∀ k < N, itinerary c a k = itinerary c b k) → |a - b| ≤ (1 / c) ^ N := by
      intro c hc a ha b hb hab
      have hc0 : 0 < c := by linarith
      have hb' := tent_agree_bound_core c hc a b ha hb N hab
      have hpow : (1 / c) ^ N * c ^ N = 1 := by
        rw [← mul_pow, div_mul_cancel₀ _ hc0.ne', one_pow]
      calc |a - b| = (1 / c) ^ N * (c ^ N * |a - b|) := by rw [← mul_assoc, hpow, one_mul]
        _ ≤ (1 / c) ^ N * 1 := by gcongr
        _ = (1 / c) ^ N := mul_one _
    have hy := bound μ hμ q.2 hq.2 p.2 hp.2 hagy
    have hx := bound (1 / lam) hν q.1 hq.1 p.1 hp.1 hagx
    have hm1 : (1 / μ) ^ N ≤ (1 / μ) ^ N1 :=
      pow_le_pow_of_le_one (by positivity) hr1.le (le_max_left _ _)
    have hm2 : (1 / (1 / lam)) ^ N ≤ (1 / (1 / lam)) ^ N2 :=
      pow_le_pow_of_le_one (by positivity) hr2.le (le_max_right _ _)
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
    constructor <;> linarith
  -- shift iterates
  have hshiftk : ∀ (k : ℕ) (s : ℤ → Fin 2) (j : ℤ), (shiftZ^[k] s) j = s (j + k) := by
    intro k
    induction k with
    | zero => intro s j; simp
    | succ k ih =>
      intro s j
      rw [Function.iterate_succ_apply', shiftZ, ih]
      congr 1; push_cast; ring
  have hconjk : ∀ (k : ℕ), ∀ p ∈ (horseshoeSet lam μ), (horseshoeItinerary lam μ F) (F^[k] p) = shiftZ^[k] ((horseshoeItinerary lam μ F) p) ∧ F^[k] p ∈ (horseshoeSet lam μ) := by
    intro k
    induction k with
    | zero => intro p hp; exact ⟨rfl, hp⟩
    | succ k ih =>
      intro p hp
      obtain ⟨h1, h2⟩ := ih p hp
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← hconj _ h2, h1]
      exact ⟨rfl, hFm _ h2⟩
  have hmaps : Set.MapsTo F (horseshoeSet lam μ) (horseshoeSet lam μ) := fun p hp => hFm p hp
  refine ⟨⟨(tent_compact_core (1 / lam)).prod (tent_compact_core μ), ?_, ?_⟩, ?_,
    ⟨fun _ _ => Set.mem_univ _, hinj, fun s _ => hsurj s⟩, hconj, ?_, ?_, hmaps, ?_⟩
  · -- totally separated
    intro p hp q hq hne
    by_cases h1 : p.1 = q.1
    · have h2 : p.2 ≠ q.2 := fun h => hne (Prod.ext h1 h)
      rcases lt_or_gt_of_ne h2 with hlt | hlt
      · obtain ⟨z, hz1, hz2, hzn⟩ := hsep μ hμ p.2 hp.2 q.2 hq.2 hlt
        refine ⟨{w | w.2 < z}, {w | z < w.2}, isOpen_lt continuous_snd continuous_const,
          isOpen_lt continuous_const continuous_snd, hz1, hz2, fun w hw => ?_,
          Set.disjoint_left.mpr fun w (h1 : w.2 < z) (h2 : z < w.2) => lt_asymm h1 h2⟩
        rcases lt_trichotomy w.2 z with h | h | h
        · exact Or.inl h
        · exact absurd (h ▸ hw.2) hzn
        · exact Or.inr h
      · obtain ⟨z, hz1, hz2, hzn⟩ := hsep μ hμ q.2 hq.2 p.2 hp.2 hlt
        refine ⟨{w | z < w.2}, {w | w.2 < z}, isOpen_lt continuous_const continuous_snd,
          isOpen_lt continuous_snd continuous_const, hz2, hz1, fun w hw => ?_,
          Set.disjoint_left.mpr fun w (h1 : z < w.2) (h2 : w.2 < z) => lt_asymm h1 h2⟩
        rcases lt_trichotomy w.2 z with h | h | h
        · exact Or.inr h
        · exact absurd (h ▸ hw.2) hzn
        · exact Or.inl h
    · rcases lt_or_gt_of_ne h1 with hlt | hlt
      · obtain ⟨z, hz1, hz2, hzn⟩ := hsep (1 / lam) hν p.1 hp.1 q.1 hq.1 hlt
        refine ⟨{w | w.1 < z}, {w | z < w.1}, isOpen_lt continuous_fst continuous_const,
          isOpen_lt continuous_const continuous_fst, hz1, hz2, fun w hw => ?_,
          Set.disjoint_left.mpr fun w (h1 : w.1 < z) (h2 : z < w.1) => lt_asymm h1 h2⟩
        rcases lt_trichotomy w.1 z with h | h | h
        · exact Or.inl h
        · exact absurd (h ▸ hw.1) hzn
        · exact Or.inr h
      · obtain ⟨z, hz1, hz2, hzn⟩ := hsep (1 / lam) hν q.1 hq.1 p.1 hp.1 hlt
        refine ⟨{w | z < w.1}, {w | w.1 < z}, isOpen_lt continuous_const continuous_fst,
          isOpen_lt continuous_fst continuous_const, hz2, hz1, fun w hw => ?_,
          Set.disjoint_left.mpr fun w (h1 : z < w.1) (h2 : w.1 < z) => lt_asymm h1 h2⟩
        rcases lt_trichotomy w.1 z with h | h | h
        · exact Or.inr h
        · exact absurd (h ▸ hw.1) hzn
        · exact Or.inl h
  · -- perfect
    rw [preperfect_iff_nhds]
    intro p hp U hU
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
    obtain ⟨y', ⟨hy'b, hy'B⟩, hy'ne⟩ := (preperfect_iff_nhds.mp (tent_preperfect_core μ hμ))
      p.2 hp.2 (Metric.ball p.2 ε) (Metric.ball_mem_nhds _ hε)
    refine ⟨(p.1, y'), ⟨hball ?_, hp.1, hy'B⟩, fun h => hy'ne (congrArg Prod.snd h)⟩
    rw [Metric.mem_ball, Prod.dist_eq, dist_self, max_lt_iff]
    exact ⟨hε, hy'b⟩
  · -- `F` maps `(horseshoeSet lam μ)` onto itself
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩; exact hFm p hp
    · intro hq
      obtain ⟨h1, -, h3⟩ := hinv q hq
      exact ⟨_, h1, h3⟩
  · -- continuity of the itinerary
    intro p hp ε hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (show (1 / 2 : ℝ) < 1 by norm_num)
    have hδ1 : 0 < (1 - 2 / μ) / μ ^ N := by
      have : 2 / μ < 1 := by rw [div_lt_one hμ0]; linarith
      exact div_pos (by linarith) (by positivity)
    have hδ2 : 0 < (1 - 2 / (1 / lam)) / (1 / lam) ^ N := by
      have : 2 / (1 / lam) < 1 := by rw [div_lt_one hν0]; linarith
      exact div_pos (by linarith) (by positivity)
    refine ⟨min ((1 - 2 / μ) / μ ^ N) ((1 - 2 / (1 / lam)) / (1 / lam) ^ N), lt_min hδ1 hδ2,
      fun q hq hqp => ?_⟩
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff, lt_min_iff, lt_min_iff] at hqp
    have hagy := tent_close_agree_core μ hμ q.2 p.2 hq.2 hp.2 N (by
      have := (lt_div_iff₀ (by positivity)).mp hqp.2.1; linarith [mul_comm (μ ^ N) |q.2 - p.2|])
    have hagx := tent_close_agree_core (1 / lam) hν q.1 p.1 hq.1 hp.1 N (by
      have := (lt_div_iff₀ (by positivity)).mp hqp.1.2
      linarith [mul_comm ((1 / lam) ^ N) |q.1 - p.1|])
    have hag : ∀ j : ℤ, |j| ≤ N → (horseshoeItinerary lam μ F) q j = (horseshoeItinerary lam μ F) p j := by
      intro j hj
      rcases j with k | k
      · rw [Int.ofNat_eq_coe, hpos q hq, hpos p hp]
        apply hagy
        rw [Int.ofNat_eq_coe, abs_of_nonneg (by positivity)] at hj; exact_mod_cast hj
      · rw [hneg q hq, hneg p hp]
        apply hagx
        rw [habsneg] at hj; push_cast at hj; omega
    have := (symDistZ_agree_core 2 le_rfl ((horseshoeItinerary lam μ F) q) ((horseshoeItinerary lam μ F) p) N).1 hag
    have e : (1 : ℝ) / ((2 : ℕ) : ℝ) ^ N = (1 / 2) ^ N := by push_cast; rw [one_div_pow]
    rw [e] at this
    linarith
  · -- continuity of the inverse
    intro p hp ε hε
    obtain ⟨N, hN⟩ := hclose p hp ε hε
    refine ⟨1 / (2 * (2 : ℝ) ^ N), by positivity, fun q hq hqp => hN q hq fun j hj => ?_⟩
    by_contra hne
    have := (symDistZ_agree_core 2 le_rfl ((horseshoeItinerary lam μ F) q) ((horseshoeItinerary lam μ F) p) N).2 ⟨j, hj, hne⟩
    push_cast at this
    linarith
  · -- chaos
    set g := hmaps.restrict F (horseshoeSet lam μ) (horseshoeSet lam μ) with hg
    have hgk : ∀ (k : ℕ) (w : (horseshoeSet lam μ)), ((g^[k] w : (horseshoeSet lam μ)) : ℝ × ℝ) = F^[k] w := by
      intro k w
      rw [hg, Set.MapsTo.iterate_restrict]
      rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- continuity
      have hcont : ContinuousOn F (horseshoeSet lam μ) := by
        intro p hp
        have hhalf : 1 / μ < 1 / 2 := by
          rw [div_lt_div_iff₀ hμ0 (by norm_num)]; linarith
        have hx01 : ∀ w ∈ (horseshoeSet lam μ), 0 ≤ w.1 ∧ w.1 ≤ 1 := fun w hw => by
          have := hw.1 0; simpa using this
        have hy01 : ∀ w ∈ (horseshoeSet lam μ), 0 ≤ w.2 ∧ w.2 ≤ 1 := fun w hw => by
          have := hw.2 0; simpa using this
        rcases tent_gap_core μ hμ p.2 hp.2 with hp0 | hp1
        · have hev : F =ᶠ[nhdsWithin p (horseshoeSet lam μ)] fun w => (lam * w.1, μ * w.2) := by
            have hopen : {w : ℝ × ℝ | w.2 < 1 / 2} ∈ nhds p :=
              (isOpen_lt continuous_snd continuous_const).mem_nhds (by
                show p.2 < 1 / 2; linarith)
            filter_upwards [inter_mem_nhdsWithin (horseshoeSet lam μ) hopen] with w hw
            have hw0 : w.2 ≤ 1 / μ := by
              rcases tent_gap_core μ hμ w.2 hw.1.2 with h | h
              · exact h
              · exfalso; have : (1 : ℝ) / 2 < 1 - 1 / μ := by linarith
                exact absurd hw.2 (by simp only [Set.mem_setOf_eq]; linarith)
            exact hF.1 w ⟨hx01 w hw.1, ⟨(hy01 w hw.1).1, hw0⟩⟩
          exact (Continuous.continuousWithinAt (by fun_prop)).congr_of_eventuallyEq hev
            (hev.self_of_nhdsWithin hp)
        · have hev : F =ᶠ[nhdsWithin p (horseshoeSet lam μ)] fun w => (1 - lam * w.1, μ * (1 - w.2)) := by
            have hopen : {w : ℝ × ℝ | 1 / 2 < w.2} ∈ nhds p :=
              (isOpen_lt continuous_const continuous_snd).mem_nhds (by
                show 1 / 2 < p.2; linarith)
            filter_upwards [inter_mem_nhdsWithin (horseshoeSet lam μ) hopen] with w hw
            have hw1 : 1 - 1 / μ ≤ w.2 := by
              rcases tent_gap_core μ hμ w.2 hw.1.2 with h | h
              · exfalso
                exact absurd hw.2 (by simp only [Set.mem_setOf_eq]; linarith)
              · exact h
            exact hF.2 w ⟨hx01 w hw.1, ⟨hw1, (hy01 w hw.1).2⟩⟩
          exact (Continuous.continuousWithinAt (by fun_prop)).congr_of_eventuallyEq hev
            (hev.self_of_nhdsWithin hp)
      apply continuous_induced_rng.2
      have : (Subtype.val ∘ g) = (horseshoeSet lam μ).restrict F := by funext w; rfl
      rw [this]
      exact hcont.restrict
    · -- infinite
      have hinfZ : Infinite (ℤ → Fin 2) := by
        refine Infinite.of_injective (fun n : ℕ => fun j : ℤ => if j = n then (1 : Fin 2) else 0)
          (fun a b hab => ?_)
        have := congrFun hab (a : ℤ)
        by_contra hne
        simp [hne] at this
      exact Infinite.of_surjective (fun w : (horseshoeSet lam μ) => (horseshoeItinerary lam μ F) w) (fun s => by
        obtain ⟨p, hp, hps⟩ := hsurj s
        exact ⟨⟨p, hp⟩, hps⟩)
    · -- transitive
      intro U V hU hV hUne hVne
      obtain ⟨⟨p, hp⟩, hpU⟩ := hUne
      obtain ⟨⟨q, hq⟩, hqV⟩ := hVne
      obtain ⟨U', hU'o, hU'⟩ := isOpen_induced_iff.mp hU
      obtain ⟨V', hV'o, hV'⟩ := isOpen_induced_iff.mp hV
      have hpU' : p ∈ U' := by rw [← hU'] at hpU; exact hpU
      have hqV' : q ∈ V' := by rw [← hV'] at hqV; exact hqV
      obtain ⟨εU, hεU, hbU⟩ := Metric.isOpen_iff.mp hU'o p hpU'
      obtain ⟨εV, hεV, hbV⟩ := Metric.isOpen_iff.mp hV'o q hqV'
      obtain ⟨N1, hN1⟩ := hclose p hp εU hεU
      obtain ⟨N2, hN2⟩ := hclose q hq εV hεV
      set N := max N1 N2
      set M : ℕ := 2 * N + 1
      obtain ⟨r, hr, hrs⟩ := hsurj (fun j => if j ≤ N then (horseshoeItinerary lam μ F) p j else (horseshoeItinerary lam μ F) q (j - M))
      have hrU : (⟨r, hr⟩ : (horseshoeSet lam μ)) ∈ U := by
        rw [← hU']
        apply hbU
        rw [Metric.mem_ball]
        apply hN1 r hr
        intro j hj
        rw [hrs]
        have : j ≤ (N : ℤ) := by
          have := le_abs_self j
          have : (N1 : ℤ) ≤ N := by exact_mod_cast le_max_left N1 N2
          linarith
        simp [this]
      refine ⟨M, by omega, g^[M] ⟨r, hr⟩, ⟨⟨r, hr⟩, hrU, rfl⟩, ?_⟩
      rw [← hV']
      show ((g^[M] ⟨r, hr⟩ : (horseshoeSet lam μ)) : ℝ × ℝ) ∈ V'
      rw [hgk]
      apply hbV
      rw [Metric.mem_ball]
      obtain ⟨hk1, hk2⟩ := hconjk M r hr
      apply hN2 _ hk2
      intro j hj
      rw [hk1, hshiftk, hrs]
      have hN2N : (N2 : ℤ) ≤ N := by exact_mod_cast le_max_right N1 N2
      have hjl : -(N : ℤ) ≤ j := by
        have := neg_abs_le j
        linarith
      have : ¬ (j + (M : ℤ) ≤ N) := by
        push_cast [M]; omega
      simp only [this, if_false]
      congr 1; ring
    · -- dense periodic points
      rw [Metric.dense_iff]
      rintro ⟨p, hp⟩ ε hε
      obtain ⟨N, hN⟩ := hclose p hp ε hε
      set M : ℕ := 2 * N + 1
      set s : ℤ → Fin 2 := fun j => (horseshoeItinerary lam μ F) p ((j + N) % (M : ℤ) - N) with hs
      obtain ⟨r, hr, hrs⟩ := hsurj s
      have hper : s = shiftZ^[M] s := by
        funext j
        rw [hshiftk]
        simp only [hs]
        congr 2
        rw [show j + (M : ℤ) + N = (j + N) + M by ring, ← Int.emod_eq_add_self_emod]
      have hfix : F^[M] r = r := by
        obtain ⟨hk1, hk2⟩ := hconjk M r hr
        apply hinj hk2 hr
        rw [hk1, hrs, ← hper]
      refine ⟨⟨r, hr⟩, ?_, Function.mk_mem_periodicPts (n := M) (by omega) ?_⟩
      · rw [Metric.mem_ball, Subtype.dist_eq]
        apply hN r hr
        intro j hj
        rw [hrs]
        simp only [hs]
        congr 1
        have h1 : 0 ≤ j + N := by have := neg_abs_le j; linarith
        have h2 : j + N < M := by
          have := le_abs_self j
          push_cast [M]; linarith
        rw [Int.emod_eq_of_lt h1 h2]; ring
      · apply Subtype.ext
        rw [hgk]
        exact hfix

#print axioms solution
