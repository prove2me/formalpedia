-- Prove2me | solution 1 for TeschlODE.Horseshoe.tentSet_isCantorSet
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:53:42.605325+00:00
-- url     : https://prove2.me/submissions/28cfffd2-6592-40ba-af04-7e431416c881

import Mathlib
import Definitions.Def_TeschlODE_Shared_tentRepellor
import Definitions.Def_TeschlODE_Horseshoe_IsCantorSet

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

theorem solution (μ : ℝ) (hμ : 2 < μ) :
    TeschlODE.Horseshoe.IsCantorSet (TeschlODE.Shared.tentRepellor μ) := by
  refine ⟨tent_compact_core μ, ?_, tent_preperfect_core μ hμ⟩
  have key : ∀ x ∈ tentRepellor μ, ∀ y ∈ tentRepellor μ, x < y →
      ∃ u v : Set ℝ, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ tentRepellor μ ⊆ u ∪ v ∧
        Disjoint u v := by
    intro x hx y hy hxy
    have hgap := tent_exists_gap_core μ hμ x y hxy
    obtain ⟨z, hz, hzn⟩ := Set.not_subset.mp hgap
    have hzx : x < z := lt_of_le_of_ne hz.1 (by rintro rfl; exact hzn hx)
    have hzy : z < y := lt_of_le_of_ne hz.2 (by rintro rfl; exact hzn hy)
    refine ⟨Set.Iio z, Set.Ioi z, isOpen_Iio, isOpen_Ioi, hzx, hzy, fun w hw => ?_, ?_⟩
    · rcases lt_trichotomy w z with h | h | h
      · exact Or.inl h
      · exact absurd (h ▸ hw) hzn
      · exact Or.inr h
    · exact Set.disjoint_left.mpr fun w (hw1 : w < z) (hw2 : z < w) => lt_asymm hw1 hw2
  intro x hx y hy hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key x hx y hy hlt
  · obtain ⟨u, v, hu, hv, hyu, hxv, hcov, hdisj⟩ := key y hy x hx hlt
    exact ⟨v, u, hv, hu, hxv, hyu, by rwa [Set.union_comm], hdisj.symm⟩

#print axioms solution
