-- Prove2me | solution 1 for OWMR.con_offset_exists
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T12:52:28.578208+00:00
-- url     : https://prove2.me/submissions/dc4d7174-0035-4f69-b27a-409747414946

import Definitions.Def_owmr_consolidation_policy

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace OWMR.Sel

/-- Atoms `u < g θ` with `g` monotone and continuous keep their truth value just left of `θ₀`. -/
lemma ev_lt (g : ℝ → ℝ) (hg : Monotone g) (hc : Continuous g) (u θ0 : ℝ) :
    ∀ᶠ θ in 𝓝[<] θ0, (u < g θ ↔ u < g θ0) := by
  by_cases h : u < g θ0
  · have : ∀ᶠ θ in 𝓝 θ0, u < g θ := (hc.tendsto θ0).eventually (lt_mem_nhds h)
    filter_upwards [nhdsWithin_le_nhds this] with θ hθ
    exact ⟨fun _ => h, fun _ => hθ⟩
  · filter_upwards [self_mem_nhdsWithin] with θ hθ
    refine ⟨fun h' => absurd (lt_of_lt_of_le h' (hg (le_of_lt hθ))) h, fun h' => absurd h' h⟩

lemma ev_le (g : ℝ → ℝ) (hg : Monotone g) (hc : Continuous g) (u θ0 : ℝ) :
    ∀ᶠ θ in 𝓝[<] θ0, (g θ ≤ u ↔ g θ0 ≤ u) := by
  by_cases h : g θ0 ≤ u
  · filter_upwards [self_mem_nhdsWithin] with θ hθ
    exact ⟨fun _ => h, fun _ => le_trans (hg (le_of_lt hθ)) h⟩
  · push Not at h
    have : ∀ᶠ θ in 𝓝 θ0, u < g θ := (hc.tendsto θ0).eventually (lt_mem_nhds h)
    filter_upwards [nhdsWithin_le_nhds this] with θ hθ
    exact ⟨fun h' => absurd h' (not_le.2 hθ), fun h' => absurd h' (not_le.2 h)⟩

lemma ev_third (θ0 : ℝ) (h3 : θ0 ≠ 1 / 3) : ∀ᶠ θ in 𝓝[<] θ0, (θ < 1 / 3 ↔ θ0 < 1 / 3) := by
  rcases lt_or_gt_of_ne h3 with h | h
  · filter_upwards [self_mem_nhdsWithin] with θ hθ
    exact ⟨fun _ => h, fun _ => lt_trans hθ h⟩
  · have : ∀ᶠ θ in 𝓝 θ0, 1 / 3 < θ := lt_mem_nhds h
    filter_upwards [nhdsWithin_le_nhds this] with θ hθ
    exact ⟨fun h' => absurd h' (not_lt.2 hθ.le), fun h' => absurd h' (not_lt.2 h.le)⟩

lemma ev_cross (Q : ℝ) (hQ : 0 < Q) (a b θ0 : ℝ) (h3 : θ0 ≠ 1 / 3) :
    ∀ᶠ θ in 𝓝[<] θ0, (crossesThreshold Q θ a b ↔ crossesThreshold Q θ0 a b) := by
  have hc : 0 ≤ 3 * Q / 4 := by positivity
  have hm1 : Monotone fun θ : ℝ => 3 * Q / 4 * θ := fun x y h => mul_le_mul_of_nonneg_left h hc
  have hm2 : Monotone fun θ : ℝ => 3 * Q / 4 * (1 + θ) := fun x y h =>
    mul_le_mul_of_nonneg_left (by linarith) hc
  have hc1 : Continuous fun θ : ℝ => 3 * Q / 4 * θ := by fun_prop
  have hc2 : Continuous fun θ : ℝ => 3 * Q / 4 * (1 + θ) := by fun_prop
  filter_upwards [ev_lt _ hm1 hc1 a θ0, ev_le _ hm1 hc1 b θ0, ev_lt _ hm2 hc2 a θ0,
    ev_le _ hm2 hc2 b θ0, ev_third θ0 h3] with θ e1 e2 e3 e4 e5
  simp only [crossesThreshold] at e1 e2 e3 e4 ⊢
  rw [e1, e2, e3, e4, e5]

lemma ev_ship (Q : ℝ) (hQ : 0 < Q) (A : ℕ → ℝ) (θ0 : ℝ) (h3 : θ0 ≠ 1 / 3) :
    ∀ k, ∀ᶠ θ in 𝓝[<] θ0, shippedPath Q θ A k = shippedPath Q θ0 A k
  | 0 => by
    filter_upwards [ev_cross Q hQ 0 (A 0) θ0 h3] with θ h
    simp only [shippedPath]
    by_cases hc : crossesThreshold Q θ0 0 (A 0)
    · rw [if_pos (h.2 hc), if_pos hc]
    · rw [if_neg (fun h' => hc (h.1 h')), if_neg hc]
  | k + 1 => by
    filter_upwards [ev_cross Q hQ (A k) (A (k + 1)) θ0 h3, ev_ship Q hQ A θ0 h3 k] with θ h h'
    simp only [shippedPath]
    by_cases hc : crossesThreshold Q θ0 (A k) (A (k + 1))
    · rw [if_pos (h.2 hc), if_pos hc]
    · rw [if_neg (fun h'' => hc (h.1 h'')), if_neg hc, h']

lemma ship_nonneg (Q θ : ℝ) (A : ℕ → ℝ) (hA0 : ∀ k, 0 ≤ A k) : ∀ k, 0 ≤ shippedPath Q θ A k
  | 0 => by simp only [shippedPath]; split_ifs; exacts [hA0 0, le_rfl]
  | k + 1 => by
    simp only [shippedPath]; split_ifs; exacts [hA0 _, ship_nonneg Q θ A hA0 k]

end OWMR.Sel

open OWMR OWMR.Sel

theorem solution {β : Type} [MeasurableSpace β] (ν : Measure β) [IsProbabilityMeasure ν]
    (K hp Q : ℝ) (hK : 0 ≤ K) (hhp : 0 ≤ hp) (hQ : 0 < Q) (A : ℕ → ℝ) (hA0 : ∀ k, 0 ≤ A k)
    (hAQ : ∀ k, A k ≤ Q) (L : ℕ) (X : β → ℕ → ℝ) (hXm : ∀ k, Measurable fun b => X b k)
    (hX0 : ∀ b k, 0 ≤ X b k) (e : ℕ ≃ {q : ℚ // 0 < q ∧ q < 1}) (j : ℕ) :
    ∃ k : ℕ, ∫⁻ b, ENNReal.ofReal (K * (1 + if ((e k : ℚ) : ℝ) < 1 / 3 then 2 else 1)
          + hp * ∑ k' ∈ Finset.range (L + 1),
            max (A k' - shippedPath Q ((e k : ℚ) : ℝ) A k' - X b k') 0) ∂ν
      < (∫⁻ θ in Set.Ioo (0 : ℝ) 1, ∫⁻ b, ENNReal.ofReal (K * (1 + if θ < 1 / 3 then 2 else 1)
          + hp * ∑ k' ∈ Finset.range (L + 1), max (A k' - shippedPath Q θ A k' - X b k') 0) ∂ν)
        + (2 : ℝ≥0∞)⁻¹ ^ j := by
  set f : ℝ → β → ℝ≥0∞ := fun θ b => ENNReal.ofReal (K * (1 + if θ < 1 / 3 then 2 else 1)
    + hp * ∑ k' ∈ Finset.range (L + 1), max (A k' - shippedPath Q θ A k' - X b k') 0) with hf
  set z : ℝ → ℝ≥0∞ := fun θ => ∫⁻ b, f θ b ∂ν with hz
  set zbar : ℝ≥0∞ := ∫⁻ θ in Set.Ioo (0 : ℝ) 1, z θ with hzbar
  set ε : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ j with hε
  set M : ℝ := 3 * K + hp * ((L + 1 : ℕ) * Q) with hM
  -- uniform bound
  have hbd : ∀ θ b, f θ b ≤ ENNReal.ofReal M := by
    intro θ b
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : K * (1 + if θ < 1 / 3 then 2 else 1) ≤ 3 * K := by
      split_ifs <;> nlinarith
    have h2 : ∑ k' ∈ Finset.range (L + 1), max (A k' - shippedPath Q θ A k' - X b k') 0
        ≤ ((L + 1 : ℕ) : ℝ) * Q := by
      have : ∀ k' ∈ Finset.range (L + 1), max (A k' - shippedPath Q θ A k' - X b k') 0 ≤ Q :=
        fun k' _ => max_le (by linarith [ship_nonneg Q θ A hA0 k', hX0 b k', hAQ k']) hQ.le
      calc _ ≤ ∑ _k' ∈ Finset.range (L + 1), Q := Finset.sum_le_sum this
        _ = _ := by simp
    have h3 := mul_le_mul_of_nonneg_left h2 hhp
    linarith
  have hzb : ∀ θ, z θ ≤ ENNReal.ofReal M := fun θ => by
    calc z θ ≤ ∫⁻ _b, ENNReal.ofReal M ∂ν := lintegral_mono fun b => hbd θ b
      _ = ENNReal.ofReal M := by simp
  have hzbar_fin : zbar ≠ ∞ := by
    refine ne_of_lt (lt_of_le_of_lt (setLIntegral_mono_ae (g := fun _ => ENNReal.ofReal M)
      measurable_const.aemeasurable (Filter.Eventually.of_forall fun θ _ => hzb θ)) ?_)
    rw [setLIntegral_const, Real.volume_Ioo]
    simp
  have hε0 : ε ≠ 0 := by
    rw [hε]; exact pow_ne_zero _ (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top)
  by_contra hcon
  push Not at hcon
  -- every rational offset is bad, hence every offset except `1/3`
  have hmeas : ∀ θ, Measurable (f θ) := by
    intro θ
    refine ENNReal.measurable_ofReal.comp (measurable_const.add (measurable_const.mul ?_))
    exact Finset.measurable_sum _ fun k' _ =>
      ((measurable_const.sub (hXm k')).max measurable_const)
  have hall : ∀ θ0 ∈ Set.Ioo (0 : ℝ) 1, θ0 ≠ 1 / 3 → zbar + ε ≤ z θ0 := by
    intro θ0 hθ0 h3
    -- rationals approaching from the left
    have hr : ∀ m : ℕ, ∃ r : ℚ, max 0 (θ0 - 1 / (m + 1)) < r ∧ (r : ℝ) < θ0 := fun m =>
      exists_rat_btwn (max_lt hθ0.1 (by
        have : (0 : ℝ) < 1 / (m + 1) := by positivity
        linarith))
    choose r hr1 hr2 using hr
    have hr0 : ∀ m, (0 : ℝ) < r m := fun m => lt_of_le_of_lt (le_max_left _ _) (hr1 m)
    have hr1' : ∀ m, (r m : ℝ) < 1 := fun m => lt_trans (hr2 m) hθ0.2
    have htend : Tendsto (fun m => (r m : ℝ)) atTop (𝓝[<] θ0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Filter.Eventually.of_forall hr2⟩
      refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => Filter.Eventually.of_forall fun m =>
        lt_trans (hr2 m) ha⟩
      obtain ⟨m0, hm0⟩ := exists_nat_one_div_lt (sub_pos.2 ha)
      refine Filter.eventually_atTop.2 ⟨m0, fun m hm => ?_⟩
      have h1 : 1 / ((m : ℝ) + 1) ≤ 1 / ((m0 : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hm)
      have h2 := lt_of_le_of_lt (le_max_right _ _) (hr1 m)
      linarith
    -- pointwise eventual equality of the integrand
    have hev : ∀ b, ∀ᶠ θ in 𝓝[<] θ0, f θ b = f θ0 b := by
      intro b
      have hs : ∀ᶠ θ in 𝓝[<] θ0, ∀ k' ∈ Finset.range (L + 1),
          shippedPath Q θ A k' = shippedPath Q θ0 A k' :=
        (Finset.eventually_all _).2 fun k' _ => ev_ship Q hQ A θ0 h3 k'
      filter_upwards [hs, ev_third θ0 h3] with θ h1 h2
      simp only [hf]
      congr 2
      · by_cases h : θ0 < 1 / 3
        · rw [if_pos (h2.2 h), if_pos h]
        · rw [if_neg (fun h' => h (h2.1 h')), if_neg h]
      · congr 1
        exact Finset.sum_congr rfl fun k' hk' => by rw [h1 k' hk']
    have hlim : Tendsto (fun m => z (r m)) atTop (𝓝 (z θ0)) := by
      refine tendsto_lintegral_of_dominated_convergence (fun _ => ENNReal.ofReal M)
        (fun m => hmeas _) (fun m => Filter.Eventually.of_forall fun b => hbd _ b) (by simp)
        (Filter.Eventually.of_forall fun b => ?_)
      exact tendsto_nhds_of_eventually_eq ((htend.eventually (hev b)))
    have hge : ∀ m, zbar + ε ≤ z (r m) := by
      intro m
      have := hcon (e.symm ⟨r m, by exact_mod_cast hr0 m, by exact_mod_cast hr1' m⟩)
      rw [Equiv.apply_symm_apply] at this
      have e1 : zbar = ∫⁻ θ in Set.Ioo (0 : ℝ) 1, ∫⁻ b, ENNReal.ofReal
          (K * (1 + if θ < 1 / 3 then 2 else 1)
            + hp * ∑ k' ∈ Finset.range (L + 1), max (A k' - shippedPath Q θ A k' - X b k') 0) ∂ν :=
        rfl
      have e2 : z (r m) = ∫⁻ b, ENNReal.ofReal
          (K * (1 + if ((r m : ℚ) : ℝ) < 1 / 3 then 2 else 1)
            + hp * ∑ k' ∈ Finset.range (L + 1),
              max (A k' - shippedPath Q ((r m : ℚ) : ℝ) A k' - X b k') 0) ∂ν := rfl
      rw [e1, e2]
      exact this
    exact ge_of_tendsto hlim (Filter.Eventually.of_forall hge)
  -- integrate
  have hae : ∀ᵐ θ ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)), zbar + ε ≤ z θ := by
    have h1 : ∀ᵐ θ ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)), θ ∈ Set.Ioo (0 : ℝ) 1 :=
      ae_restrict_mem measurableSet_Ioo
    have h2 : ∀ᵐ θ ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)), θ ≠ 1 / 3 := by
      have h0 : (volume.restrict (Set.Ioo (0 : ℝ) 1)) {1 / 3} = 0 := by
        rw [Measure.restrict_apply (measurableSet_singleton _)]
        exact measure_mono_null Set.inter_subset_left (measure_singleton _)
      rw [ae_iff]
      exact measure_mono_null (fun θ hθ => by simpa using hθ) h0
    filter_upwards [h1, h2] with θ hθ1 hθ2
    exact hall θ hθ1 hθ2
  have : zbar + ε ≤ zbar := by
    calc zbar + ε = ∫⁻ _θ in Set.Ioo (0 : ℝ) 1, (zbar + ε) := by
          rw [setLIntegral_const, Real.volume_Ioo]; simp
      _ ≤ zbar := lintegral_mono_ae hae
  exact absurd this (not_le.2 (ENNReal.lt_add_right hzbar_fin hε0))
