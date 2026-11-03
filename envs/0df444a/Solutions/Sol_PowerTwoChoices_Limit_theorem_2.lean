-- Prove2me | solution 1 for PowerTwoChoices.Limit.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T20:51:34.579303+00:00
-- url     : https://prove2.me/submissions/e04021ed-cc2a-436f-a9f6-f896a0603668

import Mathlib
import Definitions.Def_PowerTwoChoices_Limit_SupermarketSystem

open scoped ENNReal
open Filter Topology
open PowerTwoChoices.Limit

private lemma isState_le_one {x : ℕ → ℝ} (hx : IsState x) (i : ℕ) : x i ≤ 1 := by
  have := hx.2.2 (Nat.zero_le i)
  linarith [hx.1]

private lemma isState_eq_zero_of_ge {x : ℕ → ℝ} (hx : IsState x) {j i : ℕ}
    (hj : x j = 0) (hji : j ≤ i) : x i = 0 := by
  have h1 := hx.2.1 i
  have h2 := hx.2.2 hji
  linarith

private lemma deriv_nonneg_of_max_on_Icc {g : ℝ → ℝ} {t0 d : ℝ}
    (ht0 : 0 < t0) (hd : HasDerivWithinAt g d (Set.Ici 0) t0)
    (hmax : ∀ t ∈ Set.Icc 0 t0, g t ≤ g t0) : 0 ≤ d := by
  have hd_at : HasDerivAt g d t0 := hd.hasDerivAt (Ici_mem_nhds ht0)
  have hd_lt : HasDerivWithinAt g d (Set.Iio t0) t0 := hd_at.hasDerivWithinAt
  have hdiff : Set.Iio t0 \ {t0} = Set.Iio t0 :=
    Set.diff_singleton_eq_self (by simp)
  rw [hasDerivWithinAt_iff_tendsto_slope, hdiff] at hd_lt
  have hmem : Set.Ico 0 t0 ∈ 𝓝[<] t0 := Ico_mem_nhdsLT ht0
  have h_nonneg : ∀ᶠ t in 𝓝[<] t0, 0 ≤ slope g t0 t := by
    filter_upwards [hmem] with t ht
    rw [slope_def_field]
    have hle : g t - g t0 ≤ 0 := sub_nonpos.mpr (hmax t ⟨ht.1, ht.2.le⟩)
    have hlt : t - t0 < 0 := sub_neg.mpr ht.2
    exact div_nonneg_of_nonpos hle hlt.le
  exact ge_of_tendsto hd_lt h_nonneg

private lemma nonpos_of_hasDerivWithinAt_neg {g g' : ℝ → ℝ}
    (hg0 : g 0 ≤ 0)
    (hderiv : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt g (g' t) (Set.Ici 0) t)
    (hneg : ∀ t : ℝ, 0 < t → 0 < g t → g' t < 0)
    {T : ℝ} (hT : 0 ≤ T) : g T ≤ 0 := by
  have hcont : ContinuousOn g (Set.Icc 0 T) := by
    intro t ht
    exact ((hderiv t ht.1).continuousWithinAt).mono Set.Icc_subset_Ici_self
  rcases isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hT) hcont with ⟨t0, ht0, hmax⟩
  have hT_le : g T ≤ g t0 := hmax (Set.right_mem_Icc.mpr hT)
  by_contra hpos
  push_neg at hpos
  have ht0_pos : 0 < g t0 := lt_of_lt_of_le hpos hT_le
  have ht0_ne : t0 ≠ 0 := by
    intro h0
    subst h0
    linarith
  have ht0_gt : 0 < t0 := lt_of_le_of_ne ht0.1 (Ne.symm ht0_ne)
  have hd_nonneg : 0 ≤ g' t0 :=
    deriv_nonneg_of_max_on_Icc ht0_gt (hderiv t0 ht0.1)
      (fun t ht => hmax ⟨ht.1, ht.2.trans ht0.2⟩)
  have hd_neg : g' t0 < 0 := hneg t0 ht0_gt ht0_pos
  linarith

private lemma sum_drift_eq (lam : ℝ) (d : ℕ) (x : ℕ → ℝ) (m : ℕ) (hm : 1 ≤ m) :
    ∀ K : ℕ, ∑ k ∈ Finset.range K, drift lam d x (m + k) =
      lam * (x (m - 1) ^ d - x (m + K - 1) ^ d) - (x m - x (m + K))
  | 0 => by
    have : m + 0 - 1 = m - 1 := by omega
    simp [this]
  | K + 1 => by
    rw [Finset.sum_range_succ, sum_drift_eq lam d x m hm K]
    unfold drift
    have h1 : m + K - 1 + 1 = m + K := by omega
    have h2 : m + (K + 1) - 1 = m + K := by omega
    have h3 : m + K + 1 = m + (K + 1) := by omega
    rw [h2, ← h3]
    ring

private lemma drift_sum_le_one {lam : ℝ} {d : ℕ} (hlam0 : 0 < lam) (hlam1 : lam < 1)
    {x : ℕ → ℝ} (hx : IsState x) (m : ℕ) (hm : 1 ≤ m) (K : ℕ) :
    ∑ k ∈ Finset.range K, drift lam d x (m + k) ≤ 1 := by
  rw [sum_drift_eq lam d x m hm K]
  have h1 : x (m - 1) ^ d ≤ 1 := pow_le_one₀ (hx.2.1 (m - 1)) (isState_le_one hx (m - 1))
  have h2 : 0 ≤ x (m + K - 1) ^ d := pow_nonneg (hx.2.1 (m + K - 1)) d
  have h3 : x (m + K) ≤ x m := hx.2.2 (Nat.le_add_right m K)
  nlinarith

private lemma hasDerivWithinAt_sum_coords {lam : ℝ} {d : ℕ} {s : ℝ → ℕ → ℝ}
    (hs : IsTrajectory lam d s) (m : ℕ) (hm : 1 ≤ m) (K : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun u => ∑ k ∈ Finset.range K, s u (m + k))
      (∑ k ∈ Finset.range K, drift lam d (s t) (m + k)) (Set.Ici 0) t := by
  induction K with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    exact hasDerivWithinAt_const t (Set.Ici 0) (0 : ℝ)
  | succ K ih =>
    simp only [Finset.sum_range_succ]
    exact ih.add (hs.2 (m + K) (by omega) t ht)

private lemma tail_sum_le_two_mul_t {lam : ℝ} {d : ℕ} (hlam0 : 0 < lam) (hlam1 : lam < 1)
    {s : ℝ → ℕ → ℝ} (hs : IsTrajectory lam d s) {m : ℕ} (hm : 1 ≤ m) (hm0 : s 0 m = 0)
    (K : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∑ k ∈ Finset.range K, s t (m + k) ≤ 2 * t := by
  let g : ℝ → ℝ := fun u => (∑ k ∈ Finset.range K, s u (m + k)) - 2 * u
  let g' : ℝ → ℝ := fun u => (∑ k ∈ Finset.range K, drift lam d (s u) (m + k)) - 2
  have hg0 : g 0 ≤ 0 := by
    have hsum0 : ∑ k ∈ Finset.range K, s 0 (m + k) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      exact isState_eq_zero_of_ge (hs.1 0 le_rfl) hm0 (Nat.le_add_right m k)
    simp [g, hsum0]
  have hderiv : ∀ u : ℝ, 0 ≤ u → HasDerivWithinAt g (g' u) (Set.Ici 0) u := by
    intro u hu
    have h1 := hasDerivWithinAt_sum_coords hs m hm K hu
    have h2 : HasDerivWithinAt (fun v : ℝ => 2 * v) 2 (Set.Ici 0) u := by
      simpa using (hasDerivWithinAt_id u (Set.Ici 0)).const_mul (2 : ℝ)
    exact h1.sub h2
  have hneg : ∀ u : ℝ, 0 < u → 0 < g u → g' u < 0 := by
    intro u hu _
    have hle := drift_sum_le_one (d := d) hlam0 hlam1 (hs.1 u hu.le) m hm K
    dsimp [g']
    linarith
  have := nonpos_of_hasDerivWithinAt_neg hg0 hderiv hneg ht
  dsimp [g] at this
  linarith

private lemma coord_le_div_of_tail_sum {lam : ℝ} {d : ℕ} (hlam0 : 0 < lam) (hlam1 : lam < 1)
    {s : ℝ → ℕ → ℝ} (hs : IsTrajectory lam d s) {m : ℕ} (hm : 1 ≤ m) (hm0 : s 0 m = 0)
    {K : ℕ} (hK : 1 ≤ K) {t : ℝ} (ht : 0 ≤ t) {i : ℕ} (hi : m + K ≤ i) :
    s t i ≤ (2 * t) / (K : ℝ) := by
  have hst : IsState (s t) := hs.1 t ht
  have hsum := tail_sum_le_two_mul_t hlam0 hlam1 hs hm hm0 K ht
  have hmin : (K : ℝ) * s t i ≤ ∑ k ∈ Finset.range K, s t (m + k) := by
    have : ∑ k ∈ Finset.range K, s t i ≤ ∑ k ∈ Finset.range K, s t (m + k) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [Finset.mem_range] at hk
      exact hst.2.2 (by omega)
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  have hKpos : (0 : ℝ) < (K : ℝ) := by positivity
  rw [le_div_iff₀ hKpos]
  linarith [hmin, hsum]

private lemma sum_range_geom_succ (d k : ℕ) :
    ∑ r ∈ Finset.range (k + 1), d ^ r = 1 + (∑ r ∈ Finset.range k, d ^ r) * d := by
  induction k with
  | zero => simp
  | succ k ih =>
    conv_lhs => rw [Finset.sum_range_succ, ih]
    conv_rhs => rw [Finset.sum_range_succ]
    rw [pow_succ]
    ring

private lemma fixedPoint_succ (lam : ℝ) (d k : ℕ) :
    fixedPoint lam d (k + 1) = lam * (fixedPoint lam d k) ^ d := by
  unfold fixedPoint
  rw [sum_range_geom_succ, pow_add, pow_one, pow_mul]

private lemma fixedPoint_zero (lam : ℝ) (d : ℕ) : fixedPoint lam d 0 = 1 := by
  simp [fixedPoint]

private lemma fixedPoint_nonneg {lam : ℝ} (hlam0 : 0 < lam) (d i : ℕ) :
    0 ≤ fixedPoint lam d i :=
  pow_nonneg hlam0.le _

private lemma fixedPoint_le_one {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (d i : ℕ) :
    fixedPoint lam d i ≤ 1 :=
  pow_le_one₀ hlam0.le hlam1.le

private noncomputable def uSeq (lam : ℝ) (d m i : ℕ) : ℝ :=
  fixedPoint lam d (i - (m - 1))

private lemma uSeq_eq_one_of_lt (lam : ℝ) (d m i : ℕ) (hi : i < m) :
    uSeq lam d m i = 1 := by
  unfold uSeq
  have : i - (m - 1) = 0 := by omega
  rw [this, fixedPoint_zero]

private lemma uSeq_nonneg {lam : ℝ} (hlam0 : 0 < lam) (d m i : ℕ) :
    0 ≤ uSeq lam d m i :=
  fixedPoint_nonneg hlam0 d _

private lemma uSeq_le_one {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (d m i : ℕ) :
    uSeq lam d m i ≤ 1 :=
  fixedPoint_le_one hlam0 hlam1 d _

private lemma uSeq_step {lam : ℝ} {d m i : ℕ} (hm : 1 ≤ m) (hi : m ≤ i) :
    lam * (uSeq lam d m (i - 1)) ^ d = uSeq lam d m i := by
  unfold uSeq
  have h1 : i - (m - 1) = (i - 1 - (m - 1)) + 1 := by omega
  rw [h1, fixedPoint_succ]

private lemma pow_sub_pow_le {a b δ : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hδ : 0 ≤ δ) (hab : a - b ≤ δ) (d : ℕ) :
    a ^ d - b ^ d ≤ (d : ℝ) * δ := by
  by_cases hle : a ≤ b
  · have : a ^ d ≤ b ^ d := pow_le_pow_left₀ ha0 hle d
    have hdδ : 0 ≤ (d : ℝ) * δ := by positivity
    linarith
  · push_neg at hle
    induction d with
    | zero => simp
    | succ d ih =>
      have had_ge : b ^ d ≤ a ^ d := pow_le_pow_left₀ hb0 hle.le d
      have hbd1 : b ^ d ≤ 1 := pow_le_one₀ hb0 hb1
      have hdecomp : a ^ (d + 1) - b ^ (d + 1) = a * (a ^ d - b ^ d) + b ^ d * (a - b) := by ring
      have h1 : a * (a ^ d - b ^ d) ≤ 1 * (a ^ d - b ^ d) :=
        mul_le_mul_of_nonneg_right ha1 (sub_nonneg.mpr had_ge)
      have h2 : b ^ d * (a - b) ≤ 1 * δ := by
        calc b ^ d * (a - b) ≤ 1 * (a - b) :=
              mul_le_mul_of_nonneg_right hbd1 (by linarith)
          _ ≤ 1 * δ := by linarith
      push_cast
      linarith

private lemma main_invariant {lam : ℝ} {d : ℕ} (hd : 2 ≤ d) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    {s : ℝ → ℕ → ℝ} (hs : IsTrajectory lam d s) {m : ℕ} (hm : 1 ≤ m) (hm0 : s 0 m = 0)
    {T : ℝ} (hT : 0 ≤ T) (i_star : ℕ) :
    s T i_star ≤ uSeq lam d m i_star := by
  by_contra hgt
  push_neg at hgt
  let C : ℝ := lam * (d : ℝ) + 2
  have hC_pos : 0 < C := by positivity
  let h : ℕ → ℝ → ℝ := fun i t => (s t i - uSeq lam d m i) * Real.exp (-C * t)
  have h_star_pos : 0 < h i_star T :=
    mul_pos (sub_pos.mpr hgt) (Real.exp_pos _)
  let ε : ℝ := h i_star T / 2
  have hε_pos : 0 < ε := half_pos h_star_pos
  obtain ⟨K, hK_gt⟩ := exists_nat_gt ((2 * T) / ε)
  let K1 : ℕ := max K (max 1 (i_star + 1))
  have hK1_ge_one : 1 ≤ K1 := le_trans (le_max_left 1 _) (le_max_right K _)
  have hK1_gt : (2 * T) / ε < (K1 : ℝ) := by
    calc (2 * T) / ε < (K : ℝ) := hK_gt
      _ ≤ (K1 : ℝ) := by exact_mod_cast le_max_left K _
  let M : ℕ := m + K1
  have hi_star_lt_M : i_star < M := by
    have : i_star + 1 ≤ K1 := le_trans (le_max_right 1 _) (le_max_right K _)
    omega
  have h_tail : ∀ t ∈ Set.Icc 0 T, ∀ i : ℕ, M ≤ i → h i t < h i_star T := by
    intro t ht i hi
    have hsi : s t i ≤ (2 * t) / (K1 : ℝ) :=
      coord_le_div_of_tail_sum hlam0 hlam1 hs hm hm0 hK1_ge_one ht.1 hi
    have hK1_pos : (0 : ℝ) < (K1 : ℝ) := by positivity
    have hsi_lt_ε : s t i < ε := by
      have hmul : 2 * T < ε * (K1 : ℝ) := by
        have := (div_lt_iff₀ hε_pos).mp hK1_gt
        linarith
      calc s t i ≤ (2 * t) / (K1 : ℝ) := hsi
        _ ≤ (2 * T) / (K1 : ℝ) := by
          apply div_le_div_of_nonneg_right _ hK1_pos.le
          linarith [ht.2]
        _ < ε := (div_lt_iff₀ hK1_pos).mpr hmul
    have hu_nonneg : 0 ≤ uSeq lam d m i := uSeq_nonneg hlam0 d m i
    have hexp_le : Real.exp (-C * t) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [ht.1, hC_pos]
    have hdiff_le : s t i - uSeq lam d m i ≤ s t i := by linarith
    by_cases hdiff : s t i - uSeq lam d m i ≤ 0
    · have : h i t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hdiff (Real.exp_pos _).le
      linarith
    · push_neg at hdiff
      have : h i t ≤ s t i * 1 :=
        mul_le_mul hdiff_le hexp_le (Real.exp_pos _).le (hs.1 t ht.1 |>.2.1 i)
      linarith [show ε < h i_star T by dsimp [ε]; linarith]
  have hderiv_h : ∀ i : ℕ, 1 ≤ i → ∀ t : ℝ, 0 ≤ t →
      HasDerivWithinAt (h i)
        ((drift lam d (s t) i - C * (s t i - uSeq lam d m i)) * Real.exp (-C * t))
        (Set.Ici 0) t := by
    intro i hi t ht
    have hd1 : HasDerivWithinAt (fun u => s u i - uSeq lam d m i)
        (drift lam d (s t) i) (Set.Ici 0) t :=
      (hs.2 i hi t ht).sub_const (uSeq lam d m i)
    have hd2 : HasDerivWithinAt (fun u => Real.exp (-C * u))
        (Real.exp (-C * t) * (-C)) (Set.Ici 0) t := by
      have hlin : HasDerivWithinAt (fun u : ℝ => -C * u) (-C) (Set.Ici 0) t := by
        simpa using (hasDerivWithinAt_id t (Set.Ici 0)).const_mul (-C)
      exact hlin.exp
    exact (hd1.mul hd2).congr_deriv (by ring)
  have hcont_h : ∀ i : ℕ, ContinuousOn (h i) (Set.Icc 0 T) := by
    intro i
    by_cases hi0 : i = 0
    · subst hi0
      have hcon : ContinuousOn (fun t : ℝ => (1 - uSeq lam d m 0) * Real.exp (-C * t)) (Set.Icc 0 T) :=
        (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn
      refine hcon.congr ?_
      intro t ht
      simp [h, (hs.1 t ht.1).1]
    · have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
      intro t ht
      exact ((hderiv_h i hi1 t ht.1).continuousWithinAt).mono Set.Icc_subset_Ici_self
  have hmax_each : ∀ i : ℕ, ∃ t_i ∈ Set.Icc 0 T, IsMaxOn (h i) (Set.Icc 0 T) t_i :=
    fun i => isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hT) (hcont_h i)
  choose tMax htMax_mem htMax_max using hmax_each
  have hM_nonempty : (Finset.range M).Nonempty :=
    ⟨i_star, Finset.mem_range.mpr hi_star_lt_M⟩
  obtain ⟨i0, hi0_mem, hi0_max⟩ :=
    Finset.exists_max_image (Finset.range M) (fun i => h i (tMax i)) hM_nonempty
  let t0 : ℝ := tMax i0
  have ht0_mem : t0 ∈ Set.Icc 0 T := htMax_mem i0
  have h_bound_range : ∀ i ∈ Finset.range M, ∀ t ∈ Set.Icc 0 T, h i t ≤ h i0 t0 := by
    intro i hi t ht
    calc h i t ≤ h i (tMax i) := htMax_max i ht
      _ ≤ h i0 t0 := hi0_max i hi
  have hi0_t0_ge_star : h i_star T ≤ h i0 t0 :=
    h_bound_range i_star (Finset.mem_range.mpr hi_star_lt_M) T (Set.right_mem_Icc.mpr hT)
  have hi0_t0_pos : 0 < h i0 t0 := lt_of_lt_of_le h_star_pos hi0_t0_ge_star
  have h_bound_all : ∀ i : ℕ, ∀ t ∈ Set.Icc 0 T, h i t ≤ h i0 t0 := by
    intro i t ht
    by_cases hiM : i < M
    · exact h_bound_range i (Finset.mem_range.mpr hiM) t ht
    · push_neg at hiM
      exact (h_tail t ht i hiM).le.trans hi0_t0_ge_star
  have hi0_ge_m : m ≤ i0 := by
    by_contra hlt
    push_neg at hlt
    have hu1 : uSeq lam d m i0 = 1 := uSeq_eq_one_of_lt lam d m i0 hlt
    have hs1 : s t0 i0 ≤ 1 := isState_le_one (hs.1 t0 ht0_mem.1) i0
    have : h i0 t0 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_pos _).le
    linarith
  have ht0_pos : 0 < t0 := by
    have ht0_ne : t0 ≠ 0 := by
      intro h0
      have hs0 : s 0 i0 = 0 := isState_eq_zero_of_ge (hs.1 0 le_rfl) hm0 hi0_ge_m
      have hu0 : 0 ≤ uSeq lam d m i0 := uSeq_nonneg hlam0 d m i0
      have : h i0 t0 ≤ 0 := by
        rw [h0]
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_pos _).le
      linarith
    exact lt_of_le_of_ne ht0_mem.1 (Ne.symm ht0_ne)
  have hi0_ge_one : 1 ≤ i0 := le_trans hm hi0_ge_m
  have hd_nonneg : 0 ≤ (drift lam d (s t0) i0 - C * (s t0 i0 - uSeq lam d m i0)) * Real.exp (-C * t0) :=
    deriv_nonneg_of_max_on_Icc ht0_pos (hderiv_h i0 hi0_ge_one t0 ht0_mem.1)
      (fun t ht => htMax_max i0 ⟨ht.1, ht.2.trans ht0_mem.2⟩)
  let δ : ℝ := s t0 i0 - uSeq lam d m i0
  have hδ_pos : 0 < δ := by
    by_contra hle
    push_neg at hle
    have : h i0 t0 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hle (Real.exp_pos _).le
    linarith
  have h_prev_le : s t0 (i0 - 1) - uSeq lam d m (i0 - 1) ≤ δ := by
    have := h_bound_all (i0 - 1) t0 ht0_mem
    exact le_of_mul_le_mul_right this (Real.exp_pos _)
  have h_next_le : s t0 (i0 + 1) - uSeq lam d m (i0 + 1) ≤ δ := by
    have := h_bound_all (i0 + 1) t0 ht0_mem
    exact le_of_mul_le_mul_right this (Real.exp_pos _)
  have hst0 : IsState (s t0) := hs.1 t0 ht0_mem.1
  have hpow_prev : s t0 (i0 - 1) ^ d - uSeq lam d m (i0 - 1) ^ d ≤ (d : ℝ) * δ :=
    pow_sub_pow_le (hst0.2.1 _) (isState_le_one hst0 _)
      (uSeq_nonneg hlam0 d m _) (uSeq_le_one hlam0 hlam1 d m _) hδ_pos.le h_prev_le d
  have hpow_curr : uSeq lam d m i0 ^ d ≤ s t0 i0 ^ d :=
    pow_le_pow_left₀ (uSeq_nonneg hlam0 d m i0) (by dsimp [δ] at hδ_pos; linarith) d
  have hu_drift : drift lam d (uSeq lam d m) i0 = 0 := by
    unfold drift
    have hstep1 := uSeq_step (lam := lam) (d := d) hm hi0_ge_m
    have hstep2 := uSeq_step (lam := lam) (d := d) (i := i0 + 1) hm (by omega)
    simp only [Nat.add_sub_cancel] at hstep2
    linarith
  have hdrift_bound : drift lam d (s t0) i0 ≤ lam * (d : ℝ) * δ := by
    have hdiff : drift lam d (s t0) i0 = drift lam d (s t0) i0 - drift lam d (uSeq lam d m) i0 := by
      rw [hu_drift, sub_zero]
    rw [hdiff]
    unfold drift
    have h1 : lam * (s t0 (i0 - 1) ^ d - uSeq lam d m (i0 - 1) ^ d) ≤ lam * ((d : ℝ) * δ) :=
      mul_le_mul_of_nonneg_left hpow_prev hlam0.le
    have h2 : 0 ≤ lam * (s t0 i0 ^ d - uSeq lam d m i0 ^ d) :=
      mul_nonneg hlam0.le (sub_nonneg.mpr hpow_curr)
    have h3 : s t0 i0 - uSeq lam d m i0 = δ := rfl
    linarith
  have hd_neg : (drift lam d (s t0) i0 - C * δ) * Real.exp (-C * t0) < 0 := by
    apply mul_neg_of_neg_of_pos _ (Real.exp_pos _)
    dsimp [C]
    linarith
  linarith

theorem solution (lam : ℝ) (d : ℕ) (hd : 2 ≤ d) (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    (∀ s : ℝ → ℕ → ℝ, IsTrajectory lam d s → (∃ j : ℕ, s 0 j = 0) →
      ∃ (N : ℕ) (α β γ : ℝ), ∀ t : ℝ, 0 ≤ t → IsDoublyExpBound N α β γ (s t)) ∧
    (∀ s : ℝ → ℕ → ℝ, IsTrajectory lam d s → s 0 = emptyState →
      ∀ t : ℝ, 0 ≤ t → ∀ i : ℕ, s t i ≤ fixedPoint lam d i) := by
  refine ⟨?_, ?_⟩
  · intro s hs ⟨j, hj⟩
    let m : ℕ := max j 1
    have hm1 : 1 ≤ m := le_max_right j 1
    have hm0 : s 0 m = 0 := isState_eq_zero_of_ge (hs.1 0 le_rfl) hj (le_max_left j 1)
    let β : ℝ := (d : ℝ)
    let α : ℝ := lam ^ ((β ^ m)⁻¹)
    refine ⟨m, α, β, 1, ?_⟩
    intro t ht
    have hβ_gt_one : 1 < β := by
      dsimp [β]
      exact_mod_cast lt_of_lt_of_le (by decide : 1 < 2) hd
    have hβm_pos : 0 < (β ^ m)⁻¹ := by positivity
    have hα_pos : 0 < α := Real.rpow_pos_of_pos hlam0 _
    have hα_lt_one : α < 1 := Real.rpow_lt_one hlam0.le hlam1 hβm_pos
    refine ⟨hm1, hα_pos, hα_lt_one, hβ_gt_one, zero_lt_one, ?_⟩
    intro i hi
    have hinv := main_invariant hd hlam0 hlam1 hs hm1 hm0 ht i
    have hexp_ge : d ^ (i - m) ≤ ∑ k ∈ Finset.range (i - (m - 1)), d ^ k := by
      have hrew : i - (m - 1) = (i - m) + 1 := by omega
      rw [hrew, Finset.sum_range_succ]
      exact Nat.le_add_left _ _
    have hu_le : uSeq lam d m i ≤ lam ^ (d ^ (i - m)) := by
      unfold uSeq fixedPoint
      exact pow_le_pow_of_le_one hlam0.le hlam1.le hexp_ge
    have hrpow_eq : (1 : ℝ) * α ^ (β ^ i) = lam ^ (d ^ (i - m)) := by
      rw [one_mul]
      dsimp [α]
      rw [← Real.rpow_mul hlam0.le]
      have hpow_div : (β ^ m)⁻¹ * β ^ i = ((d ^ (i - m) : ℕ) : ℝ) := by
        have hsplit : i = m + (i - m) := by omega
        have hβ_ne : β ^ m ≠ 0 := by positivity
        conv_lhs => rw [hsplit, pow_add]
        rw [inv_mul_cancel_left₀ hβ_ne]
        simp [β]
      rw [hpow_div, Real.rpow_natCast]
    linarith
  · intro s hs hempty t ht i
    have hm0 : s 0 1 = 0 := by
      rw [hempty]
      simp [emptyState]
    have hinv := main_invariant hd hlam0 hlam1 hs le_rfl hm0 ht i
    simpa [uSeq] using hinv
