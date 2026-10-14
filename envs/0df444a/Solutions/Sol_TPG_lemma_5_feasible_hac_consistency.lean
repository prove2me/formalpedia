-- Prove2me | solution 1 for TPG.lemma_5_feasible_hac_consistency
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:40:38.774549+00:00
-- url     : https://prove2.me/submissions/0302c0fc-b751-4c25-9a70-ed2f020b1aa3

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Definitions.Def_TPG_Inference
import Theorems.Thm_TPG_isProbabilityMeasure_trajLaw
import Theorems.Thm_TPG_ae_abs_Y_le

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
open TPG

/-! ### Deterministic algebra for lagged sums -/

/-- Each time `t` has at most one partner `t' = t + ℓ`. -/
private lemma h5_lag_sum_left {T : ℕ} (ℓ : ℕ) (f : Fin T → ℝ) (hf : ∀ t, 0 ≤ f t) :
    ∑ t : Fin T, ∑ t' : Fin T, (if (t : ℕ) + ℓ = (t' : ℕ) then f t else 0) ≤ ∑ t, f t := by
  refine Finset.sum_le_sum fun t _ => ?_
  by_cases h : (t : ℕ) + ℓ < T
  · rw [Finset.sum_eq_single (⟨(t : ℕ) + ℓ, h⟩ : Fin T)]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro h'
      exact hb (Fin.ext h'.symm)
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · rw [Finset.sum_eq_zero]
    · exact hf t
    · intro b _
      rw [if_neg]
      intro h'
      exact h (h' ▸ b.isLt)

/-- Each time `t'` has at most one partner `t = t' - ℓ`. -/
private lemma h5_lag_sum_right {T : ℕ} (ℓ : ℕ) (f : Fin T → ℝ) (hf : ∀ t, 0 ≤ f t) :
    ∑ t : Fin T, ∑ t' : Fin T, (if (t : ℕ) + ℓ = (t' : ℕ) then f t' else 0) ≤ ∑ t, f t := by
  refine le_of_eq_of_le Finset.sum_comm ?_
  refine Finset.sum_le_sum fun t' _ => ?_
  by_cases h : ℓ ≤ (t' : ℕ)
  · rw [Finset.sum_eq_single (⟨(t' : ℕ) - ℓ, by omega⟩ : Fin T)]
    · simp [Nat.sub_add_cancel h]
    · intro b _ hb
      rw [if_neg]
      intro h'
      apply hb
      apply Fin.ext
      simp only
      omega
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · rw [Finset.sum_eq_zero]
    · exact hf t'
    · intro b _
      rw [if_neg]
      omega

/-- Changing the centering of a lagged product sum from `m t` to a common constant `bbar`
costs at most `2 K √Q + Q`, where `Q = 2 (bbar - mbar)² + 2 (1/T) ∑ (m t - mbar)²`. -/
private lemma h5_lag_diff {T : ℕ} (hT : 0 < T) (ℓ : ℕ) (b m : Fin T → ℝ) (K bbar mbar : ℝ)
    (hb : ∀ t, |b t - m t| ≤ K) :
    |(1 / (T : ℝ)) * ∑ t : Fin T, ∑ t' : Fin T,
          (if (t : ℕ) + ℓ = (t' : ℕ) then (b t - bbar) * (b t' - bbar) else 0)
        - (1 / (T : ℝ)) * ∑ t : Fin T, ∑ t' : Fin T,
          (if (t : ℕ) + ℓ = (t' : ℕ) then (b t - m t) * (b t' - m t') else 0)|
      ≤ 2 * K * Real.sqrt (2 * (bbar - mbar) ^ 2 + 2 * ((1 / (T : ℝ)) * ∑ t, (m t - mbar) ^ 2))
        + (2 * (bbar - mbar) ^ 2 + 2 * ((1 / (T : ℝ)) * ∑ t, (m t - mbar) ^ 2)) := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hK : 0 ≤ K := le_trans (abs_nonneg _) (hb ⟨0, hT⟩)
  have hTinv : (0 : ℝ) ≤ 1 / (T : ℝ) := by positivity
  -- the deviations `d t = bbar - m t`
  have step1 : |(1 / (T : ℝ)) * ∑ t : Fin T, ∑ t' : Fin T,
          (if (t : ℕ) + ℓ = (t' : ℕ) then (b t - bbar) * (b t' - bbar) else 0)
        - (1 / (T : ℝ)) * ∑ t : Fin T, ∑ t' : Fin T,
          (if (t : ℕ) + ℓ = (t' : ℕ) then (b t - m t) * (b t' - m t') else 0)|
      ≤ 2 * K * ((1 / (T : ℝ)) * ∑ t, |bbar - m t|) + (1 / (T : ℝ)) * ∑ t, (bbar - m t) ^ 2 := by
    have hpt : ∀ t t' : Fin T,
        |(if (t : ℕ) + ℓ = (t' : ℕ) then (b t - bbar) * (b t' - bbar) else 0)
          - (if (t : ℕ) + ℓ = (t' : ℕ) then (b t - m t) * (b t' - m t') else 0)|
        ≤ (if (t : ℕ) + ℓ = (t' : ℕ) then K * |bbar - m t| + (bbar - m t) ^ 2 / 2 else 0)
          + (if (t : ℕ) + ℓ = (t' : ℕ) then K * |bbar - m t'| + (bbar - m t') ^ 2 / 2 else 0) := by
      intro t t'
      split_ifs with h
      · have e : (b t - bbar) * (b t' - bbar) - (b t - m t) * (b t' - m t')
            = -((b t - m t) * (bbar - m t')) - (bbar - m t) * (b t' - m t')
              + (bbar - m t) * (bbar - m t') := by ring
        rw [e]
        have h1 : |(b t - m t) * (bbar - m t')| ≤ K * |bbar - m t'| := by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hb t) (abs_nonneg _)
        have h2 : |(bbar - m t) * (b t' - m t')| ≤ K * |bbar - m t| := by
          rw [abs_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right (hb t') (abs_nonneg _)
        have h3 : |(bbar - m t) * (bbar - m t')|
            ≤ (bbar - m t) ^ 2 / 2 + (bbar - m t') ^ 2 / 2 := by
          rw [abs_mul]
          nlinarith [sq_nonneg (|bbar - m t| - |bbar - m t'|), sq_abs (bbar - m t),
            sq_abs (bbar - m t')]
        rw [abs_le] at h1 h2 h3 ⊢
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
      · simp
    have hf : ∀ t : Fin T, 0 ≤ K * |bbar - m t| + (bbar - m t) ^ 2 / 2 := fun t => by positivity
    have hl := h5_lag_sum_left ℓ (fun t => K * |bbar - m t| + (bbar - m t) ^ 2 / 2) hf
    have hr := h5_lag_sum_right ℓ (fun t => K * |bbar - m t| + (bbar - m t) ^ 2 / 2) hf
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg hTinv]
    calc (1 / (T : ℝ)) * |∑ t : Fin T,
            (∑ t' : Fin T, (if (t : ℕ) + ℓ = (t' : ℕ) then (b t - bbar) * (b t' - bbar) else 0)
              - ∑ t' : Fin T, (if (t : ℕ) + ℓ = (t' : ℕ) then (b t - m t) * (b t' - m t') else 0))|
        ≤ (1 / (T : ℝ)) * ∑ t : Fin T, ∑ t' : Fin T,
            ((if (t : ℕ) + ℓ = (t' : ℕ) then K * |bbar - m t| + (bbar - m t) ^ 2 / 2 else 0)
              + (if (t : ℕ) + ℓ = (t' : ℕ)
                  then K * |bbar - m t'| + (bbar - m t') ^ 2 / 2 else 0)) := by
          refine mul_le_mul_of_nonneg_left ?_ hTinv
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => ?_)
          rw [← Finset.sum_sub_distrib]
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t' _ => hpt t t')
      _ = (1 / (T : ℝ)) * (∑ t : Fin T, ∑ t' : Fin T,
              (if (t : ℕ) + ℓ = (t' : ℕ) then K * |bbar - m t| + (bbar - m t) ^ 2 / 2 else 0)
            + ∑ t : Fin T, ∑ t' : Fin T,
              (if (t : ℕ) + ℓ = (t' : ℕ)
                then K * |bbar - m t'| + (bbar - m t') ^ 2 / 2 else 0)) := by
          simp only [Finset.sum_add_distrib]
      _ ≤ (1 / (T : ℝ)) * (∑ t : Fin T, (K * |bbar - m t| + (bbar - m t) ^ 2 / 2)
            + ∑ t : Fin T, (K * |bbar - m t| + (bbar - m t) ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_left (add_le_add hl hr) hTinv
      _ = 2 * K * ((1 / (T : ℝ)) * ∑ t, |bbar - m t|)
            + (1 / (T : ℝ)) * ∑ t, (bbar - m t) ^ 2 := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
          ring
  have step2 : ((1 / (T : ℝ)) * ∑ t, |bbar - m t|) ^ 2
      ≤ (1 / (T : ℝ)) * ∑ t, (bbar - m t) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin T)))
      (f := fun t => |bbar - m t|)
    simp only [Finset.card_univ, Fintype.card_fin, sq_abs] at h
    rw [mul_pow]
    calc (1 / (T : ℝ)) ^ 2 * (∑ t, |bbar - m t|) ^ 2
        ≤ (1 / (T : ℝ)) ^ 2 * ((T : ℝ) * ∑ t, (bbar - m t) ^ 2) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = (1 / (T : ℝ)) * ∑ t, (bbar - m t) ^ 2 := by
          field_simp
  have step3 : (1 / (T : ℝ)) * ∑ t, (bbar - m t) ^ 2
      ≤ 2 * (bbar - mbar) ^ 2 + 2 * ((1 / (T : ℝ)) * ∑ t, (m t - mbar) ^ 2) := by
    calc (1 / (T : ℝ)) * ∑ t, (bbar - m t) ^ 2
        ≤ (1 / (T : ℝ)) * ∑ t : Fin T, (2 * (bbar - mbar) ^ 2 + 2 * (m t - mbar) ^ 2) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun t _ => ?_) hTinv
          nlinarith [sq_nonneg ((bbar - mbar) + (m t - mbar))]
      _ = 2 * (bbar - mbar) ^ 2 + 2 * ((1 / (T : ℝ)) * ∑ t, (m t - mbar) ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            ← Finset.mul_sum, nsmul_eq_mul]
          field_simp
  have hA1 : (1 / (T : ℝ)) * ∑ t, |bbar - m t|
      ≤ Real.sqrt (2 * (bbar - mbar) ^ 2 + 2 * ((1 / (T : ℝ)) * ∑ t, (m t - mbar) ^ 2)) :=
    (Real.le_sqrt_of_sq_le step2).trans (Real.sqrt_le_sqrt step3)
  refine step1.trans (add_le_add ?_ step3)
  exact mul_le_mul_of_nonneg_left hA1 (by positivity)

/-! ### The HAC difference -/

private lemma h5_nw_abs_le_one (L ℓ : ℕ) (h2 : ℓ ≤ L) : |nwWeight L ℓ| ≤ 1 := by
  unfold nwWeight
  have hL : (0 : ℝ) < (L : ℝ) + 1 := by positivity
  have hl : (ℓ : ℝ) ≤ L := by exact_mod_cast h2
  have h0 : (0 : ℝ) ≤ (ℓ : ℝ) / ((L : ℝ) + 1) := by positivity
  have h1' : (ℓ : ℝ) / ((L : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hL]
    linarith
  rw [abs_le]
  constructor <;> linarith

private lemma h5_hac_diff {S : Type} [Fintype S] [MeasurableSpace S] (E : Env S) {T : ℕ}
    (hT : 0 < T) (k L : ℕ) (ω : Traj S T) (K : ℝ)
    (hb : ∀ t : Fin T, |Bt k t ω - E.meanB T k t| ≤ K) :
    |hacEst T k L ω - E.hacIdeal T k L ω|
      ≤ (2 * (L : ℝ) + 1) *
        (2 * K * Real.sqrt (2 * (Bbar T k ω - (1 / (T : ℝ)) * ∑ s : Fin T, E.meanB T k s) ^ 2
              + 2 * E.cesaroDevSq T k)
          + (2 * (Bbar T k ω - (1 / (T : ℝ)) * ∑ s : Fin T, E.meanB T k s) ^ 2
              + 2 * E.cesaroDevSq T k)) := by
  set c : ℝ := 2 * K * Real.sqrt (2 * (Bbar T k ω - (1 / (T : ℝ)) * ∑ s : Fin T, E.meanB T k s) ^ 2
              + 2 * E.cesaroDevSq T k)
          + (2 * (Bbar T k ω - (1 / (T : ℝ)) * ∑ s : Fin T, E.meanB T k s) ^ 2
              + 2 * E.cesaroDevSq T k) with hc
  have hlag : ∀ ℓ : ℕ, |GammaHat T k ℓ ω - E.GammaIdeal T k ℓ ω| ≤ c := fun ℓ =>
    h5_lag_diff hT ℓ (fun t => Bt k t ω) (fun t => E.meanB T k t) K (Bbar T k ω)
      ((1 / (T : ℝ)) * ∑ s : Fin T, E.meanB T k s) hb
  have hc0 : 0 ≤ c := le_trans (abs_nonneg _) (hlag 0)
  unfold hacEst Env.hacIdeal
  have e : GammaHat T k 0 ω + 2 * ∑ ℓ ∈ Finset.Icc 1 L, nwWeight L ℓ * GammaHat T k ℓ ω
        - (E.GammaIdeal T k 0 ω + 2 * ∑ ℓ ∈ Finset.Icc 1 L, nwWeight L ℓ * E.GammaIdeal T k ℓ ω)
      = (GammaHat T k 0 ω - E.GammaIdeal T k 0 ω)
        + 2 * ∑ ℓ ∈ Finset.Icc 1 L, nwWeight L ℓ * (GammaHat T k ℓ ω - E.GammaIdeal T k ℓ ω) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [e]
  have hsum : |∑ ℓ ∈ Finset.Icc 1 L, nwWeight L ℓ * (GammaHat T k ℓ ω - E.GammaIdeal T k ℓ ω)|
      ≤ (L : ℝ) * c := by
    calc |∑ ℓ ∈ Finset.Icc 1 L, nwWeight L ℓ * (GammaHat T k ℓ ω - E.GammaIdeal T k ℓ ω)|
        ≤ ∑ ℓ ∈ Finset.Icc 1 L, |nwWeight L ℓ * (GammaHat T k ℓ ω - E.GammaIdeal T k ℓ ω)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ℓ ∈ Finset.Icc 1 L, c := by
          refine Finset.sum_le_sum fun ℓ hℓ => ?_
          rw [Finset.mem_Icc] at hℓ
          rw [abs_mul]
          calc |nwWeight L ℓ| * |GammaHat T k ℓ ω - E.GammaIdeal T k ℓ ω|
              ≤ 1 * c := mul_le_mul (h5_nw_abs_le_one L ℓ hℓ.2) (hlag ℓ) (abs_nonneg _) zero_le_one
            _ = c := one_mul c
      _ = (L : ℝ) * c := by simp
  calc |(GammaHat T k 0 ω - E.GammaIdeal T k 0 ω)
          + 2 * ∑ ℓ ∈ Finset.Icc 1 L, nwWeight L ℓ * (GammaHat T k ℓ ω - E.GammaIdeal T k ℓ ω)|
      ≤ |GammaHat T k 0 ω - E.GammaIdeal T k 0 ω|
          + |2 * ∑ ℓ ∈ Finset.Icc 1 L,
              nwWeight L ℓ * (GammaHat T k ℓ ω - E.GammaIdeal T k ℓ ω)| := abs_add_le _ _
    _ ≤ c + 2 * ((L : ℝ) * c) := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        exact add_le_add (hlag 0) (mul_le_mul_of_nonneg_left hsum (by norm_num))
    _ = (2 * (L : ℝ) + 1) * c := by ring

/-! ### Rates -/

private lemma h5_N_bigO (L : ℕ → ℕ) (hL : IsBandwidth L) :
    (fun T : ℕ => (2 * (L T : ℝ) + 1) ^ 2)
      =O[atTop] (fun T : ℕ => ((T : ℝ) ^ ((1 : ℝ) / 3)) ^ 2) := by
  obtain ⟨_, _, hO⟩ := hL
  have h1 : (fun _ : ℕ => (1 : ℝ)) =O[atTop] (fun T : ℕ => (T : ℝ) ^ ((1 : ℝ) / 3)) := by
    refine Asymptotics.IsBigO.of_bound' ?_
    filter_upwards [eventually_ge_atTop 1] with T hT
    have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
    have h : (1 : ℝ) ≤ (T : ℝ) ^ ((1 : ℝ) / 3) := Real.one_le_rpow hT' (by norm_num)
    rw [norm_one, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact h
  exact ((hO.const_mul_left 2).add h1).pow 2

private lemma h5_tendsto_dev {S : Type} [Fintype S] [MeasurableSpace S] (E : Env S) (k : ℕ)
    (L : ℕ → ℕ) (hL : IsBandwidth L) (hstab : E.MeanStability k) :
    Tendsto (fun T : ℕ => (2 * (L T : ℝ) + 1) ^ 2 * E.cesaroDevSq T k) atTop (𝓝 0) := by
  have hstab' : (fun T : ℕ => E.cesaroDevSq T k)
      =o[atTop] (fun T : ℕ => (T : ℝ) ^ (-(2 / 3) : ℝ)) := hstab
  have h := (h5_N_bigO L hL).mul_isLittleO hstab'
  rw [← Asymptotics.isLittleO_one_iff ℝ]
  refine h.trans_eventuallyEq ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  show ((T : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 * (T : ℝ) ^ (-(2 / 3) : ℝ) = 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hT'.le, ← Real.rpow_add hT']
  norm_num

private lemma h5_tendsto_var {S : Type} [Fintype S] [MeasurableSpace S] (E : Env S) (k : ℕ)
    (v : ℝ) (L : ℕ → ℕ) (hL : IsBandwidth L) (hvar : E.AsymptoticVariance k v) :
    Tendsto (fun T : ℕ => (2 * (L T : ℝ) + 1) ^ 2 * E.normVar T k * (T : ℝ)⁻¹) atTop (𝓝 0) := by
  have hv : (fun T : ℕ => E.normVar T k) =O[atTop] (fun _ : ℕ => (1 : ℝ)) :=
    hvar.2.isBigO_one ℝ
  have h := ((h5_N_bigO L hL).mul hv).mul
    (Asymptotics.isBigO_refl (fun T : ℕ => (T : ℝ)⁻¹) atTop)
  refine h.trans_tendsto ?_
  have ht : Tendsto (fun T : ℕ => (T : ℝ) ^ (-(1 / 3) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp tendsto_natCast_atTop_atTop
  refine ht.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  show (T : ℝ) ^ (-(1 / 3) : ℝ) = ((T : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 * 1 * (T : ℝ)⁻¹
  rw [mul_one, ← Real.rpow_natCast, ← Real.rpow_mul hT'.le, ← Real.rpow_neg_one (T : ℝ),
    ← Real.rpow_add hT']
  norm_num

/-! ### Boundedness and measurability of `B_t` -/

private lemma h5_measurable_Bt {S : Type} [Fintype S] [MeasurableSpace S] {T : ℕ} (k : ℕ)
    (t : Fin T) : Measurable (Bt k t : Traj S T → ℝ) := by
  unfold Bt
  refine Finset.measurable_sum _ fun i _ => ?_
  refine Measurable.ite (MeasurableSet.const _) ?_ measurable_const
  have hZ : Measurable (Z i : Traj S T → Bool) := by
    unfold Z
    exact (measurable_pi_apply i).snd.fst
  have hY : Measurable (Y t : Traj S T → ℝ) := by
    unfold Y
    exact (measurable_pi_apply t).snd.snd
  exact ((Measurable.of_discrete (f := ipw)).comp hZ).mul hY

private lemma h5_abs_ipw (z : Bool) : |ipw z| = 2 := by
  unfold ipw
  cases z <;> norm_num

private lemma h5_card_window {T : ℕ} (k : ℕ) (t : Fin T) :
    (Finset.univ.filter
      (fun i : Fin T => (i : ℕ) ≤ (t : ℕ) ∧ (t : ℕ) ≤ (i : ℕ) + k)).card ≤ k + 1 := by
  have h := Finset.card_le_card_of_injOn
    (s := Finset.univ.filter (fun i : Fin T => (i : ℕ) ≤ (t : ℕ) ∧ (t : ℕ) ≤ (i : ℕ) + k))
    (t := Finset.range (k + 1)) (fun i => (t : ℕ) - (i : ℕ)) ?_ ?_
  · simpa using h
  · intro i hi
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi
    simp only [Finset.coe_range, Set.mem_Iio]
    omega
  · intro i hi j hj hij
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi hj
    apply Fin.ext
    simp only at hij
    omega

private lemma h5_abs_Bt_le {S : Type} [Fintype S] {T : ℕ} (k : ℕ) (t : Fin T) (ω : Traj S T)
    (M : ℝ) (hY : |Y t ω| ≤ M) : |Bt k t ω| ≤ 2 * ((k : ℝ) + 1) * |M| := by
  unfold Bt
  calc |∑ i : Fin T, if (i : ℕ) ≤ (t : ℕ) ∧ (t : ℕ) ≤ (i : ℕ) + k
          then ipw (Z i ω) * Y t ω else 0|
      ≤ ∑ i : Fin T, |if (i : ℕ) ≤ (t : ℕ) ∧ (t : ℕ) ≤ (i : ℕ) + k
          then ipw (Z i ω) * Y t ω else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin T, if (i : ℕ) ≤ (t : ℕ) ∧ (t : ℕ) ≤ (i : ℕ) + k then 2 * |M| else 0 := by
        refine Finset.sum_le_sum fun i _ => ?_
        split_ifs
        · rw [abs_mul, h5_abs_ipw]
          have := le_abs_self M
          linarith
        · simp
    _ = ((Finset.univ.filter
          (fun i : Fin T => (i : ℕ) ≤ (t : ℕ) ∧ (t : ℕ) ≤ (i : ℕ) + k)).card : ℝ) * (2 * |M|) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((k : ℝ) + 1) * (2 * |M|) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast h5_card_window k t
    _ = 2 * ((k : ℝ) + 1) * |M| := by ring

/-! ### Elementary arithmetic behind the choice of thresholds -/

private lemma h5_arith (N K V c η : ℝ) (hN1 : 1 ≤ N) (hK0 : 0 ≤ K) (hc : 0 ≤ c)
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hV : |V| < η / (2 * N))
    (hdev : N ^ 2 * (2 * c) < η ^ 2 / 2) :
    N * (2 * K * Real.sqrt (2 * V ^ 2 + 2 * c) + (2 * V ^ 2 + 2 * c)) < (2 * K + 1) * η := by
  have hNpos : 0 < N := by linarith
  have hQ0 : 0 ≤ 2 * V ^ 2 + 2 * c := by positivity
  have hVsq : N ^ 2 * (2 * V ^ 2) < η ^ 2 / 2 := by
    have h1 : V ^ 2 < (η / (2 * N)) ^ 2 := by
      rw [← sq_abs V]
      exact pow_lt_pow_left₀ hV (abs_nonneg _) (by norm_num)
    have h2 : N ^ 2 * (2 * (η / (2 * N)) ^ 2) = η ^ 2 / 2 := by
      field_simp
    have hN2 : 0 < N ^ 2 := by positivity
    calc N ^ 2 * (2 * V ^ 2) < N ^ 2 * (2 * (η / (2 * N)) ^ 2) :=
          mul_lt_mul_of_pos_left (by linarith) hN2
      _ = η ^ 2 / 2 := h2
  have hNQ : N ^ 2 * (2 * V ^ 2 + 2 * c) < η ^ 2 := by linarith
  generalize 2 * V ^ 2 + 2 * c = Q at hQ0 hNQ ⊢
  have hsqrt : N * Real.sqrt Q < η := by
    have h1 : Real.sqrt Q < η / N := by
      rw [Real.sqrt_lt' (by positivity), div_pow, lt_div_iff₀ (by positivity)]
      linarith
    calc N * Real.sqrt Q < N * (η / N) := mul_lt_mul_of_pos_left h1 hNpos
      _ = η := by field_simp
  have hNQ' : N * Q < η := by
    have h1 : N * Q ≤ N ^ 2 * Q := by
      calc N * Q = 1 * (N * Q) := (one_mul _).symm
        _ ≤ N * (N * Q) := mul_le_mul_of_nonneg_right hN1 (mul_nonneg hNpos.le hQ0)
        _ = N ^ 2 * Q := by ring
    have h2 : η ^ 2 ≤ η := by
      calc η ^ 2 = η * η := sq η
        _ ≤ 1 * η := mul_le_mul_of_nonneg_right hη1 hη0.le
        _ = η := one_mul η
    linarith
  have h1 : 2 * K * (N * Real.sqrt Q) ≤ 2 * K * η :=
    mul_le_mul_of_nonneg_left hsqrt.le (by positivity)
  calc N * (2 * K * Real.sqrt Q + Q) = 2 * K * (N * Real.sqrt Q) + N * Q := by ring
    _ < 2 * K * η + η := add_lt_add_of_le_of_lt h1 hNQ'
    _ = (2 * K + 1) * η := by ring

/-! ### The probability bound at a fixed horizon -/

private lemma h5_prob_bound {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (k : ℕ) (M : ℝ) (hM : E.RewardBound M) {T : ℕ} (hT : 0 < T) (L : ℕ) (ε η : ℝ)
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hηε : (2 * (4 * ((k : ℝ) + 1) * |M|) + 1) * η ≤ ε)
    (hdev : (2 * (L : ℝ) + 1) ^ 2 * (2 * E.cesaroDevSq T k) < η ^ 2 / 2) :
    (E.expLaw T (1 / 2)) {ω | ε ≤ |hacEst T k L ω - E.hacIdeal T k L ω - 0|}
      ≤ ENNReal.ofReal (4 / η ^ 2 * ((2 * (L : ℝ) + 1) ^ 2 * E.normVar T k * (T : ℝ)⁻¹)) := by
  have hprob : IsProbabilityMeasure (E.expLaw T (1 / 2)) :=
    TPG.isProbabilityMeasure_trajLaw E T (fun _ => 1 / 2) (fun _ => by norm_num)
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hY : ∀ᵐ ω ∂(E.expLaw T (1 / 2)), ∀ t : Fin T, |Y t ω| ≤ M :=
    TPG.ae_abs_Y_le E T (fun _ => 1 / 2) M hM
  have hB : ∀ᵐ ω ∂(E.expLaw T (1 / 2)), ∀ t : Fin T, |Bt k t ω| ≤ 2 * ((k : ℝ) + 1) * |M| :=
    hY.mono fun ω h t => h5_abs_Bt_le k t ω M (h t)
  have hBint : ∀ t : Fin T, Integrable (Bt k t) (E.expLaw T (1 / 2)) := fun t =>
    Integrable.of_bound (h5_measurable_Bt k t).aestronglyMeasurable (2 * ((k : ℝ) + 1) * |M|)
      (hB.mono fun ω h => by rw [Real.norm_eq_abs]; exact h t)
  have hmean : ∀ t : Fin T, |E.meanB T k t| ≤ 2 * ((k : ℝ) + 1) * |M| := by
    intro t
    have h := norm_integral_le_of_norm_le_const (μ := E.expLaw T (1 / 2)) (f := Bt k t)
      (C := 2 * ((k : ℝ) + 1) * |M|) (hB.mono fun ω h => by rw [Real.norm_eq_abs]; exact h t)
    rw [probReal_univ, mul_one, Real.norm_eq_abs] at h
    exact h
  have hV : ∀ᵐ ω ∂(E.expLaw T (1 / 2)), ∀ t : Fin T,
      |Bt k t ω - E.meanB T k t| ≤ 4 * ((k : ℝ) + 1) * |M| :=
    hB.mono fun ω h t => by
      have h1 := abs_sub (Bt k t ω) (E.meanB T k t)
      linarith [h t, hmean t]
  have hSmeas : Measurable (fun ω : Traj S T => ∑ t : Fin T, Bt k t ω) :=
    Finset.measurable_sum _ fun t _ => h5_measurable_Bt k t
  have hSLp : MemLp (fun ω : Traj S T => ∑ t : Fin T, Bt k t ω) 2 (E.expLaw T (1 / 2)) :=
    MemLp.of_bound hSmeas.aestronglyMeasurable ((T : ℝ) * (2 * ((k : ℝ) + 1) * |M|))
      (hB.mono fun ω h => by
        rw [Real.norm_eq_abs]
        calc |∑ t : Fin T, Bt k t ω| ≤ ∑ t : Fin T, |Bt k t ω| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _t : Fin T, 2 * ((k : ℝ) + 1) * |M| := Finset.sum_le_sum fun t _ => h t
          _ = (T : ℝ) * (2 * ((k : ℝ) + 1) * |M|) := by simp)
  have hSint : ∫ ω, (∑ t : Fin T, Bt k t ω) ∂(E.expLaw T (1 / 2))
      = ∑ t : Fin T, E.meanB T k t := by
    rw [integral_finsetSum _ fun t _ => hBint t]
    rfl
  have hvarS : variance (fun ω : Traj S T => ∑ t : Fin T, Bt k t ω) (E.expLaw T (1 / 2))
      = (T : ℝ) * E.normVar T k := by
    unfold Env.normVar
    field_simp
  have hN1 : (1 : ℝ) ≤ 2 * (L : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
    linarith
  have hNpos : (0 : ℝ) < 2 * (L : ℝ) + 1 := by linarith
  have hcpos : 0 < (T : ℝ) * (η / (2 * (2 * (L : ℝ) + 1))) := by positivity
  have hcheb := meas_ge_le_variance_div_sq hSLp hcpos
  rw [hSint, hvarS] at hcheb
  have hrhs : (T : ℝ) * E.normVar T k / ((T : ℝ) * (η / (2 * (2 * (L : ℝ) + 1)))) ^ 2
      = 4 / η ^ 2 * ((2 * (L : ℝ) + 1) ^ 2 * E.normVar T k * (T : ℝ)⁻¹) := by
    field_simp
    ring
  rw [hrhs] at hcheb
  refine le_trans (measure_mono_ae ?_) hcheb
  have hces0 : 0 ≤ E.cesaroDevSq T k := by
    unfold Env.cesaroDevSq
    positivity
  have himp : ∀ᵐ ω ∂(E.expLaw T (1 / 2)),
      ω ∈ {ω : Traj S T | ε ≤ |hacEst T k L ω - E.hacIdeal T k L ω - 0|} →
      ω ∈ {ω : Traj S T | (T : ℝ) * (η / (2 * (2 * (L : ℝ) + 1)))
          ≤ |∑ t : Fin T, Bt k t ω - ∑ t : Fin T, E.meanB T k t|} := by
    filter_upwards [hV] with ω hω hε
    simp only [sub_zero] at hε ⊢
    by_contra hcon
    rw [not_le] at hcon
    have hbound := h5_hac_diff E hT k L ω (4 * ((k : ℝ) + 1) * |M|) hω
    have hVabs : |Bbar T k ω - (1 / (T : ℝ)) * ∑ s : Fin T, E.meanB T k s|
        < η / (2 * (2 * (L : ℝ) + 1)) := by
      have hVeq : Bbar T k ω - (1 / (T : ℝ)) * ∑ s : Fin T, E.meanB T k s
          = (1 / (T : ℝ)) * (∑ t : Fin T, Bt k t ω - ∑ t : Fin T, E.meanB T k t) := by
        unfold Bbar
        ring
      rw [hVeq, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (T : ℝ))]
      calc 1 / (T : ℝ) * |∑ t : Fin T, Bt k t ω - ∑ t : Fin T, E.meanB T k t|
          < 1 / (T : ℝ) * ((T : ℝ) * (η / (2 * (2 * (L : ℝ) + 1)))) :=
            mul_lt_mul_of_pos_left hcon (by positivity)
        _ = η / (2 * (2 * (L : ℝ) + 1)) := by field_simp
    have hfin := h5_arith (2 * (L : ℝ) + 1) (4 * ((k : ℝ) + 1) * |M|)
      (Bbar T k ω - (1 / (T : ℝ)) * ∑ s : Fin T, E.meanB T k s) (E.cesaroDevSq T k) η
      hN1 (by positivity) hces0 hη0 hη1 hVabs hdev
    linarith
  exact himp

/-! ### Main statement -/

theorem solution {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (k : ℕ) (γ M v : ℝ) (L : ℕ → ℕ)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hmix : ∀ T : ℕ, E.Mixing T γ) (hM : E.RewardBound M)
    (hvar : E.AsymptoticVariance k v) (hstab : E.MeanStability k) (hL : IsBandwidth L) :
    E.TendstoInProb
      (fun (T : ℕ) (ω : Traj S T) => hacEst T k (L T) ω - E.hacIdeal T k (L T) ω) 0 := by
  intro ε hε
  have hKnn : (0 : ℝ) ≤ 4 * ((k : ℝ) + 1) * |M| := by positivity
  have hK1 : (0 : ℝ) < 2 * (4 * ((k : ℝ) + 1) * |M|) + 1 := by linarith
  set η : ℝ := min 1 (ε / (2 * (4 * ((k : ℝ) + 1) * |M|) + 1)) with hη
  have hη0 : 0 < η := lt_min one_pos (div_pos hε hK1)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : (2 * (4 * ((k : ℝ) + 1) * |M|) + 1) * η ≤ ε := by
    have h : η ≤ ε / (2 * (4 * ((k : ℝ) + 1) * |M|) + 1) := min_le_right _ _
    rw [le_div_iff₀ hK1] at h
    linarith
  have hdev := h5_tendsto_dev E k L hL hstab
  have hvarT := h5_tendsto_var E k v L hL hvar
  have hdev' : ∀ᶠ T : ℕ in atTop,
      (2 * (L T : ℝ) + 1) ^ 2 * (2 * E.cesaroDevSq T k) < η ^ 2 / 2 := by
    have h : ∀ᶠ T : ℕ in atTop, (2 * (L T : ℝ) + 1) ^ 2 * E.cesaroDevSq T k < η ^ 2 / 4 :=
      hdev.eventually (gt_mem_nhds (by positivity))
    filter_upwards [h] with T hT
    linarith
  have hup : Tendsto (fun T : ℕ => ENNReal.ofReal
      (4 / η ^ 2 * ((2 * (L T : ℝ) + 1) ^ 2 * E.normVar T k * (T : ℝ)⁻¹))) atTop (𝓝 0) := by
    have h0 := ENNReal.tendsto_ofReal (hvarT.const_mul (4 / η ^ 2))
    rw [mul_zero, ENNReal.ofReal_zero] at h0
    exact h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun T => zero_le) ?_
  filter_upwards [hdev', eventually_gt_atTop 0] with T hT1 hT0
  exact h5_prob_bound E k M hM hT0 (L T) ε η hη0 hη1 hηε hT1
