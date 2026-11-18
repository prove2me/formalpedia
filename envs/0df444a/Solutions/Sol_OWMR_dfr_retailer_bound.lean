-- Prove2me | solution 1 for OWMR.dfr_retailer_bound
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T09:57:52.733956+00:00
-- url     : https://prove2.me/submissions/346a510c-6767-4694-8e2b-331c63615625

import Definitions.Def_owmr_dfr_policy
import Theorems.Thm_OWMR_renewal_concave_dfr
import Theorems.Thm_OWMR_dfr_mirror_bound
import Theorems.Thm_OWMR_dfr_window_contraction
import Theorems.Thm_OWMR_ss_renewal_reward
import Theorems.Thm_OWMR_canonical_width_bound
import Theorems.Thm_OWMR_renewalMeasure_Ico_lt_top
import Theorems.Thm_OWMR_F_properties
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Order.Filter.ENNReal
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Retailer bound of Theorem D.1 (Steps 1-3 of its proof): every retailer policy selected by
Definition D.1 has augmented cost at most `(1 + θλ) J_i(K_i/θ)`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open OWMR

noncomputable section

namespace DFRRet

section coord
variable {α : Type} [MeasurableSpace α] [Zero α]
lemma measurable_padHist' (N : ℕ) : Measurable (padHist N : (Fin N → α) → ℕ → α) := by
  refine measurable_pi_lambda _ fun t => ?_
  by_cases h : t < N
  · simp only [padHist, dif_pos h]
    exact measurable_pi_apply _
  · simp only [padHist, dif_neg h]
    exact measurable_const
end coord

lemma ssPre_SS_le (S : ℝ) (d : ℕ → ℝ≥0) : ∀ t, ssPre S S d t ≤ S
  | 0 => le_rfl
  | t + 1 => by
    show (if ssPre S S d t ≤ S then S else ssPre S S d t) - (d t : ℝ) ≤ S
    rw [if_pos (ssPre_SS_le S d t)]
    linarith [NNReal.coe_nonneg (d t)]

lemma ssPeriodCost_SS (f : ℝ → ℝ) (K S : ℝ) (d : ℕ → ℝ≥0) (t : ℕ) :
    ssPeriodCost f K S S d t
      = (if t = 0 then 0 else K * (if 0 < d (t - 1) then 1 else 0)) + f S := by
  unfold ssPeriodCost ssPost
  rw [if_pos (ssPre_SS_le S d t)]
  cases t with
  | zero => simp [ssPre]
  | succ t =>
    have h : ssPre S S d (t + 1) = S - (d t : ℝ) := by
      show (if ssPre S S d t ≤ S then S else ssPre S S d t) - (d t : ℝ) = _
      rw [if_pos (ssPre_SS_le S d t)]
    rw [h, if_neg (Nat.succ_ne_zero t), add_tsub_cancel_right]
    congr 2
    by_cases hd : 0 < d t
    · have : (0 : ℝ) < (d t : ℝ) := by exact_mod_cast hd
      rw [if_pos ⟨by linarith, by linarith⟩, if_pos hd]
    · have : (d t : ℝ) = 0 := by
        have := le_antisymm (not_lt.1 hd) zero_le
        exact_mod_cast this
      rw [if_neg (by rw [this]; simp), if_neg hd]

/-- The long-run average cost of the base-stock policy `(S,S)`. -/
lemma ss_avg_SS (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (f : ℝ → ℝ) (hf0 : ∀ y, 0 ≤ f y)
    (K S : ℝ) (hK : 0 ≤ K) :
    ssAvgCost ρ f K S S = ENNReal.ofReal (f S + K * (ρ (Set.Ioi 0)).toReal) := by
  set r := (ρ (Set.Ioi 0)).toReal with hr
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  have hint : ∫ a, (K * (if 0 < a then 1 else 0) + f S) ∂ρ = K * r + f S := by
    have h1 : (fun a : ℝ≥0 => K * (if 0 < a then (1 : ℝ) else 0) + f S)
        = fun a => K * (Set.Ioi (0 : ℝ≥0)).indicator 1 a + f S := by
      funext a
      by_cases ha : 0 < a
      · simp [Set.indicator_of_mem (show a ∈ Set.Ioi 0 from ha), ha]
      · simp [Set.indicator_of_notMem (show a ∉ Set.Ioi 0 from ha), ha]
    have hi1 : Integrable ((Set.Ioi (0 : ℝ≥0)).indicator (1 : ℝ≥0 → ℝ)) ρ :=
      (integrable_const (1 : ℝ)).indicator measurableSet_Ioi
    rw [h1, integral_add (f := fun a => K * (Set.Ioi (0 : ℝ≥0)).indicator (1 : ℝ≥0 → ℝ) a)
      (hi1.const_mul K) (integrable_const _), integral_const_mul,
      integral_indicator_one measurableSet_Ioi, integral_const, probReal_univ, one_smul,
      measureReal_def]
  have hE : ∀ T t, t < T →
      ∫⁻ z, ENNReal.ofReal (ssPeriodCost f K S S (padHist T z) t) ∂(Measure.pi fun _ : Fin T => ρ)
        = ENNReal.ofReal ((if t = 0 then 0 else K * r) + f S) := by
    intro T t ht
    simp_rw [ssPeriodCost_SS]
    rcases t with _ | t
    · simp
    · have hcoord : ∀ z : Fin T → ℝ≥0, padHist T z t = z ⟨t, by omega⟩ := fun z => by
        simp [padHist, show t < T by omega]
      simp only [Nat.succ_ne_zero, if_false, add_tsub_cancel_right, hcoord]
      have hmp := measurePreserving_eval (fun _ : Fin T => ρ) (⟨t, by omega⟩ : Fin T)
      have hm : Measurable fun a : ℝ≥0 => ENNReal.ofReal (K * (if 0 < a then 1 else 0) + f S) :=
        ENNReal.measurable_ofReal.comp ((measurable_const.mul (Measurable.ite measurableSet_Ioi
          measurable_const measurable_const)).add measurable_const)
      rw [hmp.lintegral_comp hm, ← ofReal_integral_eq_lintegral_ofReal, hint]
      · refine Integrable.of_bound (C := K + f S) ((measurable_const.mul (Measurable.ite
          (measurableSet_lt measurable_const measurable_id) measurable_const
          measurable_const)).add measurable_const).aestronglyMeasurable (ae_of_all _ fun a => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (by have := hf0 S; split_ifs <;> nlinarith)]
        split_ifs <;> linarith
      · exact ae_of_all _ fun a => by
          simp only [Pi.zero_apply]; have := hf0 S; split_ifs <;> nlinarith
  have havg : ∀ T : ℕ, ((T + 1 : ℕ) : ℝ≥0∞)⁻¹ * ∫⁻ z, ∑ t ∈ Finset.range (T + 1),
      ENNReal.ofReal (ssPeriodCost f K S S (padHist (T + 1) z) t) ∂(Measure.pi fun _ : Fin (T + 1) => ρ)
        = ENNReal.ofReal (f S + K * r * ((T : ℝ) / ((T : ℝ) + 1))) := by
    intro T
    rw [lintegral_finsetSum]
    · rw [Finset.sum_congr rfl fun t ht => hE (T + 1) t (Finset.mem_range.1 ht),
        ← ENNReal.ofReal_sum_of_nonneg (fun t _ => by have := hf0 S; split_ifs <;> nlinarith)]
      have hsum : ∑ t ∈ Finset.range (T + 1), ((if t = 0 then 0 else K * r) + f S)
          = (T : ℝ) * (K * r) + ((T : ℝ) + 1) * f S := by
        rw [Finset.sum_range_succ']
        simp only [Nat.succ_ne_zero, if_false, if_true, zero_add, Finset.sum_add_distrib,
          Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
      rw [hsum]
      have hT : (0 : ℝ) < (T : ℝ) + 1 := by positivity
      rw [show ((T + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((T : ℝ) + 1) by
          rw [← ENNReal.ofReal_natCast]; push_cast; rfl,
        ← ENNReal.ofReal_inv_of_pos hT, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
      ring
    · intro t _
      exact ENNReal.measurable_ofReal.comp (by
        have hp := measurable_padHist' (α := ℝ≥0) (T + 1)
        simp_rw [ssPeriodCost_SS]
        refine Measurable.add ?_ measurable_const
        split_ifs
        · exact measurable_const
        · exact measurable_const.mul (Measurable.ite
            (measurableSet_lt measurable_const ((measurable_pi_apply (t - 1)).comp hp))
            measurable_const measurable_const))
  have hlim : Tendsto (fun T : ℕ => ENNReal.ofReal (f S + K * r * ((T : ℝ) / ((T : ℝ) + 1))))
      atTop (𝓝 (ENNReal.ofReal (f S + K * r))) := by
    refine ENNReal.tendsto_ofReal ?_
    have := (tendsto_natCast_div_add_atTop (1 : ℝ)).const_mul (K * r)
    simpa using this.const_add (f S)
  unfold ssAvgCost
  refine Tendsto.limsup_eq ?_
  rw [← tendsto_add_atTop_iff_nat 1]
  refine hlim.congr fun T => ?_
  rw [havg T]

lemma ssPre_SS_bound (S : ℝ) (d : ℕ → ℝ≥0) : ∀ t, ssPre S S d t ≤ S
  | 0 => le_rfl
  | t + 1 => by
    have ih := ssPre_SS_bound S d t
    show (if ssPre S S d t ≤ S then S else ssPre S S d t) - (d t : ℝ) ≤ S
    rw [if_pos ih]
    linarith [NNReal.coe_nonneg (d t)]

/-- With `s = S = a` the mirror loss vanishes. -/
lemma mirrorAvg_SS (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (h p S : ℝ) :
    mirrorAvg ρ h p S S S = 0 := by
  have e : ∀ T (z : Fin T → ℝ≥0) t,
      ENNReal.ofReal (whLoss h p (S - ssPost S S (padHist T z) t)) = 0 := by
    intro T z t
    have : ssPost S S (padHist T z) t = S := if_pos (ssPre_SS_bound S _ t)
    rw [this, sub_self]
    simp [whLoss]
  simp [mirrorAvg, e]


end DFRRet

namespace DFRRet

lemma renewalM_eq (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (w : ℝ) :
    renewalM ρ w = renewalMeasure ρ (Set.Ico 0 w) := by
  unfold renewalM renewalMeasure
  rw [Measure.sum_apply _ measurableSet_Ico]
  refine tsum_congr fun k => ?_
  rw [Measure.map_apply (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).coe_nnreal_real)
    measurableSet_Ico]
  congr 1
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ico]
  constructor
  · intro h; exact ⟨Finset.sum_nonneg fun j _ => NNReal.coe_nonneg _, h⟩
  · exact fun h => h.2

lemma one_le_renewal (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (w : ℝ) (hw : 0 < w) :
    1 ≤ renewalMeasure ρ (Set.Ico 0 w) := by
  unfold renewalMeasure
  refine le_trans ?_ (Measure.le_iff'.1 (Measure.le_sum _ 0) _)
  rw [Measure.map_apply (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).coe_nnreal_real)
    measurableSet_Ico]
  have : (fun z : Fin 0 → ℝ≥0 => ∑ j, (z j : ℝ)) ⁻¹' Set.Ico 0 w = Set.univ := by
    ext z
    simp [hw]
  rw [this, measure_univ]

lemma renewalM_nonpos (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] {w : ℝ} (hw : w ≤ 0) :
    renewalM ρ w = 0 := by
  rw [renewalM_eq]
  rw [Set.Ico_eq_empty (not_lt.2 hw), measure_empty]

lemma renewalM_mono (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] {a b : ℝ} (hab : a ≤ b) :
    renewalM ρ a ≤ renewalM ρ b := by
  rw [renewalM_eq, renewalM_eq]
  exact measure_mono (Set.Ico_subset_Ico_right hab)

/-- `U{0} = 1/ℙ(D > 0)`. -/
lemma renewal_zero_atom (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] :
    renewalMeasure ρ {0} = (ρ (Set.Ioi 0))⁻¹ := by
  unfold renewalMeasure
  rw [Measure.sum_apply _ (measurableSet_singleton 0)]
  have hk : ∀ k : ℕ, ((Measure.pi fun _ : Fin k => ρ).map fun z => ∑ j, (z j : ℝ)) {0}
      = ρ {0} ^ k := by
    intro k
    rw [Measure.map_apply (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).coe_nnreal_real)
      (measurableSet_singleton 0)]
    have hset : (fun z : Fin k → ℝ≥0 => ∑ j, (z j : ℝ)) ⁻¹' {0}
        = Set.pi Set.univ fun _ => ({0} : Set ℝ≥0) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, true_implies]
      constructor
      · intro h j
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => NNReal.coe_nonneg (z j))).1 h j
          (Finset.mem_univ j)
        exact_mod_cast this
      · intro h
        exact Finset.sum_eq_zero fun j _ => by rw [h j]; rfl
    rw [hset, Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp_rw [hk]
  rw [ENNReal.tsum_geometric]
  congr 1
  have hc : ({0} : Set ℝ≥0)ᶜ = Set.Ioi 0 := by
    ext z; simp [pos_iff_ne_zero]
  rw [← hc, prob_compl_eq_one_sub (measurableSet_singleton 0)]

/-- A single-location value is at least any lower bound of the cost function. -/
lemma sl_ge (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (f : ℝ → ℝ) (K c : ℝ) (hK : 0 ≤ K)
    (hf : ∀ y, c ≤ f y) : ENNReal.ofReal c ≤ slValue ρ f K := by
  unfold slValue
  refine le_iInf fun U => le_iInf fun _ => le_iInf fun ν => le_iInf fun _ => le_iInf fun q =>
    le_iInf fun hq => ?_
  unfold slAvgCost
  refine Filter.le_limsup_of_frequently_le ((Filter.eventually_ge_atTop 1).mono fun T hT => ?_).frequently ?_
  · have hle : ∀ ω : U × (Fin T → ℝ≥0), (T : ℝ≥0∞) * ENNReal.ofReal c
        ≤ ∑ t ∈ Finset.range T, ENNReal.ofReal (slPeriodCost f K 0 q ω.1 (padHist T ω.2) t) := by
      intro ω
      rw [show (T : ℝ≥0∞) * ENNReal.ofReal c = ∑ t ∈ Finset.range T, ENNReal.ofReal c by simp]
      refine Finset.sum_le_sum fun t _ => ENNReal.ofReal_le_ofReal ?_
      unfold slPeriodCost
      have := hf (slPos 0 q ω.1 (padHist T ω.2) t)
      have : 0 ≤ K * (if 0 < q t ω.1 (padHist T ω.2) then 1 else 0) := by
        split_ifs <;> simp [hK]
      linarith
    haveI : IsProbabilityMeasure (ν.prod (Measure.pi fun _ : Fin T => ρ)) := by infer_instance
    have hT0 : (T : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show T ≠ 0 by omega)
    calc ENNReal.ofReal c = (T : ℝ≥0∞)⁻¹ * ((T : ℝ≥0∞) * ENNReal.ofReal c) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hT0 (ENNReal.natCast_ne_top T), one_mul]
      _ = (T : ℝ≥0∞)⁻¹ * ∫⁻ _ω, (T : ℝ≥0∞) * ENNReal.ofReal c
            ∂(ν.prod (Measure.pi fun _ : Fin T => ρ)) := by
          rw [lintegral_const, measure_univ, mul_one]
      _ ≤ _ := by gcongr with ω; exact hle ω
  · isBoundedDefault

end DFRRet

namespace DFRRet

lemma bdd_of_cont {φ : ℝ → ℝ} (hφ : Continuous φ) (c e : ℝ) :
    ∃ C, ∀ y ∈ Set.Icc c e, φ y ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := c) (b := e)).exists_bound_of_continuousOn hφ.continuousOn
  exact ⟨C, fun y hy => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC y hy)⟩

/-- AM-GM step of Step 2. -/
lemma amgm {z m θ : ℝ} (hz : 0 < z) (hm : 0 < m) (hθ : 0 < θ) :
    z / Real.sqrt (z / m) + Real.sqrt (z / m) * m ≤ z / θ + θ * m := by
  set s := Real.sqrt (z / m) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (div_pos hz hm)
  have hs2 : s ^ 2 = z / m := Real.sq_sqrt (div_pos hz hm).le
  have hz' : z = s ^ 2 * m := by rw [hs2]; field_simp
  rw [hz']
  have e1 : s ^ 2 * m / s = s * m := by field_simp
  rw [e1]
  have : 0 ≤ (s - θ) ^ 2 * m / θ := by positivity
  have e2 : s ^ 2 * m / θ + θ * m - (s * m + s * m) = (s - θ) ^ 2 * m / θ := by field_simp; ring
  linarith

lemma lambda_nonneg : 0 ≤ dfrLambda := by
  unfold dfrLambda
  have h := Real.sqrt_le_sqrt (show (2 : ℝ) ≤ 4 by norm_num)
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h
  linarith

/-- The mirror ratio `1/(1 + √(p/(p+h))) ≤ λ` and the width bound combine to `m ≤ λ j`. -/
lemma mirror_ratio {h p H wh j mm : ℝ} (hh : 0 < h) (hp : h ≤ p) (hH : h ≤ H) (hj0 : 0 ≤ j)
    (hwh : h * p / (h + p) * wh ≤ h * (H + p) / (H * (h + p)) * j)
    (hmm : mm ≤ p * (1 - Real.sqrt (p / (p + h))) * wh) : mm ≤ dfrLambda * j := by
  have hp0 : 0 < p := lt_of_lt_of_le hh hp
  have hH0 : 0 < H := lt_of_lt_of_le hh hH
  have hhp : 0 < h + p := by linarith
  set σ := Real.sqrt (p / (p + h)) with hσ
  have hpph : 0 < p / (p + h) := div_pos hp0 (by linarith)
  have hσ0 : 0 < σ := Real.sqrt_pos.2 hpph
  have hσsq : σ ^ 2 = p / (p + h) := Real.sq_sqrt hpph.le
  have hσ1 : σ < 1 := by
    have : p / (p + h) < 1 := by rw [div_lt_one (by linarith)]; linarith
    nlinarith
  -- width bound
  have hwj : wh ≤ (H + p) / (H * p) * j := by
    have h1 : 0 < h * p / (h + p) := by positivity
    have e : h * (H + p) / (H * (h + p)) * j / (h * p / (h + p)) = (H + p) / (H * p) * j := by
      field_simp
    rw [← e, le_div_iff₀ h1]
    linarith
  -- `1/(1+σ) ≤ λ`
  have hσ2 : Real.sqrt 2 / 2 ≤ σ := by
    have : (1 : ℝ) / 2 ≤ p / (p + h) := by rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
    have h2 := Real.sqrt_le_sqrt this
    rw [hσ.symm] at h2
    have : Real.sqrt (1 / 2) = Real.sqrt 2 / 2 := by
      rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 1), Real.sqrt_one]
      field_simp
      rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    linarith
  have hsq2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hlam : 1 ≤ dfrLambda * (1 + σ) := by
    unfold dfrLambda
    have h3 : 0 ≤ 2 - Real.sqrt 2 := by
      have := lambda_nonneg; unfold dfrLambda at this; exact this
    nlinarith [mul_le_mul_of_nonneg_left hσ2 h3]
  have hs2 : σ ^ 2 * (h + p) = p := by rw [hσsq]; field_simp; ring
  have hkey : p * (1 - σ) * ((H + p) / (H * p)) ≤ 1 / (1 + σ) := by
    have k1 : p * (1 - σ) * ((H + p) / (H * p)) = (1 - σ) * (H + p) / H := by
      field_simp
    have k2 : (1 - σ) * (H + p) / H ≤ (1 - σ) * (h + p) / h := by
      rw [div_le_div_iff₀ hH0 hh]
      have : 0 ≤ (1 - σ) * p * (H - h) := mul_nonneg (mul_nonneg (by linarith) hp0.le) (by linarith)
      nlinarith
    have k3 : (1 - σ) * (h + p) / h = 1 / (1 + σ) := by
      rw [div_eq_div_iff (ne_of_gt hh) (by linarith)]
      nlinarith [hs2]
    rw [k1]; linarith
  have h1 : mm ≤ p * (1 - σ) * ((H + p) / (H * p) * j) :=
    hmm.trans (mul_le_mul_of_nonneg_left hwj (mul_nonneg hp0.le (by linarith)))
  have h2 : p * (1 - σ) * ((H + p) / (H * p) * j) ≤ 1 / (1 + σ) * j := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hkey hj0
  have h3 : 1 / (1 + σ) * j ≤ dfrLambda * j := by
    refine mul_le_mul_of_nonneg_right ?_ hj0
    rw [div_le_iff₀ (by linarith)]
    linarith
  linarith

end DFRRet

set_option maxHeartbeats 1000000 in
open DFRRet in
theorem solution {n : ℕ} (N : Network n) (hN : N.Standing) (θ : ℝ) (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1) (c : FIFOChoice n) (hc : IsDFRChoice N θ c) (i : Fin n)
    (hH : N.h ≤ N.H i) (hp : N.h ≤ N.p) (hD : 0 < N.K i → N.DFRPositive i) :
    c.s i ≤ c.S i ∧
      ssAvgCost (N.marginal i) (N.F i) (N.K i) (c.s i) (c.S i)
          + mirrorAvg (N.marginal i) N.h N.p (c.s i) (c.S i) (c.a i)
        ≤ ENNReal.ofReal (1 + θ * dfrLambda) * N.J i (N.K i / θ) := by
  set ρ := N.marginal i with hρdef
  have hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ := by
    rw [hρdef]; unfold Network.marginal
    rw [lintegral_map measurable_coe_nnreal_ennreal (measurable_pi_apply i)]
    exact hN.mean_pos i
  have hF := F_properties N hN i
  have hFc : Continuous (N.F i) := by
    rw [Metric.continuous_iff]
    intro b ε hε
    have hHp : 0 < N.H i + N.p + 1 := by linarith [hN.H_pos i, hN.p_pos]
    refine ⟨ε / (N.H i + N.p + 1), by positivity, fun a hab => ?_⟩
    rw [Real.dist_eq] at hab ⊢
    calc |N.F i a - N.F i b| ≤ (N.H i + N.p) * |a - b| := hF.2.2.1 a b
      _ ≤ (N.H i + N.p) * (ε / (N.H i + N.p + 1)) :=
          mul_le_mul_of_nonneg_left hab.le (by linarith [hN.H_pos i, hN.p_pos])
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ hHp]
          nlinarith [hN.H_pos i, hN.p_pos]
  have hlam0 := lambda_nonneg
  have hcoef : 1 ≤ 1 + θ * dfrLambda := by nlinarith
  have hK0 := hN.K_nonneg i
  rcases hK0.lt_or_eq with hK | hK
  swap
  · -- zero setup cost: base stock at a minimizer of `F`
    obtain ⟨hsS, hmin, ha⟩ := hc.1 i hK.symm
    refine ⟨hsS.le, ?_⟩
    rw [hsS, ha, mirrorAvg_SS, add_zero, ss_avg_SS ρ (N.F i) hF.1 _ _ hK0, ← hK, zero_mul,
      add_zero, zero_div]
    calc ENNReal.ofReal (N.F i (c.S i)) ≤ N.J i 0 := sl_ge ρ (N.F i) 0 _ le_rfl hmin
      _ ≤ ENNReal.ofReal (1 + θ * dfrLambda) * N.J i 0 := by
          conv_lhs => rw [← one_mul (N.J i 0)]
          gcongr
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal hcoef
  -- positive setup cost
  obtain ⟨sh, Sh, hcan, hT1, hTlow, hTwin⟩ := hc.2.1 i hK
  have hcan' := hcan
  obtain ⟨hsSh, hJ, -, -, -⟩ := hcan
  set wh := Sh - sh with hwhdef
  have hwh : 0 < wh := by rw [hwhdef]; linarith
  set U := renewalMeasure ρ with hUdef
  have hUfin : ∀ b : ℝ, U (Set.Ico 0 b) ≠ ∞ := fun b => (renewalMeasure_Ico_lt_top ρ hρ b).ne
  set M := (renewalM ρ wh).toReal with hMdef
  have hMU : M = (U (Set.Ico 0 wh)).toReal := by rw [hMdef, renewalM_eq]
  have hM1 : 1 ≤ M := by
    rw [hMU]
    have := ENNReal.toReal_mono (hUfin wh) (one_le_renewal ρ wh hwh)
    simpa using this
  have hM0 : 0 < M := by linarith
  set I := ∫ x in Set.Ico 0 wh, N.F i (Sh - x) ∂U with hIdef
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_Ico fun x _ => hF.1 _
  have hKθ : 0 ≤ N.K i / θ := div_nonneg hK0 hθ0.le
  -- `J_i(K_i/θ) = (K_i/θ + I)/M`
  have hJeq : N.J i (N.K i / θ) = ENNReal.ofReal ((N.K i / θ + I) / M) := by
    unfold Network.J
    rw [← hJ, ss_renewal_reward ρ hρ _ hFc.measurable hF.1 _ sh Sh hKθ hsSh (bdd_of_cont hFc _ _),
      ← hwhdef, hMU]
  set j := (N.K i / θ + I) / M with hjdef
  set z := N.K i / M with hzdef
  set r := I / M with hrdef
  have hj : j = z / θ + r := by rw [hjdef, hzdef, hrdef]; field_simp
  have hz0 : 0 < z := div_pos hK hM0
  have hr0 : 0 ≤ r := div_nonneg hI0 hM0.le
  have hj0 : 0 ≤ j := by rw [hj]; positivity
  -- Brown's concavity under DFR demand
  obtain ⟨-, hdfr⟩ := hD hK
  have hS0 : 0 < N.survival i 0 := by
    unfold Network.survival
    by_contra hneg
    have h0 : N.marginal i {z : ℝ≥0 | (0 : ℝ) < (z : ℝ)} = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff _).1 (le_antisymm (not_lt.1 hneg) ENNReal.toReal_nonneg)
        with h | h
      · exact h
      · exact absurd h (measure_ne_top _ _)
    have hae : (fun x : ℝ≥0 => (x : ℝ≥0∞)) =ᵐ[ρ] 0 := by
      rw [Filter.EventuallyEq, ae_iff]
      refine measure_mono_null (fun x hx => ?_) h0
      simp only [Set.mem_setOf_eq, Pi.zero_apply, ENNReal.coe_eq_zero] at hx ⊢
      exact lt_of_le_of_ne x.2 (Ne.symm (by exact_mod_cast hx))
    have : ∫⁻ x, (x : ℝ≥0∞) ∂ρ = 0 := by rw [lintegral_congr_ae hae]; simp
    rw [this] at hρ
    exact lt_irrefl _ hρ
  have hlc : ∀ x y η : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ η → η ≤ 1 →
      (ρ {z : ℝ≥0 | η * x + (1 - η) * y < (z : ℝ)}).toReal
        ≤ (ρ {z : ℝ≥0 | x < (z : ℝ)}).toReal ^ η * (ρ {z : ℝ≥0 | y < (z : ℝ)}).toReal ^ (1 - η) := by
    intro x y η hx hy hη0 hη1
    have h := hdfr x y η hx hy hη0 hη1
    unfold Network.survival at h hS0
    set S0 := (N.marginal i {z : ℝ≥0 | (0 : ℝ) < (z : ℝ)}).toReal
    rw [Real.div_rpow ENNReal.toReal_nonneg hS0.le, Real.div_rpow ENNReal.toReal_nonneg hS0.le,
      div_mul_div_comm, ← Real.rpow_add hS0, show η + (1 - η) = 1 by ring, Real.rpow_one,
      div_le_div_iff_of_pos_right hS0] at h
    exact h
  have hconc := renewal_concave_dfr ρ hρ hlc
  have hconcI : ConcaveOn ℝ (Set.Icc 0 wh) (fun x => (renewalMeasure ρ (Set.Icc 0 x)).toReal) :=
    hconc.subset (fun x hx => Set.mem_Ici.2 hx.1) (convex_Icc 0 wh)
  -- the full-window mirror cost
  set mm := (mirrorCost ρ N.h N.p sh Sh).toReal with hmmdef
  have hmb := dfr_mirror_bound ρ hρ N.h N.p sh Sh hN.h_pos hN.p_pos hsSh
    (by rw [← hwhdef]; exact hconcI)
  rw [← hwhdef] at hmb
  have hmfin : mirrorCost ρ N.h N.p sh Sh ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmb
  have hmm0 : 0 ≤ mm := ENNReal.toReal_nonneg
  have hmmle : mm ≤ N.p * (1 - Real.sqrt (N.p / (N.p + N.h))) * wh := by
    rw [hmmdef]
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmb
    rwa [ENNReal.toReal_ofReal (by
      have : Real.sqrt (N.p / (N.p + N.h)) ≤ 1 := by
        rw [Real.sqrt_le_one]; rw [div_le_one (by linarith [hN.p_pos, hN.h_pos])]
        linarith [hN.h_pos]
      exact mul_nonneg (mul_nonneg hN.p_pos.le (by linarith)) hwh.le)] at this
  have hwb := canonical_width_bound N hN i (N.K i / θ) sh Sh hcan'
  rw [hJeq, ← hwhdef, ← ENNReal.ofReal_mul (by
    have := hN.h_pos; have := hN.H_pos i; have := hN.p_pos; positivity)] at hwb
  have hwb' := (ENNReal.ofReal_le_ofReal_iff (by
    have := hN.h_pos; have := hN.H_pos i; have := hN.p_pos; positivity)).1 hwb
  have hmlam : mm ≤ dfrLambda * j :=
    mirror_ratio hN.h_pos hp hH hj0 hwb' hmmle
  have hmmeq : mirrorCost ρ N.h N.p sh Sh = ENNReal.ofReal mm := (ENNReal.ofReal_toReal hmfin).symm
  -- the target bound in real form
  have hgoal : ∀ v : ℝ, v ≤ (1 + θ * dfrLambda) * j →
      ENNReal.ofReal v ≤ ENNReal.ofReal (1 + θ * dfrLambda) * N.J i (N.K i / θ) := by
    intro v hv
    rw [hJeq, ← ENNReal.ofReal_mul (by linarith)]
    exact ENNReal.ofReal_le_ofReal hv
  have hbound : j + θ * mm ≤ (1 + θ * dfrLambda) * j := by nlinarith
  -- the case analysis on `t`
  have hTdef : N.dfrT i sh Sh
      = if mm = 0 then 1 else min 1 (Real.sqrt (z / mm)) := by
    unfold Network.dfrT Network.dfrMirror Network.dfrZ
    rfl
  by_cases htt : N.dfrT i sh Sh = 1
  · -- the canonical cycle
    obtain ⟨h1, h2, h3⟩ := hT1 htt
    refine ⟨by rw [h1, h2]; exact hsSh.le, ?_⟩
    rw [h1, h2, h3, ss_renewal_reward ρ hρ _ hFc.measurable hF.1 _ sh Sh hK0 hsSh
      (bdd_of_cont hFc _ _), ← hwhdef, ← hMU, hmmeq, ← ENNReal.ofReal_add
      (div_nonneg (by linarith) hM0.le) hmm0]
    refine hgoal _ ?_
    show (N.K i + I) / M + mm ≤ _
    have hmz : mm ≤ z := by
      by_cases hm0 : mm = 0
      · rw [hm0]; exact hz0.le
      · rw [hTdef, if_neg hm0] at htt
        have hmpos : 0 < mm := lt_of_le_of_ne hmm0 (Ne.symm hm0)
        have h1' : 1 ≤ Real.sqrt (z / mm) := by
          by_contra hlt; push_neg at hlt
          rw [min_eq_right hlt.le] at htt; linarith
        have : 1 ≤ z / mm := by rwa [Real.one_le_sqrt] at h1'
        rwa [le_div_iff₀ hmpos, one_mul] at this
    have e : (N.K i + I) / M = z + r := by rw [hzdef, hrdef]; field_simp
    rw [e]
    have : z + mm ≤ z / θ + θ * mm := by
      have hzθ : z ≤ z / θ := by rw [le_div_iff₀ hθ0]; nlinarith
      have h1 : 0 ≤ (1 - θ) * (z / θ - mm) := mul_nonneg (by linarith) (by linarith)
      have h2 : (1 - θ) * (z / θ) = z / θ - z := by field_simp
      nlinarith
    linarith
  · have htlt : N.dfrT i sh Sh < 1 := by
      rcases lt_or_eq_of_le (show N.dfrT i sh Sh ≤ 1 by
        rw [hTdef]; split_ifs
        · exact le_rfl
        · exact min_le_left _ _) with h | h
      · exact h
      · exact absurd h htt
    have hmpos : 0 < mm := by
      rcases hmm0.lt_or_eq with h | h
      · exact h
      · exfalso; rw [hTdef, if_pos h.symm] at htlt; linarith
    have htval : N.dfrT i sh Sh = Real.sqrt (z / mm) := by
      rw [hTdef, if_neg hmpos.ne'] at htlt ⊢
      rcases le_total 1 (Real.sqrt (z / mm)) with h | h
      · rw [min_eq_left h] at htlt; linarith
      · exact min_eq_right h
    set tt := N.dfrT i sh Sh with htt_def
    have htt0 : 0 < tt := by rw [htval]; exact Real.sqrt_pos.2 (div_pos hz0 hmpos)
    have hkey : z / tt + tt * mm ≤ z / θ + θ * mm := by rw [htval]; exact amgm hz0 hmpos hθ0
    by_cases hlow : tt ≤ N.dfrT0 i sh Sh
    · -- base stock
      obtain ⟨hsS, hmin, ha⟩ := hTlow htlt hlow
      refine ⟨hsS.le, ?_⟩
      rw [hsS, ha, mirrorAvg_SS, add_zero, ss_avg_SS ρ (N.F i) hF.1 _ _ hK0]
      refine hgoal _ ?_
      -- `K q = z / t₀`
      set q := (ρ (Set.Ioi 0)).toReal with hqdef
      have hq0 : 0 < q := by
        have : ρ (Set.Ioi 0) ≠ 0 := by
          intro h0
          have : renewalMeasure ρ {0} = ∞ := by rw [renewal_zero_atom, h0, ENNReal.inv_zero]
          exact (ne_top_of_le_ne_top (hUfin 1) (measure_mono (fun x hx => by
            simp only [Set.mem_singleton_iff] at hx; simp [hx]))) this
        exact ENNReal.toReal_pos this (measure_ne_top _ _)
      have ht0 : N.dfrT0 i sh Sh = 1 / (q * M) := by
        unfold Network.dfrT0
        rw [renewal_zero_atom, ENNReal.toReal_inv, ← hqdef, ← hMdef]
        field_simp
      have hKq : N.K i * q ≤ z / tt := by
        have h1 : z / N.dfrT0 i sh Sh = N.K i * q := by rw [ht0, hzdef]; field_simp
        rw [← h1]
        exact div_le_div_of_nonneg_left hz0.le htt0 hlow
      have hFr : N.F i (c.S i) ≤ r := by
        rw [hrdef, le_div_iff₀ hM0, hIdef]
        have hint : IntegrableOn (fun x => N.F i (Sh - x)) (Set.Ico 0 wh) U := by
          obtain ⟨C, hC⟩ := (isCompact_Icc (a := 0) (b := wh)).exists_bound_of_continuousOn
            (hFc.comp (continuous_const.sub continuous_id)).continuousOn
          refine Measure.integrableOn_of_bounded (M := C) (hUfin wh)
            (hFc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable ?_
          exact ae_restrict_of_forall_mem measurableSet_Ico fun x hx =>
            hC x (Set.Ico_subset_Icc_self hx)
        calc N.F i (c.S i) * M = ∫ _x in Set.Ico 0 wh, N.F i (c.S i) ∂U := by
              rw [setIntegral_const, smul_eq_mul, measureReal_def, ← hMU, mul_comm]
          _ ≤ ∫ x in Set.Ico 0 wh, N.F i (Sh - x) ∂U :=
              setIntegral_mono_on (integrableOn_const (hUfin wh) enorm_ne_top) hint
                measurableSet_Ico fun x _ => hmin _
      have : N.F i (c.S i) + N.K i * q ≤ r + z / tt + tt * mm := by
        have := mul_nonneg htt0.le hmm0; linarith
      linarith [hbound, hj]
    · -- shortened window
      push_neg at hlow
      obtain ⟨hMw, hopt, hmir⟩ := hTwin htlt hlow
      obtain ⟨w, hwdef⟩ : ∃ w, w = c.S i - c.s i := ⟨_, rfl⟩
      rw [← hwdef] at hMw hopt
      have hMwpos : 0 < (renewalM ρ w).toReal := by
        rw [hMw, ENNReal.toReal_mul, ENNReal.toReal_ofReal htt0.le, ← hMdef]
        positivity
      have hw0 : 0 < w := by
        by_contra hneg; push_neg at hneg
        rw [renewalM_nonpos ρ hneg] at hMwpos; simp at hMwpos
      have hwwh : w ≤ wh := by
        by_contra hgt; push_neg at hgt
        have hmono := ENNReal.toReal_mono (by rw [renewalM_eq]; exact hUfin w) (renewalM_mono ρ hgt.le)
        rw [hMw, ENNReal.toReal_mul, ENNReal.toReal_ofReal htt0.le, ← hMdef] at hmono
        nlinarith
      have hsS : c.s i < c.S i := by rw [hwdef] at hw0; linarith
      refine ⟨hsS.le, ?_⟩
      obtain ⟨hcm, hch⟩ := dfr_window_contraction N hN i wh w tt hw0 hwwh htt0 htlt.le hMw hconcI
      have hmirw := hcm (c.S i) Sh
      rw [show c.S i - w = c.s i by rw [hwdef]; ring, show Sh - wh = sh by rw [hwhdef]; ring,
        hmmeq, ← ENNReal.ofReal_mul htt0.le] at hmirw
      obtain ⟨S', hS'⟩ := hch Sh
      rw [show Sh - wh = sh by rw [hwhdef]; ring] at hS'
      have hhold := (hopt S').trans hS'
      have hmw : (renewalM ρ w).toReal = tt * M := by
        rw [hMw, ENNReal.toReal_mul, ENNReal.toReal_ofReal htt0.le]
      have hMwU : (U (Set.Ico 0 w)).toReal = tt * M := by rw [← hmw, renewalM_eq]
      -- holding and setup costs of the window
      set Iw := ∫ x in Set.Ico 0 w, N.F i (c.S i - x) ∂U with hIw
      have hIw0 : 0 ≤ Iw := setIntegral_nonneg measurableSet_Ico fun x _ => hF.1 _
      have hssK : ssAvgCost ρ (N.F i) (N.K i) (c.s i) (c.S i)
          = ENNReal.ofReal (z / tt) + ssAvgCost ρ (N.F i) 0 (c.s i) (c.S i) := by
        rw [ss_renewal_reward ρ hρ _ hFc.measurable hF.1 _ _ _ hK0 hsS (bdd_of_cont hFc _ _),
          ss_renewal_reward ρ hρ _ hFc.measurable hF.1 _ _ _ le_rfl hsS (bdd_of_cont hFc _ _),
          ← hwdef, hMwU, zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        rw [hzdef]
        field_simp
      have hss0 : ssAvgCost ρ (N.F i) 0 sh Sh = ENNReal.ofReal r := by
        rw [ss_renewal_reward ρ hρ _ hFc.measurable hF.1 _ _ _ le_rfl hsSh (bdd_of_cont hFc _ _),
          ← hwhdef, ← hMU, zero_add]
      rw [hss0] at hhold
      rw [hssK, hmir]
      calc ENNReal.ofReal (z / tt) + ssAvgCost ρ (N.F i) 0 (c.s i) (c.S i)
            + mirrorCost ρ N.h N.p (c.s i) (c.S i)
          ≤ ENNReal.ofReal (z / tt) + ENNReal.ofReal r + ENNReal.ofReal (tt * mm) := by
            gcongr
        _ = ENNReal.ofReal (z / tt + r + tt * mm) := by
            rw [← ENNReal.ofReal_add (by positivity) hr0,
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
        _ ≤ _ := by
            refine hgoal _ ?_
            linarith [hbound, hj]
