-- Prove2me | solution 1 for OWMR.arb_supplier_shortage
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T12:52:29.652938+00:00
-- url     : https://prove2.me/submissions/090ccaec-dd78-4fbc-81ff-7db9461fc532

import Definitions.Def_owmr_consolidation_policy
import Theorems.Thm_OWMR_ss_renewal_reward
import Theorems.Thm_OWMR_sl_subsolution
import Theorems.Thm_OWMR_sl_adapted_bound
import Theorems.Thm_OWMR_renewalMeasure_Ico_lt_top
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.Filter.ENNReal
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
Lemma C.4 (supplier cost and shortages). Single-location facts used: the canonical policy is
optimal among `(s,S)` policies (`slValue ≤ ssAvgCost`), the value is at least `min f`, the right
derivative of `f_{L₀}` is `h - (h+p) ℙ(D^{(L₀)} > y)`, and the renewal-reward formula.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open OWMR

noncomputable section

namespace OWMR.L4aux

lemma ssPre_dep (s S : ℝ) : ∀ (t : ℕ) (d d' : ℕ → ℝ≥0), (∀ r < t, d r = d' r) →
    ssPre s S d t = ssPre s S d' t
  | 0, d, d', _ => rfl
  | t + 1, d, d', h => by
    simp only [ssPre]
    rw [ssPre_dep s S t d d' (fun r hr => h r (by omega)), h t (by omega)]

lemma ssPre_meas (s S : ℝ) : ∀ t, Measurable fun d : ℕ → ℝ≥0 => ssPre s S d t
  | 0 => measurable_const
  | t + 1 => by
    simp only [ssPre]
    exact (Measurable.ite (measurableSet_le (ssPre_meas s S t) measurable_const) measurable_const
      (ssPre_meas s S t)).sub ((measurable_pi_apply t).coe_nnreal_real)

lemma ssPre_le (s S : ℝ) (hsS : s ≤ S) (d : ℕ → ℝ≥0) : ∀ t, ssPre s S d t ≤ S
  | 0 => le_rfl
  | t + 1 => by
    simp only [ssPre]
    have := ssPre_le s S hsS d t
    split_ifs <;> linarith [NNReal.coe_nonneg (d t)]

lemma ss_pos (s S : ℝ) (d : ℕ → ℝ≥0) : ∀ t,
    S + ∑ r ∈ Finset.range (t + 1), (ssPost s S d r - ssPre s S d r)
      - ∑ r ∈ Finset.range t, (d r : ℝ) = ssPost s S d t
  | 0 => by simp [ssPre]
  | t + 1 => by
    rw [Finset.sum_range_succ (fun r => ssPost s S d r - ssPre s S d r) (t + 1),
      Finset.sum_range_succ (fun r => (d r : ℝ)) t]
    have ih := ss_pos s S d t
    have e : ssPre s S d (t + 1) = ssPost s S d t - (d t : ℝ) := rfl
    linarith

lemma measurable_padHist' (N : ℕ) : Measurable (padHist N : (Fin N → ℝ≥0) → ℕ → ℝ≥0) := by
  refine measurable_pi_lambda _ fun t => ?_
  by_cases h : t < N
  · simp only [padHist, dif_pos h]
    exact measurable_pi_apply _
  · simp only [padHist, dif_neg h]
    exact measurable_const

lemma limsup_add_tendsto_zero (u v : ℕ → ℝ≥0∞) (hv : Tendsto v atTop (𝓝 0)) :
    limsup (fun n => u n + v n) atTop ≤ limsup u atTop := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε' : (0 : ℝ≥0∞) < ε := by exact_mod_cast hε
  have hev : ∀ᶠ n in atTop, u n + v n ≤ u n + ε :=
    (hv.eventually (ge_mem_nhds hε')).mono fun n hn => add_le_add le_rfl hn
  calc limsup (fun n => u n + v n) atTop ≤ limsup (fun n => u n + (ε : ℝ≥0∞)) atTop :=
        limsup_le_limsup hev
    _ = limsup u atTop + ε :=
        limsup_add_const atTop u _ (by isBoundedDefault) (by isBoundedDefault)

/-- Every `(s,S)` policy costs at least the single-location value. -/
lemma value_le_ss (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ)
    (f : ℝ → ℝ) (hfc : Continuous f) (hfcv : ConvexOn ℝ Set.univ f) (hf0 : ∀ y, 0 ≤ f y)
    (hfco : ∀ C : ℝ, ∃ R : ℝ, ∀ y, R ≤ |y| → C ≤ f y) (hfa : AntitoneOn f (Set.Iic 0))
    (K : ℝ) (hK : 0 ≤ K) (s S : ℝ) (hsS : s ≤ S) :
    slValue ρ f K ≤ ssAvgCost ρ f K s S := by
  obtain ⟨J, hJ0, hJeq, v, hvm, hvb, hvs⟩ := sl_subsolution ρ hρ f hfc hfcv hf0 hfco hfa K hK
  rw [hJeq]
  have hsub : ∀ y, J ≤ f y + ∫ a, v (y - ((fun a : ℝ≥0 => a) a : ℝ)) ∂ρ - v y := fun y => by
    linarith [hvs y, le_max_right (f y - J) 0]
  set q : ℕ → Unit → (ℕ → ℝ≥0) → ℝ := fun t _ d => ssPost s S d t - ssPre s S d t with hq
  have hna : ∀ (t : ℕ) (u : Unit) (d d' : ℕ → ℝ≥0), (∀ r < t, d r = d' r) →
      q t u d = q t u d' := fun t u d d' h => by
    simp only [hq, ssPost, ssPre_dep s S t d d' h]
  have hpm : ∀ t, Measurable fun d : ℕ → ℝ≥0 => ssPost s S d t := fun t =>
    Measurable.ite (measurableSet_le (ssPre_meas s S t) measurable_const) measurable_const
      (ssPre_meas s S t)
  have hqm : ∀ t, Measurable fun ω : Unit × (ℕ → ℝ≥0) => q t ω.1 ω.2 := fun t =>
    ((hpm t).sub (ssPre_meas s S t)).comp measurable_snd
  have hq0 : ∀ t u d, 0 ≤ q t u d := fun t u d => by
    simp only [hq, ssPost]
    split_ifs with h
    · linarith [ssPre_le s S hsS d t]
    · simp
  have hcost : ∀ (d : ℕ → ℝ≥0) (t : ℕ),
      K * (if 0 < q t () d then 1 else 0)
        + f (S + ∑ r ∈ Finset.range (t + 1), q r () d - ∑ r ∈ Finset.range t, (d r : ℝ))
      = ssPeriodCost f K s S d t := by
    intro d t
    simp only [hq]
    rw [ss_pos s S d t]
    unfold ssPeriodCost
    congr 2
    by_cases h1 : ssPre s S d t ≤ s
    · have hpost : ssPost s S d t = S := by unfold ssPost; rw [if_pos h1]
      by_cases h2 : ssPre s S d t < S
      · have h3 : 0 < ssPost s S d t - ssPre s S d t := by rw [hpost]; linarith
        rw [if_pos h3, if_pos ⟨h1, h2⟩]
      · have h3 : ¬ 0 < ssPost s S d t - ssPre s S d t := by
          rw [hpost]; linarith [ssPre_le s S hsS d t]
        rw [if_neg h3, if_neg (fun h => h2 h.2)]
    · have hpost : ssPost s S d t = ssPre s S d t := by unfold ssPost; rw [if_neg h1]
      have h3 : ¬ 0 < ssPost s S d t - ssPre s S d t := by rw [hpost]; simp
      rw [if_neg h3, if_neg (fun h => h1 h.1)]
  have hmeasC : ∀ T t, Measurable fun z : Fin T → ℝ≥0 =>
      ENNReal.ofReal (ssPeriodCost f K s S (padHist T z) t) := fun T t => by
    refine ENNReal.measurable_ofReal.comp ?_
    unfold ssPeriodCost
    refine (measurable_const.mul (Measurable.ite ?_ measurable_const measurable_const)).add
      (hfc.measurable.comp ((hpm t).comp (measurable_padHist' T)))
    exact (measurableSet_le ((ssPre_meas s S t).comp (measurable_padHist' T)) measurable_const).inter
      (measurableSet_lt ((ssPre_meas s S t).comp (measurable_padHist' T)) measurable_const)
  have hbound : ∀ T : ℕ, ENNReal.ofReal (T * J)
      ≤ ∫⁻ z, ∑ t ∈ Finset.range T, ENNReal.ofReal (ssPeriodCost f K s S (padHist T z) t)
          ∂(Measure.pi fun _ : Fin T => ρ) + ENNReal.ofReal K := by
    intro T
    have h := sl_adapted_bound ρ (Measure.dirac ()) (fun a => a) measurable_id q hna hqm hq0 S f
      hfc.measurable hf0 K J v hvm hvb hsub T T le_rfl
    simp only [hcost] at h
    have hF : Measurable fun z : Fin T → ℝ≥0 =>
        ∑ t ∈ Finset.range T, ENNReal.ofReal (ssPeriodCost f K s S (padHist T z) t) :=
      Finset.measurable_sum _ fun t _ => hmeasC T t
    have hp := lintegral_prod (μ := Measure.dirac ()) (ν := Measure.pi fun _ : Fin T => ρ)
      (fun ω : Unit × (Fin T → ℝ≥0) =>
        ∑ t ∈ Finset.range T, ENNReal.ofReal (ssPeriodCost f K s S (padHist T ω.2) t))
      (hF.comp measurable_snd).aemeasurable
    rw [hp, lintegral_dirac] at h
    exact h
  -- divide by `T` and pass to the limit
  set a : ℕ → ℝ≥0∞ := fun T => (T : ℝ≥0∞)⁻¹ * ∫⁻ z, ∑ t ∈ Finset.range T,
    ENNReal.ofReal (ssPeriodCost f K s S (padHist T z) t) ∂(Measure.pi fun _ : Fin T => ρ) with ha
  have hev : ∀ᶠ T : ℕ in atTop, ENNReal.ofReal J ≤ a T + (T : ℝ≥0∞)⁻¹ * ENNReal.ofReal K := by
    filter_upwards [eventually_ge_atTop 1] with T hT
    have hT0 : (T : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show T ≠ 0 by omega)
    have h1 := hbound T
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg T), ENNReal.ofReal_natCast] at h1
    rw [ha, ← mul_add, ← ENNReal.mul_le_iff_le_inv hT0 (ENNReal.natCast_ne_top T)]
    exact h1
  have hlim : Tendsto (fun T : ℕ => (T : ℝ≥0∞)⁻¹ * ENNReal.ofReal K) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.mul_const (b := ENNReal.ofReal K) ENNReal.tendsto_inv_nat_nhds_zero
      (Or.inr ENNReal.ofReal_ne_top)
    simpa using this
  calc ENNReal.ofReal J ≤ limsup (fun T => a T + (T : ℝ≥0∞)⁻¹ * ENNReal.ofReal K) atTop :=
        le_limsup_of_frequently_le hev.frequently (by isBoundedDefault)
    _ ≤ limsup a atTop := limsup_add_tendsto_zero a _ hlim
    _ = ssAvgCost ρ f K s S := rfl

/-- The single-location value is at least `min f`. -/
lemma value_ge_inf (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (f : ℝ → ℝ) (hf0 : ∀ y, 0 ≤ f y)
    (K : ℝ) (hK : 0 ≤ K) : ENNReal.ofReal (⨅ y, f y) ≤ slValue ρ f K := by
  have hinf : ∀ y, (⨅ y, f y) ≤ f y := fun y => ciInf_le ⟨0, by rintro _ ⟨z, rfl⟩; exact hf0 z⟩ y
  unfold slValue
  refine le_iInf fun U => le_iInf fun mU => le_iInf fun ν => le_iInf fun hν => le_iInf fun q =>
    le_iInf fun hq => ?_
  unfold slAvgCost
  refine le_limsup_of_frequently_le (Eventually.frequently ?_) (by isBoundedDefault)
  filter_upwards [eventually_ge_atTop 1] with T hT
  have hT0 : (T : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show T ≠ 0 by omega)
  rw [← ENNReal.mul_le_iff_le_inv hT0 (ENNReal.natCast_ne_top T)]
  calc (T : ℝ≥0∞) * ENNReal.ofReal (⨅ y, f y)
      = ∫⁻ _ω, ∑ _t ∈ Finset.range T, ENNReal.ofReal (⨅ y, f y)
          ∂(ν.prod (Measure.pi fun _ : Fin T => ρ)) := by
        simp [lintegral_const, measure_univ]
    _ ≤ _ := by
        refine lintegral_mono fun ω => Finset.sum_le_sum fun t _ => ENNReal.ofReal_le_ofReal ?_
        unfold slPeriodCost
        have h1 : 0 ≤ K * (if 0 < q t ω.1 (padHist T ω.2) then 1 else 0) := by
          split_ifs <;> simp [hK]
        linarith [hinf (slPos 0 q ω.1 (padHist T ω.2) t)]

/-- `(S,S)` with zero setup cost: the post-action position is always `S`. -/
lemma ss_SS (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (f : ℝ → ℝ) (S : ℝ) :
    ssAvgCost ρ f 0 S S = ENNReal.ofReal (f S) := by
  unfold ssAvgCost
  have hc : ∀ T : ℕ, ∫⁻ z, ∑ t ∈ Finset.range T, ENNReal.ofReal (ssPeriodCost f 0 S S (padHist T z) t)
      ∂(Measure.pi fun _ : Fin T => ρ) = T * ENNReal.ofReal (f S) := by
    intro T
    have e : ∀ (d : ℕ → ℝ≥0) t, ssPeriodCost f 0 S S d t = f S := by
      intro d t
      unfold ssPeriodCost ssPost
      rw [if_pos (ssPre_le S S le_rfl d t)]
      ring
    simp only [e, Finset.sum_const, Finset.card_range, nsmul_eq_mul, lintegral_const,
      measure_univ, mul_one]
  simp only [hc]
  refine (limsup_congr (eventually_ge_atTop 1 |>.mono fun T hT => ?_)).trans (limsup_const _)
  have hT0 : (T : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show T ≠ 0 by omega)
  rw [← mul_assoc, ENNReal.inv_mul_cancel hT0 (ENNReal.natCast_ne_top T), one_mul]

end OWMR.L4aux

namespace OWMR.L4aux

/-! ### Newsvendor costs -/

def nvCost {β : Type} [MeasurableSpace β] (P : Measure β) (X : β → ℝ) (H p y : ℝ) : ℝ :=
  ∫ b, (H * max (y - X b) 0 + p * max (X b - y) 0) ∂P

section nv

variable {β : Type} [MeasurableSpace β] (P : Measure β) [IsProbabilityMeasure P] (X : β → ℝ)

lemma nv_integrable (hX : Integrable X P) (H p y : ℝ) :
    Integrable (fun b => H * max (y - X b) 0 + p * max (X b - y) 0) P :=
  (((integrable_const y).sub hX).pos_part.const_mul _).add
    ((hX.sub (integrable_const y)).pos_part.const_mul _)

omit [IsProbabilityMeasure P] in
lemma nv_nonneg (H p y : ℝ) (hH : 0 ≤ H) (hp : 0 ≤ p) : 0 ≤ nvCost P X H p y :=
  integral_nonneg fun b =>
    add_nonneg (mul_nonneg hH (le_max_right _ _)) (mul_nonneg hp (le_max_right _ _))

lemma nv_lower (hX : Integrable X P) (H p y : ℝ) (hH : 0 ≤ H) (hp : 0 ≤ p) :
    H * (y - ∫ b, X b ∂P) ≤ nvCost P X H p y ∧ p * (∫ b, X b ∂P - y) ≤ nvCost P X H p y := by
  have hi := nv_integrable P X hX H p y
  constructor
  · have e : H * (y - ∫ b, X b ∂P) = ∫ b, H * (y - X b) ∂P := by
      rw [integral_const_mul, integral_sub (integrable_const y) hX, integral_const, probReal_univ,
        one_smul]
    rw [e]
    refine integral_mono ((((integrable_const y).sub hX)).const_mul H) hi fun b => ?_
    have h1 : H * (y - X b) ≤ H * max (y - X b) 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hH
    have h2 : 0 ≤ p * max (X b - y) 0 := mul_nonneg hp (le_max_right _ _)
    simp only
    linarith
  · have e : p * (∫ b, X b ∂P - y) = ∫ b, p * (X b - y) ∂P := by
      rw [integral_const_mul, integral_sub hX (integrable_const y), integral_const, probReal_univ,
        one_smul]
    rw [e]
    refine integral_mono ((hX.sub (integrable_const y)).const_mul p) hi fun b => ?_
    have h1 : p * (X b - y) ≤ p * max (X b - y) 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hp
    have h2 : 0 ≤ H * max (y - X b) 0 := mul_nonneg hH (le_max_right _ _)
    simp only
    linarith

lemma nv_lip (hX : Integrable X P) (H p : ℝ) (hH : 0 ≤ H) (hp : 0 ≤ p) (y y' : ℝ) :
    |nvCost P X H p y - nvCost P X H p y'| ≤ (H + p) * |y - y'| := by
  unfold nvCost
  rw [← integral_sub (nv_integrable P X hX H p y) (nv_integrable P X hX H p y')]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ b, |H * max (y - X b) 0 + p * max (X b - y) 0
          - (H * max (y' - X b) 0 + p * max (X b - y') 0)| ∂P
      ≤ ∫ _b, (H + p) * |y - y'| ∂P := by
        refine integral_mono ((nv_integrable P X hX H p y).sub
          (nv_integrable P X hX H p y')).abs (integrable_const _) fun b => ?_
        have k1 := abs_max_sub_max_le_abs (y - X b) (y' - X b) 0
        have k2 := abs_max_sub_max_le_abs (X b - y) (X b - y') 0
        rw [show y - X b - (y' - X b) = y - y' by ring] at k1
        rw [show X b - y - (X b - y') = -(y - y') by ring, abs_neg] at k2
        calc |H * max (y - X b) 0 + p * max (X b - y) 0
              - (H * max (y' - X b) 0 + p * max (X b - y') 0)|
            = |H * (max (y - X b) 0 - max (y' - X b) 0)
                + p * (max (X b - y) 0 - max (X b - y') 0)| := by ring_nf
          _ ≤ |H * (max (y - X b) 0 - max (y' - X b) 0)|
                + |p * (max (X b - y) 0 - max (X b - y') 0)| := abs_add_le _ _
          _ = H * |max (y - X b) 0 - max (y' - X b) 0|
                + p * |max (X b - y) 0 - max (X b - y') 0| := by
              rw [abs_mul, abs_mul, abs_of_nonneg hH, abs_of_nonneg hp]
          _ ≤ H * |y - y'| + p * |y - y'| :=
              add_le_add (mul_le_mul_of_nonneg_left k1 hH) (mul_le_mul_of_nonneg_left k2 hp)
          _ = (H + p) * |y - y'| := by ring
    _ = (H + p) * |y - y'| := by simp [integral_const, probReal_univ]

lemma nv_continuous (hX : Integrable X P) (H p : ℝ) (hH : 0 ≤ H) (hp : 0 ≤ p) :
    Continuous (nvCost P X H p) := by
  have hL : LipschitzWith (Real.toNNReal (H + p)) (nvCost P X H p) := by
    refine LipschitzWith.of_dist_le_mul fun y y' => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by linarith)]
    exact nv_lip P X hX H p hH hp y y'
  exact hL.continuous

lemma nv_convex (hX : Integrable X P) (H p : ℝ) (hH : 0 ≤ H) (hp : 0 ≤ p) :
    ConvexOn ℝ Set.univ (nvCost P X H p) := by
  refine ⟨convex_univ, fun y _ y' _ a c ha hc hac => ?_⟩
  simp only [smul_eq_mul]
  unfold nvCost
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((nv_integrable P X hX H p y).const_mul a)
      ((nv_integrable P X hX H p y').const_mul c)]
  refine integral_mono (nv_integrable P X hX H p _)
    (((nv_integrable P X hX H p y).const_mul a).add ((nv_integrable P X hX H p y').const_mul c))
    fun b => ?_
  have k1 : max (a * y + c * y' - X b) 0 ≤ a * max (y - X b) 0 + c * max (y' - X b) 0 := by
    refine max_le ?_ (add_nonneg (mul_nonneg ha (le_max_right _ _))
      (mul_nonneg hc (le_max_right _ _)))
    have := mul_le_mul_of_nonneg_left (le_max_left (y - X b) 0) ha
    have := mul_le_mul_of_nonneg_left (le_max_left (y' - X b) 0) hc
    have hs : a * X b + c * X b = X b := by rw [← add_mul, hac, one_mul]
    nlinarith
  have k2 : max (X b - (a * y + c * y')) 0 ≤ a * max (X b - y) 0 + c * max (X b - y') 0 := by
    refine max_le ?_ (add_nonneg (mul_nonneg ha (le_max_right _ _))
      (mul_nonneg hc (le_max_right _ _)))
    have := mul_le_mul_of_nonneg_left (le_max_left (X b - y) 0) ha
    have := mul_le_mul_of_nonneg_left (le_max_left (X b - y') 0) hc
    have hs : a * X b + c * X b = X b := by rw [← add_mul, hac, one_mul]
    nlinarith
  have := mul_le_mul_of_nonneg_left k1 hH
  have := mul_le_mul_of_nonneg_left k2 hp
  simp only
  linarith

lemma nv_anti (hX : Integrable X P) (hX0 : ∀ b, 0 ≤ X b) (H p : ℝ) (hp : 0 ≤ p) :
    AntitoneOn (nvCost P X H p) (Set.Iic 0) := by
  intro y hy y' hy' hyy'
  simp only [Set.mem_Iic] at hy hy'
  unfold nvCost
  refine integral_mono (nv_integrable P X hX H p y') (nv_integrable P X hX H p y) fun b => ?_
  have e1 : max (y - X b) 0 = 0 := max_eq_right (by linarith [hX0 b])
  have e2 : max (y' - X b) 0 = 0 := max_eq_right (by linarith [hX0 b])
  have e3 : max (X b - y) 0 = X b - y := max_eq_left (by linarith [hX0 b])
  have e4 : max (X b - y') 0 = X b - y' := max_eq_left (by linarith [hX0 b])
  simp only [e1, e2, e3, e4]
  nlinarith

lemma nv_coercive (hX : Integrable X P) (H p : ℝ) (hH : 0 < H) (hp : 0 < p) :
    ∀ C : ℝ, ∃ R : ℝ, ∀ y, R ≤ |y| → C ≤ nvCost P X H p y := by
  intro C
  set c := ∫ b, X b ∂P
  set m := min H p with hm
  have hm0 : 0 < m := lt_min hH hp
  refine ⟨|c| + max C 0 / m, fun y hy => ?_⟩
  have hlow := nv_lower P X hX H p y hH.le hp.le
  have hyc : max C 0 / m ≤ |y - c| := by
    have := abs_sub_abs_le_abs_sub y c
    linarith
  have hmc : max C 0 ≤ m * |y - c| := by
    rw [div_le_iff₀ hm0] at hyc
    linarith
  have hkey : m * |y - c| ≤ nvCost P X H p y := by
    rcases le_or_gt c y with h | h
    · rw [abs_of_nonneg (by linarith)]
      calc m * (y - c) ≤ H * (y - c) := mul_le_mul_of_nonneg_right (min_le_left _ _) (by linarith)
        _ ≤ _ := hlow.1
    · rw [abs_of_neg (by linarith)]
      calc m * -(y - c) = m * (c - y) := by ring
        _ ≤ p * (c - y) := mul_le_mul_of_nonneg_right (min_le_right _ _) (by linarith)
        _ ≤ _ := hlow.2
  linarith [le_max_left C 0]

/-- Slope at most `H`: `f(y + a) ≤ f(y) + H a` for `a ≥ 0`. -/
lemma nv_slope (hX : Integrable X P) (H p : ℝ) (hH : 0 ≤ H) (hp : 0 ≤ p) (y a : ℝ) (ha : 0 ≤ a) :
    nvCost P X H p (y + a) ≤ nvCost P X H p y + H * a := by
  unfold nvCost
  have e : ∫ b, (H * max (y - X b) 0 + p * max (X b - y) 0) ∂P + H * a
      = ∫ b, (H * max (y - X b) 0 + p * max (X b - y) 0 + H * a) ∂P := by
    rw [integral_add (nv_integrable P X hX H p y) (integrable_const _), integral_const,
      probReal_univ, one_smul]
  rw [e]
  refine integral_mono (nv_integrable P X hX H p _)
    ((nv_integrable P X hX H p y).add (integrable_const _)) fun b => ?_
  have k1 : max (y + a - X b) 0 ≤ max (y - X b) 0 + a :=
    max_le (by linarith [le_max_left (y - X b) 0]) (by linarith [le_max_right (y - X b) 0])
  have k2 : max (X b - (y + a)) 0 ≤ max (X b - y) 0 := max_le_max (by linarith) le_rfl
  have := mul_le_mul_of_nonneg_left k1 hH
  have := mul_le_mul_of_nonneg_left k2 hp
  simp only
  linarith

/-- Right derivative: `(f(y + ε) - f(y))/ε → H - (H + p) ℙ(X > y)`. -/
lemma nv_deriv (hX : Integrable X P) (hXm : Measurable X) (H p : ℝ) (hH : 0 ≤ H) (hp : 0 ≤ p)
    (y : ℝ) :
    Tendsto (fun k : ℕ => (nvCost P X H p (y + 1 / ((k : ℝ) + 1)) - nvCost P X H p y)
        / (1 / ((k : ℝ) + 1))) atTop
      (𝓝 (H - (H + p) * P.real {b | y < X b})) := by
  set ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hε
  have hε0 : ∀ k, 0 < ε k := fun k => by positivity
  have hε_lim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set g : β → ℝ := fun b => if X b ≤ y then H else -p with hg
  have hq : ∀ k, (nvCost P X H p (y + ε k) - nvCost P X H p y) / ε k
      = ∫ b, (H * max (y + ε k - X b) 0 + p * max (X b - (y + ε k)) 0
          - (H * max (y - X b) 0 + p * max (X b - y) 0)) / ε k ∂P := by
    intro k
    unfold nvCost
    rw [integral_div, integral_sub (nv_integrable P X hX H p _) (nv_integrable P X hX H p _)]
  show Tendsto (fun k : ℕ => (nvCost P X H p (y + ε k) - nvCost P X H p y) / ε k) atTop _
  simp only [hq]
  have hlim_g : ∫ b, g b ∂P = H - (H + p) * P.real {b | y < X b} := by
    have hS : MeasurableSet {b | y < X b} := measurableSet_lt measurable_const hXm
    have e : g = fun b => H - (H + p) * {b | y < X b}.indicator (fun _ => (1 : ℝ)) b := by
      funext b
      simp only [hg]
      by_cases h : X b ≤ y
      · have : b ∉ {b | y < X b} := by simp; exact h
        rw [if_pos h, Set.indicator_of_notMem this]; ring
      · have : b ∈ {b | y < X b} := by simp; linarith
        rw [if_neg h, Set.indicator_of_mem this]; ring
    rw [e, integral_sub (integrable_const _) ((integrable_const (1 : ℝ)).indicator hS |>.const_mul _),
      integral_const_mul, integral_indicator_const _ hS]
    simp
  rw [← hlim_g]
  refine tendsto_integral_of_dominated_convergence (fun _ => H + p) (fun k => ?_)
    (integrable_const _) (fun k => Filter.Eventually.of_forall fun b => ?_)
    (Filter.Eventually.of_forall fun b => ?_)
  · exact ((((nv_integrable P X hX H p _).sub (nv_integrable P X hX H p _)).div_const _)).aestronglyMeasurable
  · -- the difference quotient is bounded by `H + p`
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hε0 k), div_le_iff₀ (hε0 k)]
    have k1 := abs_max_sub_max_le_abs (y + ε k - X b) (y - X b) 0
    have k2 := abs_max_sub_max_le_abs (X b - (y + ε k)) (X b - y) 0
    rw [show y + ε k - X b - (y - X b) = ε k by ring, abs_of_pos (hε0 k)] at k1
    rw [show X b - (y + ε k) - (X b - y) = -ε k by ring, abs_neg, abs_of_pos (hε0 k)] at k2
    calc |H * max (y + ε k - X b) 0 + p * max (X b - (y + ε k)) 0
          - (H * max (y - X b) 0 + p * max (X b - y) 0)|
        = |H * (max (y + ε k - X b) 0 - max (y - X b) 0)
            + p * (max (X b - (y + ε k)) 0 - max (X b - y) 0)| := by ring_nf
      _ ≤ |H * (max (y + ε k - X b) 0 - max (y - X b) 0)|
            + |p * (max (X b - (y + ε k)) 0 - max (X b - y) 0)| := abs_add_le _ _
      _ = H * |max (y + ε k - X b) 0 - max (y - X b) 0|
            + p * |max (X b - (y + ε k)) 0 - max (X b - y) 0| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hH, abs_of_nonneg hp]
      _ ≤ H * ε k + p * ε k :=
          add_le_add (mul_le_mul_of_nonneg_left k1 hH) (mul_le_mul_of_nonneg_left k2 hp)
      _ = (H + p) * ε k := by ring
  · -- pointwise limit
    simp only [hg]
    by_cases h : X b ≤ y
    · rw [if_pos h]
      refine tendsto_const_nhds.congr fun k => ?_
      have e1 : max (y + ε k - X b) 0 = y + ε k - X b := max_eq_left (by linarith [hε0 k])
      have e2 : max (X b - (y + ε k)) 0 = 0 := max_eq_right (by linarith [hε0 k])
      have e3 : max (y - X b) 0 = y - X b := max_eq_left (by linarith)
      have e4 : max (X b - y) 0 = 0 := max_eq_right (by linarith)
      rw [e1, e2, e3, e4]
      field_simp [(hε0 k).ne']
      ring
    · rw [if_neg h]
      rw [not_le] at h
      refine tendsto_const_nhds.congr' ?_
      have hev : ∀ᶠ k in atTop, ε k < X b - y := hε_lim.eventually (gt_mem_nhds (by linarith))
      filter_upwards [hev] with k hk
      have e1 : max (y + ε k - X b) 0 = 0 := max_eq_right (by linarith)
      have e2 : max (X b - (y + ε k)) 0 = X b - (y + ε k) := max_eq_left (by linarith)
      have e3 : max (y - X b) 0 = 0 := max_eq_right (by linarith)
      have e4 : max (X b - y) 0 = X b - y := max_eq_left (by linarith)
      rw [e1, e2, e3, e4]
      field_simp [(hε0 k).ne']
      ring

end nv

end OWMR.L4aux

namespace OWMR.L4aux

lemma one_le_renewal (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (w : ℝ) (hw : 0 < w) :
    1 ≤ renewalMeasure ρ (Set.Ico 0 w) := by
  unfold renewalMeasure
  refine le_trans ?_ (Measure.le_iff'.1 (Measure.le_sum _ 0) _)
  rw [Measure.map_apply (Finset.measurable_sum _ fun j _ =>
    (measurable_pi_apply j).coe_nnreal_real) measurableSet_Ico]
  have : (fun z : Fin 0 → ℝ≥0 => ∑ j, (z j : ℝ)) ⁻¹' Set.Ico 0 w = Set.univ := by
    ext z
    simp [hw]
  rw [this, measure_univ]

lemma nv_neg {β : Type} [MeasurableSpace β] (P : Measure β) [IsProbabilityMeasure P] (X : β → ℝ)
    (hX : Integrable X P) (hX0 : ∀ b, 0 ≤ X b) (H p y : ℝ) (hy : y ≤ 0) :
    nvCost P X H p y = p * (∫ b, X b ∂P - y) := by
  unfold nvCost
  have e : ∀ b, H * max (y - X b) 0 + p * max (X b - y) 0 = p * (X b - y) := fun b => by
    rw [max_eq_right (by linarith [hX0 b]), max_eq_left (by linarith [hX0 b])]
    ring
  simp_rw [e]
  rw [integral_const_mul, integral_sub hX (integrable_const y), integral_const, probReal_univ,
    one_smul]

end OWMR.L4aux

set_option maxHeartbeats 4000000 in
open OWMR.L4aux in
theorem solution {n : ℕ} (hn : 0 < n) (N : Network n) (hN : N.Standing) (m : ℝ)
    (hm : 1 ≤ m) (hhp : N.h ≤ N.p) (c : ConChoice n) (hc : IsConChoice N m c) :
    ∃ a0 : ℝ, 0 ≤ a0 ∧ c.s0 ≤ c.S0 ∧ 0 ≤ c.s0 ∧ N.J0 (conG m * N.K0) ≠ ∞ ∧
      ssAvgCost N.aggregate N.fL0 N.K0 c.s0 c.S0
        ≤ N.J0 (conG m * N.K0) + ENNReal.ofReal (N.h * a0) ∧
      ENNReal.ofReal (N.h * a0 + ⨅ y, N.fL0 y) ≤ N.J0 (conG m * N.K0) ∧
      ssAvgCost N.aggregate (fun y => ((Measure.pi fun _ : Fin N.L0 => N.aggregate)
          {w | y < ∑ j, (w j : ℝ)}).toReal) 0 c.s0 c.S0
        ≤ ENNReal.ofReal (N.h / (N.h + N.p)) := by
  have hh := hN.h_pos
  have hp := hN.p_pos
  obtain ⟨-, hcK0pos, hcK0zero, -⟩ := hc
  set ν := Measure.pi fun _ : Fin N.L0 => N.aggregate with hν
  set X : (Fin N.L0 → ℝ≥0) → ℝ := fun z => ∑ j, (z j : ℝ) with hX
  have hXm : Measurable X := Finset.measurable_sum _ fun j _ =>
    (measurable_pi_apply j).coe_nnreal_real
  have hX0 : ∀ z, 0 ≤ X z := fun z => Finset.sum_nonneg fun j _ => (z j).2
  have hmsum : Measurable fun a : DemandVec n => ∑ i, a i :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have hint_agg : Integrable (fun x : ℝ≥0 => (x : ℝ)) N.aggregate := by
    unfold Network.aggregate
    rw [integrable_map_measure measurable_coe_nnreal_real.aestronglyMeasurable hmsum.aemeasurable]
    have h : Integrable (fun x : DemandVec n => ∑ i, ((x i : ℝ≥0) : ℝ)) N.μ :=
      integrable_finsetSum _ fun i _ => by
        have h1 := integrable_toReal_of_lintegral_ne_top
          (f := fun x : DemandVec n => ((x i : ℝ≥0) : ℝ≥0∞))
          ((measurable_pi_apply i).coe_nnreal_ennreal.aemeasurable) (hN.mean_lt_top i).ne
        simpa using h1
    simpa [Function.comp_def, NNReal.coe_sum] using h
  have hXi : Integrable X ν := by
    refine integrable_finsetSum _ fun j _ => ?_
    have hmp := measurePreserving_eval (μ := fun _ : Fin N.L0 => N.aggregate) j
    exact (hmp.integrable_comp measurable_coe_nnreal_real.aestronglyMeasurable).2 hint_agg
  have hfnv : N.fL0 = nvCost ν X N.h N.p := by
    funext y
    unfold Network.fL0 nvCost whLoss
    congr 1
    funext z
    rw [neg_sub]
  have haggpos : 0 < ∫⁻ y, (y : ℝ≥0∞) ∂N.aggregate := by
    unfold Network.aggregate
    rw [lintegral_map measurable_coe_nnreal_ennreal hmsum]
    have e : ∀ x : DemandVec n, ((∑ i, x i : ℝ≥0) : ℝ≥0∞) = ∑ i, ((x i : ℝ≥0) : ℝ≥0∞) := fun x => by
      push_cast
      rfl
    simp_rw [e]
    rw [lintegral_finsetSum _ fun i _ => (measurable_pi_apply i).coe_nnreal_ennreal]
    exact lt_of_lt_of_le (hN.mean_pos ⟨0, hn⟩)
      (Finset.single_le_sum (f := fun i => ∫⁻ x, ((x i : ℝ≥0) : ℝ≥0∞) ∂N.μ)
        (fun i _ => zero_le) (Finset.mem_univ _))
  have hfc : Continuous N.fL0 := by rw [hfnv]; exact nv_continuous ν X hXi _ _ hh.le hp.le
  have hfcv : ConvexOn ℝ Set.univ N.fL0 := by rw [hfnv]; exact nv_convex ν X hXi _ _ hh.le hp.le
  have hf0 : ∀ y, 0 ≤ N.fL0 y := fun y => by rw [hfnv]; exact nv_nonneg ν X _ _ _ hh.le hp.le
  have hfco : ∀ C : ℝ, ∃ R : ℝ, ∀ y, R ≤ |y| → C ≤ N.fL0 y := by
    rw [hfnv]; exact nv_coercive ν X hXi _ _ hh hp
  have hfa : AntitoneOn N.fL0 (Set.Iic 0) := by rw [hfnv]; exact nv_anti ν X hXi hX0 _ _ hp.le
  have hslope : ∀ y a, 0 ≤ a → N.fL0 (y + a) ≤ N.fL0 y + N.h * a := fun y a ha => by
    rw [hfnv]; exact nv_slope ν X hXi _ _ hh.le hp.le y a ha
  have hlip : ∀ y y', |N.fL0 y - N.fL0 y'| ≤ (N.h + N.p) * |y - y'| := fun y y' => by
    rw [hfnv]; exact nv_lip ν X hXi _ _ hh.le hp.le y y'
  have hderiv : ∀ y, Tendsto (fun k : ℕ => (N.fL0 (y + 1 / ((k : ℝ) + 1)) - N.fL0 y)
      / (1 / ((k : ℝ) + 1))) atTop (𝓝 (N.h - (N.h + N.p) * ν.real {z | y < X z})) := fun y => by
    rw [hfnv]; exact nv_deriv ν X hXi hXm _ _ hh.le hp.le y
  have hinf_le : ∀ y, (⨅ y, N.fL0 y) ≤ N.fL0 y := fun y =>
    ciInf_le ⟨0, by rintro _ ⟨z, rfl⟩; exact hf0 z⟩ y
  set gsh : ℝ → ℝ := fun y => (ν {w | y < X w}).toReal with hgsh
  have hgsh_anti : Antitone gsh := fun a b hab => by
    simp only [hgsh]
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono fun z (hz : b < X z) => (lt_of_le_of_lt hab hz : a < X z))
  have hgsh01 : ∀ y, 0 ≤ gsh y ∧ gsh y ≤ 1 := fun y => ⟨ENNReal.toReal_nonneg, by
    simp only [hgsh]
    have := prob_le_one (μ := ν) (s := {w | y < X w})
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)⟩
  have hgsh_meas : Measurable gsh := hgsh_anti.measurable
  -- the value is finite
  have hgm : 1 ≤ conG m := by
    unfold conG conGammaBar
    have : 0 ≤ 32 / (57 * m) := by positivity
    linarith
  obtain ⟨J, hJ0, hJeq, -⟩ := sl_subsolution N.aggregate haggpos N.fL0 hfc hfcv hf0 hfco hfa
    (conG m * N.K0) (mul_nonneg (by linarith) hN.K0_nonneg)
  have hJ0ne : N.J0 (conG m * N.K0) ≠ ∞ := by
    show slValue N.aggregate N.fL0 (conG m * N.K0) ≠ ∞
    rw [hJeq]; exact ENNReal.ofReal_ne_top
  have hfm : Measurable N.fL0 := hfc.measurable
  set U := renewalMeasure N.aggregate with hU
  have hUfin : ∀ w, U (Set.Ico 0 w) < ∞ := fun w => renewalMeasure_Ico_lt_top N.aggregate haggpos w
  have hInt : ∀ (w : ℝ) (f : ℝ → ℝ) (B : ℝ), Measurable f → (∀ x ∈ Set.Ico (0 : ℝ) w, ‖f x‖ ≤ B) →
      IntegrableOn f (Set.Ico 0 w) U := fun w f B hf hb =>
    Measure.integrableOn_of_bounded (hUfin w).ne hf.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ico).2 (Filter.Eventually.of_forall hb))
  have hderiv' : ∀ y, Tendsto (fun k : ℕ => (N.fL0 (y + 1 / ((k : ℝ) + 1)) - N.fL0 y)
      / (1 / ((k : ℝ) + 1))) atTop (𝓝 (N.h - (N.h + N.p) * gsh y)) := fun y => hderiv y
  rcases eq_or_lt_of_le hN.K0_nonneg with hK0 | hK0
  · -- zero supplier setup cost: base stock at a minimizer of `f_{L₀}`
    obtain ⟨hsS0, hS0nn, hmin⟩ := hcK0zero hK0.symm
    have hfS0 : N.fL0 c.S0 ≤ ⨅ y, N.fL0 y := le_ciInf hmin
    have hgK0 : 0 ≤ conG m * N.K0 := mul_nonneg (by linarith) hN.K0_nonneg
    have hss0 : ssAvgCost N.aggregate N.fL0 N.K0 c.s0 c.S0 = ENNReal.ofReal (N.fL0 c.S0) := by
      rw [← hK0, hsS0, ss_SS]
    refine ⟨0, le_rfl, hsS0.le, by rw [hsS0]; exact hS0nn, hJ0ne, ?_, ?_, ?_⟩
    · rw [hss0]
      calc ENNReal.ofReal (N.fL0 c.S0) ≤ ENNReal.ofReal (⨅ y, N.fL0 y) :=
            ENNReal.ofReal_le_ofReal hfS0
        _ ≤ N.J0 (conG m * N.K0) := value_ge_inf _ _ hf0 _ hgK0
        _ ≤ _ := le_self_add
    · rw [mul_zero, zero_add]
      exact value_ge_inf _ _ hf0 _ hgK0
    · show ssAvgCost N.aggregate gsh 0 c.s0 c.S0 ≤ _
      rw [hsS0, ss_SS]
      refine ENNReal.ofReal_le_ofReal ?_
      -- first-order condition at the minimizer
      have hge : 0 ≤ N.h - (N.h + N.p) * gsh c.S0 := by
        refine ge_of_tendsto (hderiv' c.S0) (Filter.Eventually.of_forall fun k => ?_)
        have hε : 0 < 1 / ((k : ℝ) + 1) := by positivity
        exact div_nonneg (sub_nonneg.2 (hmin _)) hε.le
      rw [le_div_iff₀ (by linarith)]
      have : (N.h + N.p) * gsh c.S0 ≤ N.h := by linarith
      calc gsh c.S0 * (N.h + N.p) = (N.h + N.p) * gsh c.S0 := mul_comm _ _
        _ ≤ N.h := this
  · -- positive supplier setup cost: shifted canonical policy
    obtain ⟨sh, Sh, hcan, hs0, hS0⟩ := hcK0pos hK0
    obtain ⟨hsS, hss, hfs, hfS, hfI⟩ := hcan
    set gK := conG m * N.K0 with hgK
    have hgK0 : 0 ≤ gK := mul_nonneg (by linarith) hN.K0_nonneg
    have hKle : N.K0 ≤ gK := by
      have := mul_le_mul_of_nonneg_right hgm hN.K0_nonneg
      rw [one_mul] at this
      exact this
    set a0 := max (-sh) 0 with ha0
    have ha00 : 0 ≤ a0 := le_max_right _ _
    have hna : -sh ≤ a0 := le_max_left _ _
    set w := Sh - sh with hw
    have hw0 : 0 < w := by rw [hw]; linarith
    have hwS0 : c.S0 - c.s0 = w := by rw [hs0, hS0, hw]; ring
    set M := (U (Set.Ico 0 w)).toReal with hM
    have hM1 : 1 ≤ M := by
      have h1 : (1 : ℝ≥0∞) ≤ U (Set.Ico 0 w) := one_le_renewal N.aggregate w hw0
      have h2 := ENNReal.toReal_mono (hUfin w).ne h1
      rwa [ENNReal.toReal_one] at h2
    have hM0 : 0 < M := by linarith
    have hUreal : U.real (Set.Ico 0 w) = M := rfl
    have iC : ∀ c : ℝ, IntegrableOn (fun _ : ℝ => c) (Set.Ico 0 w) U := fun c =>
      hInt w _ |c| measurable_const fun x _ => le_of_eq (Real.norm_eq_abs c)
    have hfJ : ∀ y ∈ Set.Icc sh Sh, N.fL0 y ≤ J := fun y hy => by
      have := hfI y hy
      rw [hJeq] at this
      exact (ENNReal.ofReal_le_ofReal_iff hJ0).1 this
    -- renewal-reward form of the canonical value
    have hrr0 := ss_renewal_reward N.aggregate haggpos N.fL0 hfm hf0 gK sh Sh hgK0 hsS ⟨J, hfJ⟩
    rw [hss, ← hw, ← hU, ← hM] at hrr0
    have hI0int : IntegrableOn (fun x => N.fL0 (Sh - x)) (Set.Ico 0 w) U :=
      hInt w _ J (hfm.comp (measurable_const.sub measurable_id)) fun x hx => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 _)]
        exact hfJ _ ⟨by linarith [hx.2, hw], by linarith [hx.1]⟩
    have hshift : ∀ x, Sh - x + a0 = c.S0 - x := fun x => by rw [hS0]; ring
    have hI1int : IntegrableOn (fun x => N.fL0 (c.S0 - x)) (Set.Ico 0 w) U :=
      hInt w _ (J + N.h * a0) (hfm.comp (measurable_const.sub measurable_id)) fun x hx => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 _)]
        have h1 := hslope (Sh - x) a0 ha00
        have h2 := hfJ (Sh - x) ⟨by linarith [hx.2, hw], by linarith [hx.1]⟩
        rw [hshift] at h1
        linarith
    have hI1le : ∫ x in Set.Ico 0 w, N.fL0 (c.S0 - x) ∂U
        ≤ ∫ x in Set.Ico 0 w, N.fL0 (Sh - x) ∂U + N.h * a0 * M := by
      have h : ∫ x in Set.Ico 0 w, N.fL0 (c.S0 - x) ∂U
          ≤ ∫ x in Set.Ico 0 w, (N.fL0 (Sh - x) + N.h * a0) ∂U :=
        setIntegral_mono_on hI1int (hI0int.add (iC (N.h * a0))) measurableSet_Ico fun x _ => by
          have h1 := hslope (Sh - x) a0 ha00
          rw [hshift] at h1
          exact h1
      rw [integral_add hI0int (iC (N.h * a0)), setIntegral_const, hUreal, smul_eq_mul] at h
      linarith
    have hbf0 : ∃ C, ∀ y ∈ Set.Icc c.s0 c.S0, N.fL0 y ≤ C := ⟨J + N.h * a0, fun y hy => by
      have h1 := hslope (y - a0) a0 ha00
      rw [sub_add_cancel] at h1
      have h2 := hfJ (y - a0) ⟨by linarith [hy.1, hs0], by linarith [hy.2, hS0]⟩
      linarith⟩
    have hrr1 := ss_renewal_reward N.aggregate haggpos N.fL0 hfm hf0 N.K0 c.s0 c.S0
      hN.K0_nonneg (by rw [hs0, hS0]; linarith) hbf0
    rw [hwS0, ← hU, ← hM] at hrr1
    -- the shifted windows `(ŝ₀ + ε, Ŝ₀ + ε)` cost at least the canonical one
    have hQ : ∀ k : ℕ, 0 ≤ ∫ x in Set.Ico 0 w,
        (N.fL0 (Sh - x + 1 / ((k : ℝ) + 1)) - N.fL0 (Sh - x)) / (1 / ((k : ℝ) + 1)) ∂U := by
      intro k
      set ε : ℝ := 1 / ((k : ℝ) + 1) with hε
      have hε0 : 0 < ε := by positivity
      have hle := value_le_ss N.aggregate haggpos N.fL0 hfc hfcv hf0 hfco hfa gK hgK0
        (sh + ε) (Sh + ε) (by linarith)
      have hbfe : ∃ C, ∀ y ∈ Set.Icc (sh + ε) (Sh + ε), N.fL0 y ≤ C := ⟨J + N.h * ε, fun y hy => by
        have h1 := hslope (y - ε) ε hε0.le
        rw [sub_add_cancel] at h1
        have h2 := hfJ (y - ε) ⟨by linarith [hy.1], by linarith [hy.2]⟩
        linarith⟩
      have hrr2 := ss_renewal_reward N.aggregate haggpos N.fL0 hfm hf0 gK (sh + ε) (Sh + ε) hgK0
        (by linarith) hbfe
      have hwe : Sh + ε - (sh + ε) = w := by rw [hw]; ring
      have hcomm : ∀ x, Sh + ε - x = Sh - x + ε := fun x => by ring
      rw [hwe, ← hU, ← hM] at hrr2
      simp only [hcomm] at hrr2
      rw [hrr2, hrr0] at hle
      have hIεint : IntegrableOn (fun x => N.fL0 (Sh - x + ε)) (Set.Ico 0 w) U :=
        hInt w _ (J + N.h * ε) (hfm.comp ((measurable_const.sub measurable_id).add measurable_const))
          fun x hx => by
            rw [Real.norm_eq_abs, abs_of_nonneg (hf0 _)]
            have h1 := hslope (Sh - x) ε hε0.le
            have h2 := hfJ (Sh - x) ⟨by linarith [hx.2, hw], by linarith [hx.1]⟩
            linarith
      have hIε0 : 0 ≤ ∫ x in Set.Ico 0 w, N.fL0 (Sh - x + ε) ∂U :=
        setIntegral_nonneg measurableSet_Ico fun x _ => hf0 _
      have h3 := (ENNReal.ofReal_le_ofReal_iff (div_nonneg (by linarith) hM0.le)).1 hle
      have h4 : ∫ x in Set.Ico 0 w, N.fL0 (Sh - x) ∂U ≤ ∫ x in Set.Ico 0 w, N.fL0 (Sh - x + ε) ∂U := by
        have := (div_le_div_iff_of_pos_right hM0).1 h3
        linarith
      rw [integral_div, integral_sub hIεint hI0int]
      exact div_nonneg (by linarith) hε0.le
    -- dominated convergence for the difference quotients
    have hlimint : Tendsto (fun k : ℕ => ∫ x in Set.Ico 0 w,
        (N.fL0 (Sh - x + 1 / ((k : ℝ) + 1)) - N.fL0 (Sh - x)) / (1 / ((k : ℝ) + 1)) ∂U) atTop
        (𝓝 (∫ x in Set.Ico 0 w, (N.h - (N.h + N.p) * gsh (Sh - x)) ∂U)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => N.h + N.p) (fun k => ?_)
        (iC (N.h + N.p)) (fun k => Filter.Eventually.of_forall fun x => ?_)
        (Filter.Eventually.of_forall fun x => hderiv' (Sh - x))
      · exact (((hfc.comp ((continuous_const.sub continuous_id).add continuous_const)).sub
          (hfc.comp (continuous_const.sub continuous_id))).div_const _).aestronglyMeasurable
      · have hε0 : 0 < 1 / ((k : ℝ) + 1) := by positivity
        show ‖(N.fL0 (Sh - x + 1 / ((k : ℝ) + 1)) - N.fL0 (Sh - x)) / (1 / ((k : ℝ) + 1))‖
          ≤ N.h + N.p
        rw [Real.norm_eq_abs, abs_div, abs_of_pos hε0, div_le_iff₀ hε0]
        have := hlip (Sh - x + 1 / ((k : ℝ) + 1)) (Sh - x)
        rw [show Sh - x + 1 / ((k : ℝ) + 1) - (Sh - x) = 1 / ((k : ℝ) + 1) by ring,
          abs_of_pos hε0] at this
        exact this
    have hge : 0 ≤ ∫ x in Set.Ico 0 w, (N.h - (N.h + N.p) * gsh (Sh - x)) ∂U :=
      ge_of_tendsto hlimint (Filter.Eventually.of_forall hQ)
    have hgint : IntegrableOn (fun x => gsh (Sh - x)) (Set.Ico 0 w) U :=
      hInt w _ 1 (hgsh_meas.comp (measurable_const.sub measurable_id)) fun x _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hgsh01 _).1]
        exact (hgsh01 _).2
    have hgint0 : IntegrableOn (fun x => gsh (c.S0 - x)) (Set.Ico 0 w) U :=
      hInt w _ 1 (hgsh_meas.comp (measurable_const.sub measurable_id)) fun x _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hgsh01 _).1]
        exact (hgsh01 _).2
    have hsplit : ∫ x in Set.Ico 0 w, (N.h - (N.h + N.p) * gsh (Sh - x)) ∂U
        = N.h * M - (N.h + N.p) * ∫ x in Set.Ico 0 w, gsh (Sh - x) ∂U := by
      rw [integral_sub (iC N.h) (hgint.const_mul _), integral_const_mul, setIntegral_const,
        hUreal, smul_eq_mul, mul_comm M N.h]
    have hgbound : (N.h + N.p) * ∫ x in Set.Ico 0 w, gsh (Sh - x) ∂U ≤ N.h * M := by
      linarith
    refine ⟨a0, ha00, by rw [hs0, hS0]; linarith, by rw [hs0]; linarith, hJ0ne, ?_, ?_, ?_⟩
    · -- (i) supplier costs
      rw [hrr1]
      have hJ0eq : N.J0 gK = ENNReal.ofReal ((gK + ∫ x in Set.Ico 0 w, N.fL0 (Sh - x) ∂U) / M) :=
        hrr0
      rw [hJ0eq]
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) ENNReal.ofReal_add_le
      rw [div_add' _ _ _ hM0.ne', div_le_div_iff_of_pos_right hM0]
      linarith
    · -- (ii) `h a₀ + C₀ ≤ G₀`
      have hJs : N.J0 gK = ENNReal.ofReal (N.fL0 sh) := hfs.symm
      rw [hJs]
      refine ENNReal.ofReal_le_ofReal ?_
      rcases lt_or_ge sh 0 with hsh | hsh
      · have ha : a0 = -sh := max_eq_left (by linarith)
        have h1 : N.fL0 sh = N.p * (∫ z, X z ∂ν - sh) := by
          rw [hfnv]; exact nv_neg ν X hXi hX0 _ _ sh hsh.le
        have h2 : N.fL0 0 = N.p * (∫ z, X z ∂ν - 0) := by
          rw [hfnv]; exact nv_neg ν X hXi hX0 _ _ 0 le_rfl
        calc N.h * a0 + ⨅ y, N.fL0 y ≤ N.p * a0 + N.fL0 0 :=
              add_le_add (mul_le_mul_of_nonneg_right hhp ha00) (hinf_le 0)
          _ = N.fL0 sh := by rw [h1, h2, ha]; ring
      · have ha : a0 = 0 := max_eq_right (by linarith)
        rw [ha, mul_zero, zero_add]
        exact hinf_le sh
    · -- (iii) shortage frequency
      show ssAvgCost N.aggregate gsh 0 c.s0 c.S0 ≤ _
      have hrr3 := ss_renewal_reward N.aggregate haggpos gsh hgsh_meas (fun y => (hgsh01 y).1) 0
        c.s0 c.S0 le_rfl (by rw [hs0, hS0]; linarith) ⟨1, fun y _ => (hgsh01 y).2⟩
      rw [hwS0, ← hU, ← hM] at hrr3
      rw [hrr3]
      refine ENNReal.ofReal_le_ofReal ?_
      have hmono : ∫ x in Set.Ico 0 w, gsh (c.S0 - x) ∂U ≤ ∫ x in Set.Ico 0 w, gsh (Sh - x) ∂U :=
        setIntegral_mono_on hgint0 hgint measurableSet_Ico fun x _ =>
          hgsh_anti (by linarith [hS0])
      rw [zero_add, div_le_div_iff₀ hM0 (by linarith)]
      nlinarith
