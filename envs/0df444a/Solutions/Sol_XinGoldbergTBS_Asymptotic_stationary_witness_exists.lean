-- Prove2me | solution 1 for XinGoldbergTBS.Asymptotic.stationary_witness_exists
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-17T10:02:06.036533+00:00
-- url     : https://prove2.me/submissions/7f4d4f91-21d1-4073-ae54-517cf949c635

import Mathlib
import Definitions.Def_XinGoldbergTBS_Asymptotic_Model
import Definitions.Def_XinGoldbergTBS_Asymptotic_Witness
import Definitions.Def_XinGoldbergTBS_Asymptotic_Constants

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction

namespace XGOB

open XinGoldbergTBS.Asymptotic

lemma ae_nonneg (μ : DemandLaw) : ∀ᵐ d ∂μ.law, 0 ≤ d := by
  have h := μ.nonneg
  rw [measure_eq_zero_iff_ae_notMem] at h
  filter_upwards [h] with d hd
  simpa using hd

lemma G_nonneg (κ : Costs) (z : ℝ) : 0 ≤ G κ z := by
  unfold G
  have := κ.h_pos; have := κ.b_pos
  positivity

lemma G_ge (κ : Costs) (z : ℝ) : min κ.b κ.h * |z| ≤ G κ z := by
  unfold G
  have hb := min_le_left κ.b κ.h
  have hh := min_le_right κ.b κ.h
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz, max_eq_left hz, max_eq_right (by linarith : -z ≤ 0)]
    nlinarith
  · rw [abs_of_nonpos hz, max_eq_right hz, max_eq_left (by linarith : 0 ≤ -z)]
    nlinarith

lemma G_le (κ : Costs) (z : ℝ) : G κ z ≤ max κ.b κ.h * |z| := by
  unfold G
  have hb := le_max_left κ.b κ.h
  have hh := le_max_right κ.b κ.h
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz, max_eq_left hz, max_eq_right (by linarith : -z ≤ 0)]
    nlinarith
  · rw [abs_of_nonpos hz, max_eq_right hz, max_eq_left (by linarith : 0 ≤ -z)]
    nlinarith

lemma G_lip (κ : Costs) (a c : ℝ) : G κ a ≤ G κ c + max κ.b κ.h * |a - c| := by
  unfold G
  have hb := le_max_left κ.b κ.h
  have hh := le_max_right κ.b κ.h
  have hbp := κ.b_pos
  have hhp := κ.h_pos
  have h1 := le_abs_self (a - c)
  have h2 := neg_abs_le (a - c)
  have h3 := abs_nonneg (a - c)
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 c with hc | hc
  · rw [max_eq_left ha, max_eq_right (by linarith : -a ≤ 0), max_eq_left hc,
      max_eq_right (by linarith : -c ≤ 0)]
    nlinarith
  · rw [max_eq_left ha, max_eq_right (by linarith : -a ≤ 0), max_eq_right hc,
      max_eq_left (by linarith : 0 ≤ -c)]
    nlinarith
  · rw [max_eq_right ha, max_eq_left (by linarith : 0 ≤ -a), max_eq_left hc,
      max_eq_right (by linarith : -c ≤ 0)]
    nlinarith
  · rw [max_eq_right ha, max_eq_left (by linarith : 0 ≤ -a), max_eq_right hc,
      max_eq_left (by linarith : 0 ≤ -c)]
    nlinarith

lemma continuous_G (κ : Costs) : Continuous (G κ) := by
  unfold G
  exact (continuous_const.mul (continuous_id.max continuous_const)).add
    (continuous_const.mul (continuous_neg.max continuous_const))

instance sumLaw_isProb (μ : DemandLaw) (L₀ : ℕ) : IsProbabilityMeasure (sumLaw μ L₀) := by
  unfold sumLaw; infer_instance

lemma integrable_coord (μ : DemandLaw) (L₀ : ℕ) (i : Fin (L₀ + 1)) :
    Integrable (fun y : Fin (L₀ + 1) → ℝ => y i) (sumLaw μ L₀) := by
  unfold sumLaw
  exact integrable_comp_eval (μ := fun _ : Fin (L₀ + 1) => μ.law) (f := fun d : ℝ => d) μ.integrable

lemma integrable_shift (μ : DemandLaw) (L₀ : ℕ) (x : ℝ) :
    Integrable (fun y : Fin (L₀ + 1) → ℝ => x - ∑ i, y i) (sumLaw μ L₀) :=
  (integrable_const x).sub (integrable_finsetSum _ fun i _ => integrable_coord μ L₀ i)

lemma integrable_G_sum (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (x : ℝ) :
    Integrable (fun y : Fin (L₀ + 1) → ℝ => G κ (x - ∑ i, y i)) (sumLaw μ L₀) := by
  have hs := integrable_shift μ L₀ x
  refine Integrable.mono' (hs.norm.const_mul (max κ.b κ.h)) ?_ ?_
  · exact ((continuous_G κ).measurable.comp_aemeasurable hs.aemeasurable).aestronglyMeasurable
  · exact Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (G_nonneg _ _), Real.norm_eq_abs]
      exact G_le κ _

instance ghat_isProb : IsProbabilityMeasure ghatLaw := by
  constructor
  unfold ghatLaw
  rw [Measure.sum_apply _ MeasurableSet.univ]
  have h : ∀ i : ℕ, ((2 : ℝ≥0∞) ^ (i + 1))⁻¹ = 2⁻¹ * (2⁻¹) ^ i := by
    intro i; rw [ENNReal.inv_pow, pow_succ, mul_comm]
  calc _ = ∑' i : ℕ, ((2 : ℝ≥0∞) ^ (i + 1))⁻¹ := by simp
    _ = 1 := by
      simp only [h]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
        ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

instance pathLaw_isProb (μ : DemandLaw) : IsProbabilityMeasure (pathLaw μ) := by
  unfold pathLaw; infer_instance

instance sampleLaw_isProb (μ : DemandLaw) : IsProbabilityMeasure (sampleLaw μ) := by
  unfold sampleLaw; infer_instance

lemma measurable_initState : Measurable (fun ω : Sample => initState ω) := by
  unfold initState
  refine measurable_const.prodMk (measurable_const.prodMk ?_)
  have : Measurable (fun q : Path × ℕ => -∑ i ∈ Finset.range q.2, q.1 i) := by
    refine measurable_from_prod_countable_left fun k => ?_
    simp only
    exact (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).neg
  exact this.comp measurable_snd

lemma measurable_step (L₀ L t : ℕ) :
    Measurable (fun q : (ℝ≥0 × ℝ≥0) × ℝ × State => step L₀ L t q.1 q.2.1 q.2.2) := by
  unfold step; fun_prop

lemma measurable_observe (L₀ L t : ℕ) : Measurable (observe L₀ L t) := by
  unfold observe; fun_prop

lemma measurable_run {L₀ L : ℕ} (π : AdmissiblePolicy L₀ L) (n : ℕ) :
    Measurable (fun ω : Sample => run π ω n) := by
  induction n with
  | zero => exact measurable_initState
  | succ n ih =>
    have h1 : Measurable (fun ω : Sample => π.f (n + 1) (observe L₀ L (n + 1) (run π ω n))) :=
      (π.measurable_f _).comp ((measurable_observe _ _ _).comp ih)
    have h2 : Measurable (fun ω : Sample => ω.1 n) := (measurable_pi_apply n).comp measurable_fst
    exact (measurable_step L₀ L (n + 1)).comp (h1.prodMk (h2.prodMk ih))

/-- Replace the coordinates `m ≤ n < m + k` of `p` by those of `y`. -/
def mix (m k : ℕ) (p y : Path) : Path := fun n => if m ≤ n ∧ n < m + k then y n else p n

lemma measurable_mix (m k : ℕ) : Measurable (fun q : Path × Path => mix m k q.1 q.2) := by
  refine measurable_pi_lambda _ fun n => ?_
  by_cases h : m ≤ n ∧ n < m + k
  · simp only [mix, h, and_self, if_true]; fun_prop
  · simp only [mix, h, if_false]; fun_prop

lemma mp_mix (μ : DemandLaw) (m k : ℕ) :
    MeasurePreserving (fun q : Path × Path => mix m k q.1 q.2)
      ((pathLaw μ).prod (pathLaw μ)) (pathLaw μ) := by
  refine ⟨measurable_mix m k, ?_⟩
  conv_rhs => rw [pathLaw]
  apply Measure.eq_infinitePi
  intro s t ht
  classical
  rw [Measure.map_apply (measurable_mix m k) (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
  have hpre : (fun q : Path × Path => mix m k q.1 q.2) ⁻¹' (Set.pi (↑s) t) =
      (Set.pi ↑(s.filter (fun i => ¬ (m ≤ i ∧ i < m + k))) t) ×ˢ
        (Set.pi ↑(s.filter (fun i => m ≤ i ∧ i < m + k)) t) := by
    ext ⟨p, y⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Finset.coe_filter, Set.mem_setOf_eq,
      Finset.mem_coe, mix]
    constructor
    · intro h
      exact ⟨fun i ⟨hi, hw⟩ => by simpa [hw] using h i hi,
        fun i ⟨hi, hw⟩ => by simpa [hw] using h i hi⟩
    · rintro ⟨h1, h2⟩ i hi
      by_cases hw : m ≤ i ∧ i < m + k
      · simpa [hw] using h2 i ⟨hi, hw⟩
      · simpa [hw] using h1 i ⟨hi, hw⟩
  rw [hpre, Measure.prod_prod]
  unfold pathLaw
  rw [Measure.infinitePi_pi _ (fun i _ => ht i), Measure.infinitePi_pi _ (fun i _ => ht i), mul_comm,
    Finset.prod_filter_mul_prod_filter_not]

lemma mp_window (μ : DemandLaw) (L₀ m : ℕ) :
    MeasurePreserving (fun p : Path => fun j : Fin (L₀ + 1) => p (m + j))
      (pathLaw μ) (sumLaw μ L₀) := by
  refine ⟨by fun_prop, ?_⟩
  unfold sumLaw
  refine (Measure.pi_eq fun s hs => ?_).symm
  classical
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
  set T : ℕ → Set ℝ := fun n =>
    if h : m ≤ n ∧ n < m + (L₀ + 1) then s ⟨n - m, by omega⟩ else Set.univ with hTdef
  have hT : ∀ j : Fin (L₀ + 1), T (m + j) = s j := by
    intro j
    simp only [hTdef]
    rw [dif_pos (by omega)]
    congr 1; ext; simp
  have hpre : (fun p : Path => fun j : Fin (L₀ + 1) => p (m + j)) ⁻¹' Set.univ.pi s =
      Set.pi ↑(Finset.univ.image (fun j : Fin (L₀ + 1) => m + (j : ℕ))) T := by
    ext p
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_pi, Finset.coe_image, Finset.coe_univ,
      Set.image_univ, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff, hT]
    exact ⟨fun h a => h a (Set.mem_univ _), fun h a _ => h a⟩
  have hTm : ∀ n, MeasurableSet (T n) := by
    intro n; simp only [hTdef]; split_ifs
    · exact hs _
    · exact MeasurableSet.univ
  rw [hpre]
  unfold pathLaw
  rw [Measure.infinitePi_pi _ (fun n _ => hTm n),
    Finset.prod_image (fun a _ b _ h => by ext; simpa using h)]
  exact Finset.prod_congr rfl fun j _ => by rw [hT j]

lemma lintegral_mix (μ : DemandLaw) (m k : ℕ) {f : Sample → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, f ω ∂sampleLaw μ =
      ∫⁻ ω, ∫⁻ y, f (mix m k ω.1 y, ω.2) ∂pathLaw μ ∂sampleLaw μ := by
  have hg : Measurable (fun q : Sample × Path => f (mix m k q.1.1 q.2, q.1.2)) :=
    hf.comp (((measurable_mix m k).comp (measurable_fst.fst.prodMk measurable_snd)).prodMk
      measurable_fst.snd)
  have hF : Measurable (fun p : Path => ∫⁻ r, f (p, r) ∂((pathLaw μ).prod ghatLaw)) :=
    hf.lintegral_prod_right'
  unfold sampleLaw
  have hFm : Measurable (fun a : Path × Path =>
      ∫⁻ r, f (mix m k a.1 a.2, r) ∂((pathLaw μ).prod ghatLaw)) := hF.comp (measurable_mix m k)
  rw [lintegral_prod _ hf.aemeasurable, lintegral_prod _ hg.lintegral_prod_right'.aemeasurable,
    ← (mp_mix μ m k).lintegral_comp hF, lintegral_prod _ hFm.aemeasurable]
  refine lintegral_congr fun p => ?_
  simp only
  refine lintegral_lintegral_swap ?_
  exact (hf.comp (((measurable_mix m k).comp (measurable_const.prodMk measurable_fst)).prodMk
    measurable_snd)).aemeasurable

lemma run_local {L₀ L : ℕ} (π : AdmissiblePolicy L₀ L) (ω ω' : Sample) (h2 : ω.2 = ω'.2)
    (m : ℕ) (h1 : ∀ n < m, ω.1 n = ω'.1 n) : ∀ j ≤ m, run π ω j = run π ω' j := by
  intro j hj
  induction j with
  | zero => simp only [run, initState, h2]
  | succ j ih => simp only [run]; rw [ih (by omega), h1 j (by omega)]

lemma run_shift {L₀ L : ℕ} (π : AdmissiblePolicy L₀ L) (hL : L₀ ≤ L) (hL1 : 1 ≤ L)
    (ω ω' : Sample) (h2 : ω.2 = ω'.2)
    (m : ℕ) (h1 : ∀ n < m, ω.1 n = ω'.1 n) (n : ℕ) (hn1 : m + 1 ≤ n) (hn2 : n ≤ m + L₀ + 1) :
    (∀ i : ℤ, i ≤ (m : ℤ) + 1 →
        (run π ω n).1 i = (run π ω' n).1 i ∧ (run π ω n).2.1 i = (run π ω' n).2.1 i) ∧
      (run π ω n).2.2 + ∑ k ∈ Finset.range n, ω.1 k =
        (run π ω' n).2.2 + ∑ k ∈ Finset.range n, ω'.1 k := by
  induction n, hn1 using Nat.le_induction with
  | base =>
    have hm := run_local π ω ω' h2 m h1 m le_rfl
    simp only [run]
    rw [hm]
    refine ⟨fun i _ => ⟨rfl, rfl⟩, ?_⟩
    simp only [step, Finset.sum_range_succ]
    rw [Finset.sum_congr rfl (fun k hk => h1 k (Finset.mem_range.1 hk))]
    ring
  | succ n hn ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    simp only [run]
    refine ⟨fun i hi => ?_, ?_⟩
    · have hne : i ≠ ((n + 1 : ℕ) : ℤ) := by omega
      simp only [step, Function.update_apply, hne, if_false]
      exact ih1 i hi
    · have hR : ((n + 1 : ℕ) : ℤ) - L ≠ ((n + 1 : ℕ) : ℤ) := by omega
      have hE : ((n + 1 : ℕ) : ℤ) - L₀ ≠ ((n + 1 : ℕ) : ℤ) := by omega
      simp only [step, Function.update_apply, Finset.sum_range_succ, hR, hE, if_false]
      have e1 := (ih1 (((n + 1 : ℕ) : ℤ) - L) (by omega)).1
      have e2 := (ih1 (((n + 1 : ℕ) : ℤ) - L₀) (by omega)).2
      rw [e1, e2]
      linarith

lemma run_mix_inv {L₀ L : ℕ} (π : AdmissiblePolicy L₀ L) (hL : L₀ ≤ L) (hL1 : 1 ≤ L)
    (ω : Sample) (y : Path) (m : ℕ) :
    (run π (mix m (L₀ + 1) ω.1 y, ω.2) (m + L₀ + 1)).2.2 =
      (run π ω (m + L₀ + 1)).2.2 + ∑ j : Fin (L₀ + 1), ω.1 (m + j)
        - ∑ j : Fin (L₀ + 1), y (m + j) := by
  have h1 : ∀ n < m, ω.1 n = (mix m (L₀ + 1) ω.1 y, ω.2).1 n := by
    intro n hn; simp only [mix]; rw [if_neg (by omega)]
  obtain ⟨-, h⟩ := run_shift π hL hL1 ω (mix m (L₀ + 1) ω.1 y, ω.2) rfl m h1 (m + L₀ + 1)
    (by omega) le_rfl
  rw [show m + L₀ + 1 = m + (L₀ + 1) by ring, Finset.sum_range_add _ m (L₀ + 1),
    Finset.sum_range_add _ m (L₀ + 1)] at h
  rw [Finset.sum_congr rfl (fun k hk => (h1 k (Finset.mem_range.1 hk)).symm)] at h
  have h3 : ∑ x ∈ Finset.range (L₀ + 1), (mix m (L₀ + 1) ω.1 y, ω.2).1 (m + x) =
      ∑ x ∈ Finset.range (L₀ + 1), y (m + x) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    have := Finset.mem_range.1 hx
    simp only [mix]; rw [if_pos (by omega)]
  rw [h3] at h
  rw [Fin.sum_univ_eq_sum_range (fun j => ω.1 (m + j)), Fin.sum_univ_eq_sum_range (fun j => y (m + j))]
  rw [show m + (L₀ + 1) = m + L₀ + 1 by ring] at h
  linarith

lemma gConst_le (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (x : ℝ) :
    gConst μ κ L₀ ≤ ∫ y, G κ (x - ∑ i, y i) ∂sumLaw μ L₀ := by
  refine ciInf_le ⟨0, ?_⟩ x
  rintro _ ⟨z, rfl⟩
  exact integral_nonneg fun _ => G_nonneg _ _

lemma period_lower (μ : DemandLaw) (κ : Costs) {L₀ L : ℕ} (π : AdmissiblePolicy L₀ L)
    (hL : L₀ ≤ L) (hL1 : 1 ≤ L) (t : ℕ) (ht : L₀ + 1 ≤ t) :
    ENNReal.ofReal (gConst μ κ L₀) ≤ ∫⁻ ω, periodCost κ π ω t ∂sampleLaw μ := by
  obtain ⟨m, rfl⟩ : ∃ m, t = m + L₀ + 1 := ⟨t - L₀ - 1, by omega⟩
  set F : Sample → ℝ≥0∞ := fun ω => ENNReal.ofReal (G κ (run π ω (m + L₀ + 1)).2.2) with hFdef
  have hF : Measurable F :=
    ENNReal.measurable_ofReal.comp ((continuous_G κ).measurable.comp
      (measurable_run π _).snd.snd)
  calc ENNReal.ofReal (gConst μ κ L₀)
      = ∫⁻ _ω, ENNReal.ofReal (gConst μ κ L₀) ∂sampleLaw μ := by simp
    _ ≤ ∫⁻ ω, ∫⁻ y, F (mix m (L₀ + 1) ω.1 y, ω.2) ∂pathLaw μ ∂sampleLaw μ := by
        refine lintegral_mono fun ω => ?_
        set X := (run π ω (m + L₀ + 1)).2.2 + ∑ j : Fin (L₀ + 1), ω.1 (m + j)
        have hrw : ∀ y, F (mix m (L₀ + 1) ω.1 y, ω.2) =
            (fun z : Fin (L₀ + 1) → ℝ => ENNReal.ofReal (G κ (X - ∑ i, z i)))
              (fun j : Fin (L₀ + 1) => y (m + j)) := by
          intro y; simp only [hFdef]; rw [run_mix_inv π hL hL1 ω y m]
        simp only [hrw]
        have hcomp := (mp_window μ L₀ m).lintegral_comp
          (f := fun z : Fin (L₀ + 1) → ℝ => ENNReal.ofReal (G κ (X - ∑ i, z i)))
          (ENNReal.measurable_ofReal.comp ((continuous_G κ).measurable.comp
            (measurable_const.sub (by fun_prop))))
        simp only at hcomp
        rw [hcomp]
        rw [← ofReal_integral_eq_lintegral_ofReal (integrable_G_sum μ κ L₀ X)
          (Eventually.of_forall fun _ => G_nonneg _ _)]
        exact ENNReal.ofReal_le_ofReal (gConst_le μ κ L₀ X)
    _ = ∫⁻ ω, F ω ∂sampleLaw μ := (lintegral_mix μ m (L₀ + 1) hF).symm
    _ ≤ _ := lintegral_mono fun ω => by
        simp only [hFdef, periodCost]; exact le_add_self

lemma tendsto_frac (a : ℝ≥0∞) (ha : a ≠ ⊤) (L₀ : ℕ) :
    Tendsto (fun T : ℕ => ((T - L₀ : ℕ) : ℝ≥0∞) * a / T) atTop (𝓝 a) := by
  have e : ∀ᶠ T : ℕ in atTop,
      ENNReal.ofReal ((1 - (L₀ : ℝ) / T) * a.toReal) = ((T - L₀ : ℕ) : ℝ≥0∞) * a / T := by
    filter_upwards [eventually_ge_atTop (L₀ + 1)] with T hT
    have hT0 : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
    rw [← ENNReal.ofReal_toReal ha, ← ENNReal.ofReal_natCast (T - L₀),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast T,
      ← ENNReal.ofReal_div_of_pos hT0, ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    congr 1
    rw [Nat.cast_sub (by omega)]
    field_simp
  refine Tendsto.congr' e ?_
  have : Tendsto (fun T : ℕ => (1 - (L₀ : ℝ) / T) * a.toReal) atTop (𝓝 ((1 - 0) * a.toReal)) :=
    (tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (L₀ : ℝ))).mul
      tendsto_const_nhds
  rw [sub_zero, one_mul] at this
  have h2 := ENNReal.tendsto_ofReal this
  rwa [ENNReal.ofReal_toReal ha] at h2

lemma policy_lower (μ : DemandLaw) (κ : Costs) {L₀ L : ℕ} (π : AdmissiblePolicy L₀ L)
    (hL : L₀ ≤ L) (hL1 : 1 ≤ L) :
    ENNReal.ofReal (gConst μ κ L₀) ≤ policyCost μ κ π := by
  unfold policyCost
  refine le_trans (le_of_eq
    (tendsto_frac (ENNReal.ofReal (gConst μ κ L₀)) ENNReal.ofReal_ne_top L₀).limsup_eq.symm) ?_
  refine Filter.limsup_le_limsup (Eventually.of_forall fun T => ?_)
  refine ENNReal.div_le_div_right ?_ _
  calc ((T - L₀ : ℕ) : ℝ≥0∞) * ENNReal.ofReal (gConst μ κ L₀)
      = ∑ _t ∈ Finset.Icc (L₀ + 1) T, ENNReal.ofReal (gConst μ κ L₀) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, show T + 1 - (L₀ + 1) = T - L₀ by omega]
    _ ≤ _ := Finset.sum_le_sum fun t ht =>
        period_lower μ κ π hL hL1 t (Finset.mem_Icc.1 ht).1

/-! ## The policy `π_{0,0}` -/

/-- Expedited position of a state whose regular pipeline is empty. -/
def EP (L₀ t : ℕ) (s : State) : ℝ := s.2.2 + ∑ i : Fin L₀, s.2.1 ((t : ℤ) - L₀ + ((i : ℕ) : ℤ))

lemma ep_eq (L₀ L t : ℕ) (s : State) (hs : s.1 = 0) :
    expeditedPosition (observe L₀ L t s) = EP L₀ t s := by
  simp [expeditedPosition, observe, EP, hs]

lemma shift_sum (f : ℤ → ℝ) (a : ℤ) (n : ℕ) :
    f a + ∑ i : Fin n, f (a + 1 + ((i : ℕ) : ℤ)) =
      ∑ i : Fin n, f (a + ((i : ℕ) : ℤ)) + f (a + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [← add_assoc, ih]
    have e : a + 1 + (n : ℤ) = a + ((n + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e]

lemma ep_step (L₀ L t : ℕ) (s : State) (hs : s.1 = 0) (e : ℝ≥0) (d : ℝ) :
    (step L₀ L t (0, e) d s).1 = 0 ∧
      EP L₀ (t + 1) (step L₀ L t (0, e) d s) = EP L₀ t s + e - d := by
  have h0 : ∀ j, Function.update s.1 (t : ℤ) ((0 : ℝ≥0) : ℝ) j = 0 := by
    intro j; simp [hs, Function.update_apply]
  constructor
  · ext j; exact h0 j
  · simp only [EP, step]
    rw [h0]
    set f := Function.update s.2.1 (t : ℤ) (e : ℝ) with hf
    have hsh := shift_sum f ((t : ℤ) - L₀) L₀
    have hidx : ∀ i : Fin L₀, ((t + 1 : ℕ) : ℤ) - L₀ + ((i : ℕ) : ℤ) =
        (t : ℤ) - L₀ + 1 + ((i : ℕ) : ℤ) := by intro i; push_cast; ring
    simp only [hidx]
    have hlast : f ((t : ℤ) - L₀ + L₀) = e := by simp [hf]
    have hlow : ∀ i : Fin L₀, f ((t : ℤ) - L₀ + ((i : ℕ) : ℤ)) =
        s.2.1 ((t : ℤ) - L₀ + ((i : ℕ) : ℤ)) := by
      intro i; rw [hf, Function.update_of_ne]; have := i.isLt; omega
    rw [hlast] at hsh
    simp only [hlow] at hsh
    linarith

lemma tbs_f (L₀ L t : ℕ) (s : State) (hs : s.1 = 0) :
    (tbsPolicy L₀ L 0 0).f t (observe L₀ L t s) = (0, (-EP L₀ t s).toNNReal) := by
  show ((0 : ℝ).toNNReal, (0 - expeditedPosition (observe L₀ L t s)).toNNReal) = _
  rw [ep_eq L₀ L t s hs, Real.toNNReal_zero, zero_sub]

/-- The order quantity `q^E_{n+1}` of `π_{0,0}` (a.s.). -/
def v (ω : Sample) (n : ℕ) : ℝ :=
  if n = 0 then ∑ i ∈ Finset.range ω.2.2, ω.2.1 i else ω.1 (n - 1)

lemma v_nonneg (ω : Sample) (hD : ∀ n, 0 ≤ ω.1 n)
    (hS : 0 ≤ ∑ i ∈ Finset.range ω.2.2, ω.2.1 i) (n : ℕ) : 0 ≤ v ω n := by
  unfold v; split_ifs
  · exact hS
  · exact hD _

lemma sim (L₀ L : ℕ) (ω : Sample) (hD : ∀ n, 0 ≤ ω.1 n)
    (hS : 0 ≤ ∑ i ∈ Finset.range ω.2.2, ω.2.1 i) (n : ℕ) :
    (run (tbsPolicy L₀ L 0 0) ω n).1 = 0 ∧
      EP L₀ (n + 1) (run (tbsPolicy L₀ L 0 0) ω n) = - v ω n ∧
      run (tbsPolicy L₀ L 0 0) ω (n + 1) =
        step L₀ L (n + 1) (0, (v ω n).toNNReal) (ω.1 n) (run (tbsPolicy L₀ L 0 0) ω n) := by
  induction n with
  | zero =>
    have h1 : (run (tbsPolicy L₀ L 0 0) ω 0).1 = 0 := rfl
    have h2 : EP L₀ (0 + 1) (run (tbsPolicy L₀ L 0 0) ω 0) = - v ω 0 := by
      simp [run, initState, EP, v]
    refine ⟨h1, h2, ?_⟩
    simp only [run]
    simp only [run] at h1 h2
    rw [show (tbsPolicy L₀ L 0 0).f (0 + 1) (observe L₀ L (0 + 1) (initState ω)) =
      (0, (v ω 0).toNNReal) by simp only [tbsPolicy, ep_eq L₀ L _ _ h1, h2, Real.toNNReal_zero,
        zero_sub, neg_neg]]
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    obtain ⟨h4, h5⟩ := ep_step L₀ L (n + 1) _ h1 (v ω n).toNNReal (ω.1 n)
    have hv := v_nonneg ω hD hS n
    have hvs : v ω (n + 1) = ω.1 n := by simp [v]
    have g1 : (run (tbsPolicy L₀ L 0 0) ω (n + 1)).1 = 0 := by rw [h3]; exact h4
    have g2 : EP L₀ (n + 1 + 1) (run (tbsPolicy L₀ L 0 0) ω (n + 1)) = - v ω (n + 1) := by
      rw [h3, h5, h2, Real.coe_toNNReal _ hv, hvs]; ring
    refine ⟨g1, g2, ?_⟩
    conv_lhs => rw [run]
    rw [tbs_f L₀ L _ _ g1, g2, neg_neg]

lemma hist_stable {L₀ L : ℕ} (π : AdmissiblePolicy L₀ L) (ω : Sample) (i : ℤ) (n : ℕ)
    (hi : i ≤ n) (k : ℕ) : (run π ω (n + k)).2.1 i = (run π ω n).2.1 i := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← ih]
    have hne : i ≠ ((n + k + 1 : ℕ) : ℤ) := by omega
    show (run π ω (n + k + 1)).2.1 i = _
    simp only [run, step, Function.update_apply, hne, if_false]

lemma hist_val (L₀ L : ℕ) (ω : Sample) (hD : ∀ n, 0 ≤ ω.1 n)
    (hS : 0 ≤ ∑ i ∈ Finset.range ω.2.2, ω.2.1 i) (j n : ℕ) (h : j + 1 ≤ n) :
    (run (tbsPolicy L₀ L 0 0) ω n).2.1 ((j + 1 : ℕ) : ℤ) = v ω j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [hist_stable _ ω _ (j + 1) le_rfl k, (sim L₀ L ω hD hS j).2.2]
  simp [step, Real.coe_toNNReal _ (v_nonneg ω hD hS j)]

lemma cost_formula (κ : Costs) (L₀ L : ℕ) (ω : Sample) (hD : ∀ n, 0 ≤ ω.1 n)
    (hS : 0 ≤ ∑ i ∈ Finset.range ω.2.2, ω.2.1 i) (m : ℕ) :
    periodCost κ (tbsPolicy L₀ L 0 0) ω (m + L₀ + 1) =
      ENNReal.ofReal (κ.c * v ω m) +
        ENNReal.ofReal (G κ (-∑ j : Fin (L₀ + 1), ω.1 (m + j))) := by
  unfold periodCost
  have hi1 : ((m + L₀ + 1 : ℕ) : ℤ) - L₀ = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [hi1, hist_val L₀ L ω hD hS m _ (by omega)]
  congr 3
  obtain ⟨-, h2, -⟩ := sim L₀ L ω hD hS (m + L₀ + 1)
  simp only [EP] at h2
  have hidx : ∀ i : Fin L₀, ((m + L₀ + 1 + 1 : ℕ) : ℤ) - L₀ + ((i : ℕ) : ℤ) =
      ((m + 1 + i + 1 : ℕ) : ℤ) := by intro i; push_cast; ring
  simp only [hidx] at h2
  rw [Finset.sum_congr rfl (fun (i : Fin L₀) _ => hist_val L₀ L ω hD hS (m + 1 + i) (m + L₀ + 1)
    (by have := i.isLt; omega))] at h2
  have hv1 : ∀ i : Fin L₀, v ω (m + 1 + i) = ω.1 (m + i) := by
    intro i
    have h : m + 1 + (i : ℕ) ≠ 0 := by omega
    rw [v, if_neg h, show m + 1 + (i : ℕ) - 1 = m + i by omega]
  have hv2 : v ω (m + L₀ + 1) = ω.1 (m + L₀) := by simp [v]
  simp only [hv1, hv2] at h2
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.coe_castSucc, Fin.val_last]
  linarith

lemma mp_fst (μ : DemandLaw) : MeasurePreserving Prod.fst (sampleLaw μ) (pathLaw μ) :=
  ⟨measurable_fst, by unfold sampleLaw; rw [Measure.map_fst_prod, measure_univ, one_smul]⟩

lemma mp_snd (μ : DemandLaw) :
    MeasurePreserving Prod.snd (sampleLaw μ) ((pathLaw μ).prod ghatLaw) :=
  ⟨measurable_snd, by unfold sampleLaw; rw [Measure.map_snd_prod, measure_univ, one_smul]⟩

lemma mp_fst' (μ : DemandLaw) :
    MeasurePreserving Prod.fst ((pathLaw μ).prod ghatLaw) (pathLaw μ) :=
  ⟨measurable_fst, by rw [Measure.map_fst_prod, measure_univ, one_smul]⟩

lemma mp_eval (μ : DemandLaw) (n : ℕ) :
    MeasurePreserving (fun p : Path => p n) (pathLaw μ) μ.law := by
  unfold pathLaw; exact measurePreserving_eval_infinitePi _ n

lemma ae_good (μ : DemandLaw) :
    ∀ᵐ ω ∂sampleLaw μ, (∀ n, 0 ≤ ω.1 n) ∧ (∀ n, 0 ≤ ω.2.1 n) := by
  refine (ae_all_iff.2 fun n => ?_).and (ae_all_iff.2 fun n => ?_)
  · have hmp := (mp_eval μ n).comp (mp_fst μ)
    exact ae_of_ae_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact ae_nonneg μ)
  · have hmp := ((mp_eval μ n).comp (mp_fst' μ)).comp (mp_snd μ)
    exact ae_of_ae_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact ae_nonneg μ)

lemma E_win (μ : DemandLaw) (κ : Costs) (L₀ m : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (G κ (-∑ j : Fin (L₀ + 1), ω.1 (m + j))) ∂sampleLaw μ =
      ENNReal.ofReal (∫ y, G κ (-∑ i, y i) ∂sumLaw μ L₀) := by
  have hmp := (mp_window μ L₀ m).comp (mp_fst μ)
  have hc := hmp.lintegral_comp
    (f := fun z : Fin (L₀ + 1) → ℝ => ENNReal.ofReal (G κ (-∑ i, z i)))
    (ENNReal.measurable_ofReal.comp ((continuous_G κ).measurable.comp (by fun_prop)))
  simp only [Function.comp] at hc
  rw [hc]
  have hi : Integrable (fun y : Fin (L₀ + 1) → ℝ => G κ (-∑ i, y i)) (sumLaw μ L₀) := by
    simpa using integrable_G_sum μ κ L₀ 0
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => G_nonneg _ _)]

lemma mean_nonneg (μ : DemandLaw) : 0 ≤ μ.mean :=
  integral_nonneg_of_ae (ae_nonneg μ)

lemma E_coord (μ : DemandLaw) (κ : Costs) (k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (κ.c * ω.1 k) ∂sampleLaw μ = ENNReal.ofReal (κ.c * μ.mean) := by
  have hmp := (mp_eval μ k).comp (mp_fst μ)
  have hc := hmp.lintegral_comp (f := fun d : ℝ => ENNReal.ofReal (κ.c * d))
    (ENNReal.measurable_ofReal.comp (measurable_const.mul measurable_id))
  simp only [Function.comp] at hc
  have hi : Integrable (fun d : ℝ => κ.c * d) μ.law := μ.integrable.const_mul κ.c
  rw [hc, ← ofReal_integral_eq_lintegral_ofReal hi
    (by filter_upwards [ae_nonneg μ] with d hd; exact mul_nonneg κ.c_pos.le hd)]
  rw [integral_const_mul]
  rfl

lemma real_bound (i : ℕ) : (1 / 2 : ℝ) ^ (i + 1) * ((i : ℝ) + 1) ≤ (3 / 4) ^ i := by
  have h1 : ((i : ℝ) + 1) ≤ 2 * (3 / 2) ^ i := by
    induction i with
    | zero => norm_num
    | succ n ih =>
      have := one_le_pow₀ (show (1 : ℝ) ≤ 3 / 2 by norm_num) (n := n)
      push_cast; rw [pow_succ]; nlinarith
  calc (1 / 2 : ℝ) ^ (i + 1) * ((i : ℝ) + 1) ≤ (1 / 2) ^ (i + 1) * (2 * (3 / 2) ^ i) := by
        gcongr
    _ = (3 / 4) ^ i := by
        rw [pow_succ, show (3 / 4 : ℝ) = (1 / 2) * (3 / 2) by norm_num, mul_pow]; ring

lemma ghat_mean_ne_top : ∫⁻ k, (k : ℝ≥0∞) ∂ghatLaw ≠ ⊤ := by
  unfold ghatLaw
  rw [lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac]
  refine ne_top_of_le_ne_top (ENNReal.tsum_coe_ne_top_iff_summable.2
    (NNReal.summable_geometric (r := 3 / 4) (by norm_num))) (ENNReal.tsum_le_tsum fun i => ?_)
  rw [ENNReal.smul_def, smul_eq_mul, ← ENNReal.coe_natCast, ← ENNReal.coe_mul,
    ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
  push_cast
  exact real_bound i

lemma E0_fin (μ : DemandLaw) (κ : Costs) :
    ∫⁻ ω, ENNReal.ofReal (κ.c * ∑ i ∈ Finset.range ω.2.2, ω.2.1 i) ∂sampleLaw μ ≠ ⊤ := by
  have hq : Measurable (fun q : Path × ℕ => ENNReal.ofReal (κ.c * ∑ i ∈ Finset.range q.2, q.1 i)) := by
    refine measurable_from_prod_countable_left fun k => ?_
    simp only
    exact ENNReal.measurable_ofReal.comp
      (measurable_const.mul (Finset.measurable_sum _ fun i _ => measurable_pi_apply i))
  have hc := (mp_snd μ).lintegral_comp hq
  rw [hc, lintegral_prod_symm _ hq.aemeasurable]
  set B := ∫⁻ d, ENNReal.ofReal (κ.c * |d|) ∂μ.law with hBdef
  have hB : B ≠ ⊤ := (Integrable.lintegral_lt_top (μ.integrable.abs.const_mul κ.c)).ne
  have inner : ∀ k : ℕ, ∫⁻ x, ENNReal.ofReal (κ.c * ∑ i ∈ Finset.range k, x i) ∂pathLaw μ ≤
      (k : ℝ≥0∞) * B := by
    intro k
    have hmi : ∀ i, Measurable (fun x : Path => ENNReal.ofReal (κ.c * |x i|)) := fun i =>
      ENNReal.measurable_ofReal.comp (measurable_const.mul
        (continuous_abs.measurable.comp (measurable_pi_apply i)))
    calc _ ≤ ∫⁻ x, ∑ i ∈ Finset.range k, ENNReal.ofReal (κ.c * |x i|) ∂pathLaw μ :=
          lintegral_mono fun x => by
            rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by have := κ.c_pos; positivity)]
            apply ENNReal.ofReal_le_ofReal
            rw [Finset.mul_sum]
            exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (le_abs_self _) κ.c_pos.le
      _ = ∑ i ∈ Finset.range k, ∫⁻ x, ENNReal.ofReal (κ.c * |x i|) ∂pathLaw μ :=
          lintegral_finset_sum _ (fun i _ => hmi i)
      _ = ∑ _i ∈ Finset.range k, B := Finset.sum_congr rfl fun i _ =>
          (mp_eval μ i).lintegral_comp (f := fun d : ℝ => ENNReal.ofReal (κ.c * |d|))
            (ENNReal.measurable_ofReal.comp (measurable_const.mul continuous_abs.measurable))
      _ = (k : ℝ≥0∞) * B := by simp
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top ghat_mean_ne_top hB)
    (le_trans (lintegral_mono inner) (le_of_eq (lintegral_mul_const B (Measurable.of_discrete))))

lemma tendsto_frac2 (A a : ℝ≥0∞) (hA : A ≠ ⊤) (ha : a ≠ ⊤) (L₀ : ℕ) :
    Tendsto (fun T : ℕ => (A + ((T - L₀ - 1 : ℕ) : ℝ≥0∞) * a) / T) atTop (𝓝 a) := by
  have e : ∀ᶠ T : ℕ in atTop,
      ENNReal.ofReal (a.toReal + (A.toReal - ((L₀ : ℝ) + 1) * a.toReal) / T) =
        (A + ((T - L₀ - 1 : ℕ) : ℝ≥0∞) * a) / T := by
    filter_upwards [eventually_ge_atTop (L₀ + 1)] with T hT
    have hT0 : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
    rw [← ENNReal.ofReal_toReal ha, ← ENNReal.ofReal_toReal hA,
      ← ENNReal.ofReal_natCast (T - L₀ - 1), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity), ← ENNReal.ofReal_natCast T,
      ← ENNReal.ofReal_div_of_pos hT0, ENNReal.toReal_ofReal ENNReal.toReal_nonneg,
      ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    congr 1
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    field_simp
    push_cast
    ring
  refine Tendsto.congr' e ?_
  have : Tendsto (fun T : ℕ => a.toReal + (A.toReal - ((L₀ : ℝ) + 1) * a.toReal) / T) atTop
      (𝓝 (a.toReal + 0)) :=
    tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat _)
  rw [add_zero] at this
  have h2 := ENNReal.tendsto_ofReal this
  rwa [ENNReal.ofReal_toReal ha] at h2

lemma U_nonneg (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) : 0 ≤ UConst μ κ L₀ :=
  add_nonneg (mul_nonneg κ.c_pos.le (mean_nonneg μ))
    (integral_nonneg fun _ => G_nonneg _ _)

lemma tbs00 (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) :
    tbsCost μ κ L₀ L 0 0 = ENNReal.ofReal (UConst μ κ L₀) := by
  set π₀ := tbsPolicy L₀ L 0 0
  set E : ℕ → ℝ≥0∞ := fun t => ∫⁻ ω, periodCost κ π₀ ω t ∂sampleLaw μ with hEdef
  have hae := ae_good μ
  have hEt : ∀ m, E (m + L₀ + 1) =
      ∫⁻ ω, ENNReal.ofReal (κ.c * v ω m) ∂sampleLaw μ +
        ENNReal.ofReal (∫ y, G κ (-∑ i, y i) ∂sumLaw μ L₀) := by
    intro m
    simp only [hEdef]
    rw [lintegral_congr_ae (by
      filter_upwards [hae] with ω hω
      exact cost_formula κ L₀ L ω hω.1 (Finset.sum_nonneg fun i _ => hω.2 i) m)]
    have hmeas : Measurable (fun ω : Sample =>
        ENNReal.ofReal (G κ (-∑ j : Fin (L₀ + 1), ω.1 (m + j)))) :=
      ENNReal.measurable_ofReal.comp ((continuous_G κ).measurable.comp
        (by fun_prop : Measurable fun ω : Sample => -∑ j : Fin (L₀ + 1), ω.1 (m + j)))
    rw [lintegral_add_right _ hmeas, E_win]
  have hE1 : ∀ m, 1 ≤ m → E (m + L₀ + 1) = ENNReal.ofReal (UConst μ κ L₀) := by
    intro m hm
    rw [hEt]
    have hv : ∀ ω, v ω m = ω.1 (m - 1) := fun ω => by simp only [v]; rw [if_neg (by omega)]
    simp only [hv]
    rw [E_coord, UConst, ENNReal.ofReal_add (mul_nonneg κ.c_pos.le (mean_nonneg μ))
      (integral_nonneg fun _ => G_nonneg _ _)]
  have hE0 : E (L₀ + 1) ≠ ⊤ := by
    have := hEt 0
    rw [zero_add] at this
    rw [this]
    refine ENNReal.add_ne_top.2 ⟨?_, ENNReal.ofReal_ne_top⟩
    simpa [v] using E0_fin μ κ
  have hsum : ∀ T, L₀ + 1 ≤ T → ∑ t ∈ Finset.Icc (L₀ + 1) T, E t =
      E (L₀ + 1) + ((T - L₀ - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (UConst μ κ L₀) := by
    intro T hT
    rw [← Finset.insert_Icc_add_one_left_eq_Icc hT, Finset.sum_insert (by simp)]
    congr 1
    have hc : ∀ t ∈ Finset.Icc (L₀ + 1 + 1) T, E t = ENNReal.ofReal (UConst μ κ L₀) := by
      intro t ht
      rw [Finset.mem_Icc] at ht
      have h := hE1 (t - L₀ - 1) (by omega)
      rwa [show t - L₀ - 1 + L₀ + 1 = t by omega] at h
    rw [Finset.sum_congr rfl hc]
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, show T + 1 - (L₀ + 1 + 1) = T - L₀ - 1 by omega]
  show policyCost μ κ π₀ = _
  unfold policyCost
  rw [Filter.limsup_congr (f := atTop) (v := fun T : ℕ =>
    (E (L₀ + 1) + ((T - L₀ - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (UConst μ κ L₀)) / T) (by
      filter_upwards [eventually_ge_atTop (L₀ + 1)] with T hT
      rw [← hsum T hT])]
  exact (tendsto_frac2 _ _ hE0 ENNReal.ofReal_ne_top L₀).limsup_eq

end XGOB

namespace XGSW

open XinGoldbergTBS.Asymptotic

/-! ## P1: pathwise dynamics of an arbitrary policy -/

lemma measurable_initState : Measurable (fun ω : Sample => initState ω) := by
  unfold initState
  refine measurable_const.prodMk (measurable_const.prodMk ?_)
  have : Measurable (fun q : Path × ℕ => -∑ i ∈ Finset.range q.2, q.1 i) := by
    refine measurable_from_prod_countable_left fun k => ?_
    simp only
    exact (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).neg
  exact this.comp measurable_snd

lemma measurable_step (L₀ L t : ℕ) :
    Measurable (fun q : (ℝ≥0 × ℝ≥0) × ℝ × State => step L₀ L t q.1 q.2.1 q.2.2) := by
  unfold step; fun_prop

lemma measurable_observe (L₀ L t : ℕ) : Measurable (observe L₀ L t) := by
  unfold observe; fun_prop

lemma measurable_run {L₀ L : ℕ} (π : AdmissiblePolicy L₀ L) (n : ℕ) :
    Measurable (fun ω : Sample => run π ω n) := by
  induction n with
  | zero => exact measurable_initState
  | succ n ih =>
    have h1 : Measurable (fun ω : Sample => π.f (n + 1) (observe L₀ L (n + 1) (run π ω n))) :=
      (π.measurable_f _).comp ((measurable_observe _ _ _).comp ih)
    have h2 : Measurable (fun ω : Sample => ω.1 n) := (measurable_pi_apply n).comp measurable_fst
    exact (measurable_step L₀ L (n + 1)).comp (h1.prodMk (h2.prodMk ih))

lemma run_local {L₀ L : ℕ} (π : AdmissiblePolicy L₀ L) (ω ω' : Sample) (h2 : ω.2 = ω'.2)
    (m : ℕ) (h1 : ∀ n < m, ω.1 n = ω'.1 n) : ∀ j ≤ m, run π ω j = run π ω' j := by
  intro j hj
  induction j with
  | zero => simp only [run, initState, h2]
  | succ j ih => simp only [run]; rw [ih (by omega), h1 j (by omega)]

variable {L₀ L : ℕ}

/-- Observation in period `n + 1`. -/
def obsN (π : AdmissiblePolicy L₀ L) (ω : Sample) (n : ℕ) : Obs L₀ L :=
  observe L₀ L (n + 1) (run π ω n)

/-- Orders placed in period `n + 1`. -/
def act (π : AdmissiblePolicy L₀ L) (ω : Sample) (n : ℕ) : ℝ≥0 × ℝ≥0 :=
  π.f (n + 1) (obsN π ω n)

def chiV (π : AdmissiblePolicy L₀ L) (ω : Sample) (n : ℕ) : Fin (L - L₀ - 1) → ℝ :=
  truncPipeline (obsN π ω n)

def qV (π : AdmissiblePolicy L₀ L) (ω : Sample) (n : ℕ) : Fin (L - L₀) → ℝ :=
  fun k => ((act π ω (n + k)).2 : ℝ)

def IV (π : AdmissiblePolicy L₀ L) (ω : Sample) (n : ℕ) : ℝ :=
  expeditedPosition (obsN π ω n)

def chiF (π : AdmissiblePolicy L₀ L) (ω : Sample) (n j : ℕ) : ℝ :=
  if h : j < L - L₀ - 1 then chiV π ω n ⟨j, h⟩ else 0

def Zs (π : AdmissiblePolicy L₀ L) (ω : Sample) (n : ℕ) : ℝ :=
  IV π ω n + ((act π ω n).2 : ℝ) - ∑ i ∈ Finset.range (L₀ + 1), ω.1 (n + i)

lemma run_succ (π : AdmissiblePolicy L₀ L) (ω : Sample) (n : ℕ) :
    run π ω (n + 1) = step L₀ L (n + 1) (act π ω n) (ω.1 n) (run π ω n) := rfl

lemma hist1 (π : AdmissiblePolicy L₀ L) (ω : Sample) (p : ℕ) (i : ℤ) (hi : i ≤ p) :
    (run π ω (p + 1)).1 i = (run π ω p).1 i ∧ (run π ω (p + 1)).2.1 i = (run π ω p).2.1 i := by
  have hne : i ≠ ((p + 1 : ℕ) : ℤ) := by omega
  rw [run_succ]
  simp only [step, Function.update_apply, hne, if_false, and_self]

lemma hist (π : AdmissiblePolicy L₀ L) (ω : Sample) (p : ℕ) (i : ℤ) (hi : i ≤ p) (k : ℕ) :
    (run π ω (p + k)).1 i = (run π ω p).1 i ∧ (run π ω (p + k)).2.1 i = (run π ω p).2.1 i := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    have h := hist1 π ω (p + k) i (by omega)
    rw [← add_assoc, h.1, h.2]
    exact ih

lemma hist_new (π : AdmissiblePolicy L₀ L) (ω : Sample) (n : ℕ) :
    (run π ω (n + 1)).1 ((n + 1 : ℕ) : ℤ) = (act π ω n).1 ∧
      (run π ω (n + 1)).2.1 ((n + 1 : ℕ) : ℤ) = (act π ω n).2 := by
  rw [run_succ]
  simp only [step, Function.update_self, and_self]

lemma filter_sum (hL : L₀ < L) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin L => i.val ≤ L₀), f i.val =
      ∑ i ∈ Finset.range (L₀ + 1), f i := by
  rw [Finset.sum_filter, Fin.sum_univ_eq_sum_range (fun i => if i ≤ L₀ then f i else 0),
    ← Finset.sum_filter]
  congr 1
  ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega

lemma epos_eq (t : ℕ) (hL : L₀ < L) (s : State) :
    expeditedPosition (observe L₀ L t s) =
      s.2.2 + ∑ i ∈ Finset.range L₀, s.2.1 ((t : ℤ) - L₀ + (i : ℤ)) +
      ∑ i ∈ Finset.range (L₀ + 1), s.1 ((t : ℤ) - L + (i : ℤ)) := by
  unfold expeditedPosition observe
  simp only
  rw [Fin.sum_univ_eq_sum_range (fun i => s.2.1 ((t : ℤ) - L₀ + (i : ℤ))),
    filter_sum hL (fun i => s.1 ((t : ℤ) - L + (i : ℤ)))]

lemma epos_step (t : ℕ) (hL : L₀ + 1 < L) (a : ℝ≥0 × ℝ≥0) (d : ℝ) (s : State) :
    expeditedPosition (observe L₀ L (t + 1) (step L₀ L t a d s)) =
      expeditedPosition (observe L₀ L t s) + a.2 - d + s.1 ((t : ℤ) - L + L₀ + 1) := by
  rw [epos_eq (t + 1) (by omega), epos_eq t (by omega)]
  simp only [step]
  set qR := Function.update s.1 (t : ℤ) (a.1 : ℝ) with hqR
  set qE := Function.update s.2.1 (t : ℤ) (a.2 : ℝ) with hqE
  have hE : qE ((t : ℤ) - L₀) + ∑ i ∈ Finset.range L₀, qE (((t + 1 : ℕ) : ℤ) - L₀ + (i : ℤ)) =
      ∑ i ∈ Finset.range L₀, s.2.1 ((t : ℤ) - L₀ + (i : ℤ)) + a.2 := by
    have h1 : qE ((t : ℤ) - L₀) + ∑ i ∈ Finset.range L₀, qE (((t + 1 : ℕ) : ℤ) - L₀ + (i : ℤ)) =
        ∑ i ∈ Finset.range (L₀ + 1), qE ((t : ℤ) - L₀ + (i : ℤ)) := by
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1; ring
    rw [h1, Finset.sum_range_succ]
    have h2 : qE ((t : ℤ) - L₀ + (L₀ : ℤ)) = a.2 := by simp [hqE]
    rw [h2]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have := Finset.mem_range.1 hi
    rw [hqE, Function.update_of_ne]; omega
  have hR : qR ((t : ℤ) - L) + ∑ i ∈ Finset.range (L₀ + 1), qR (((t + 1 : ℕ) : ℤ) - L + (i : ℤ)) =
      ∑ i ∈ Finset.range (L₀ + 1), s.1 ((t : ℤ) - L + (i : ℤ)) + s.1 ((t : ℤ) - L + L₀ + 1) := by
    have h1 : qR ((t : ℤ) - L) + ∑ i ∈ Finset.range (L₀ + 1), qR (((t + 1 : ℕ) : ℤ) - L + (i : ℤ)) =
        ∑ i ∈ Finset.range (L₀ + 1 + 1), qR ((t : ℤ) - L + (i : ℤ)) := by
      rw [Finset.sum_range_succ' _ (L₀ + 1)]
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1; ring
    rw [h1, Finset.sum_range_succ]
    have h3 : ∀ i ∈ Finset.range (L₀ + 1 + 1), qR ((t : ℤ) - L + (i : ℤ)) = s.1 ((t : ℤ) - L + (i : ℤ)) := by
      intro i hi
      have := Finset.mem_range.1 hi
      rw [hqR, Function.update_of_ne]; omega
    rw [Finset.sum_congr rfl (fun i hi => h3 i (Finset.mem_range.2 (by
      have := Finset.mem_range.1 hi; omega))), h3 (L₀ + 1) (by simp)]
    congr 2; push_cast; ring
  linarith

lemma chiV_apply (π : AdmissiblePolicy L₀ L) (ω : Sample) (n : ℕ) (j : Fin (L - L₀ - 1)) :
    chiV π ω n j = (run π ω n).1 (((n + 1 : ℕ) : ℤ) - L + ((L₀ + 1 + j.val : ℕ) : ℤ)) := rfl

lemma chi_shift (π : AdmissiblePolicy L₀ L) (ω : Sample) (n : ℕ) (j : ℕ)
    (hj : j < L - L₀ - 1) :
    chiF π ω (n + j) 0 = chiF π ω n j := by
  have h0 : 0 < L - L₀ - 1 := by omega
  simp only [chiF, dif_pos h0, dif_pos hj, chiV_apply]
  have := (hist π ω n (((n + 1 : ℕ) : ℤ) - L + ((L₀ + 1 + j : ℕ) : ℤ)) (by push_cast; omega) j).1
  rw [← this]
  congr 1
  push_cast; ring

lemma iv_succ (hL : L₀ + 1 < L) (π : AdmissiblePolicy L₀ L) (ω : Sample) (n : ℕ) :
    IV π ω (n + 1) = IV π ω n + ((act π ω n).2 : ℝ) + chiF π ω n 0 - ω.1 n := by
  have h0 : 0 < L - L₀ - 1 := by omega
  simp only [IV, obsN]
  rw [run_succ, epos_step (n + 1) hL]
  simp only [chiF, dif_pos h0, chiV_apply]
  have : ((n + 1 : ℕ) : ℤ) - L + ((L₀ + 1 + 0 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) - L + L₀ + 1 := by
    push_cast; ring
  rw [this]
  ring

lemma iv_add (hL : L₀ + 1 < L) (π : AdmissiblePolicy L₀ L) (ω : Sample) (n : ℕ) :
    ∀ k ≤ L - L₀ - 1, IV π ω (n + k) = IV π ω n +
      ∑ i ∈ Finset.range k, (((act π ω (n + i)).2 : ℝ) + chiF π ω n i - ω.1 (n + i)) := by
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, iv_succ hL, ih (by omega), Finset.sum_range_succ,
      chi_shift π ω n k (by omega)]
    ring

/-- Inventory after `j` more periods. -/
lemma inv_formula (π : AdmissiblePolicy L₀ L) (ω : Sample) (m : ℕ) : ∀ j : ℕ,
    (run π ω (m + j)).2.2 = (run π ω m).2.2 +
      ∑ t ∈ Finset.range j, ((run π ω (m + j)).1 (((m + 1 + t : ℕ) : ℤ) - L) +
        (run π ω (m + j)).2.1 (((m + 1 + t : ℕ) : ℤ) - L₀)) -
      ∑ t ∈ Finset.range j, ω.1 (m + t) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have hs : (run π ω (m + (j + 1))).2.2 = (run π ω (m + j)).2.2 +
        (run π ω (m + j + 1)).1 (((m + j + 1 : ℕ) : ℤ) - L) +
        (run π ω (m + j + 1)).2.1 (((m + j + 1 : ℕ) : ℤ) - L₀) - ω.1 (m + j) := by
      rw [← add_assoc, run_succ]; rfl
    rw [hs, ih, Finset.sum_range_succ, Finset.sum_range_succ]
    have hc : ∀ t ∈ Finset.range j,
        (run π ω (m + j)).1 (((m + 1 + t : ℕ) : ℤ) - L) +
          (run π ω (m + j)).2.1 (((m + 1 + t : ℕ) : ℤ) - L₀) =
        (run π ω (m + (j + 1))).1 (((m + 1 + t : ℕ) : ℤ) - L) +
          (run π ω (m + (j + 1))).2.1 (((m + 1 + t : ℕ) : ℤ) - L₀) := by
      intro t ht
      have := Finset.mem_range.1 ht
      rw [← add_assoc, (hist1 π ω (m + j) _ (by push_cast; omega)).1,
        (hist1 π ω (m + j) _ (by push_cast; omega)).2]
    rw [Finset.sum_congr rfl hc]
    have : m + 1 + j = m + j + 1 := by ring
    rw [this, ← add_assoc]
    ring

lemma z_eq (hL : L₀ + 1 < L) (π : AdmissiblePolicy L₀ L) (ω : Sample) (n : ℕ) :
    (run π ω (n + (L₀ + 1))).2.2 = Zs π ω n ∧
      (run π ω (n + (L₀ + 1))).2.1 ((n + 1 : ℕ) : ℤ) = (act π ω n).2 := by
  have hq : (run π ω (n + (L₀ + 1))).2.1 ((n + 1 : ℕ) : ℤ) = (act π ω n).2 := by
    rw [show n + (L₀ + 1) = (n + 1) + L₀ by ring, (hist π ω (n + 1) _ le_rfl L₀).2]
    exact (hist_new π ω n).2
  refine ⟨?_, hq⟩
  rw [inv_formula π ω n (L₀ + 1)]
  simp only [Zs, IV, obsN]
  rw [epos_eq (n + 1) (by omega), Finset.sum_add_distrib, Finset.sum_range_succ
    (fun t => (run π ω (n + (L₀ + 1))).2.1 (((n + 1 + t : ℕ) : ℤ) - L₀))]
  have hR : ∀ t ∈ Finset.range (L₀ + 1), (run π ω (n + (L₀ + 1))).1 (((n + 1 + t : ℕ) : ℤ) - L) =
      (run π ω n).1 (((n + 1 : ℕ) : ℤ) - L + (t : ℤ)) := by
    intro t ht
    have := Finset.mem_range.1 ht
    rw [(hist π ω n _ (by push_cast; omega) (L₀ + 1)).1]
    congr 1; push_cast; ring
  have hE : ∀ t ∈ Finset.range L₀, (run π ω (n + (L₀ + 1))).2.1 (((n + 1 + t : ℕ) : ℤ) - L₀) =
      (run π ω n).2.1 (((n + 1 : ℕ) : ℤ) - L₀ + (t : ℤ)) := by
    intro t ht
    have := Finset.mem_range.1 ht
    rw [(hist π ω n _ (by push_cast; omega) (L₀ + 1)).2]
    congr 1; push_cast; ring
  rw [Finset.sum_congr rfl hR, Finset.sum_congr rfl hE]
  have hlast : (run π ω (n + (L₀ + 1))).2.1 (((n + 1 + L₀ : ℕ) : ℤ) - L₀) = (act π ω n).2 := by
    rw [← hq]; congr 1; push_cast; ring
  rw [hlast]
  ring

lemma periodCost_eq (hL : L₀ + 1 < L) (κ : Costs) (π : AdmissiblePolicy L₀ L) (ω : Sample)
    (n : ℕ) :
    periodCost κ π ω (n + (L₀ + 1)) =
      ENNReal.ofReal (κ.c * ((act π ω n).2 : ℝ)) + ENNReal.ofReal (G κ (Zs π ω n)) := by
  obtain ⟨h1, h2⟩ := z_eq hL π ω n
  unfold periodCost
  rw [h1, ← h2]
  congr 3
  push_cast; ring

/-- Pathwise stationarity: the k-th window functional at time `n` is the 0-th at `n + k`. -/
lemma stat_path (hL : L₀ + 1 < L) (π : AdmissiblePolicy L₀ L) (ω : Sample) (n k : ℕ)
    (hk : k < L - L₀) :
    IV π ω n + ∑ i ∈ Finset.range k, (((act π ω (n + i)).2 : ℝ) + chiF π ω n i - ω.1 (n + i))
      + ((act π ω (n + k)).2 : ℝ) - ∑ i ∈ Finset.range (L₀ + 1), ω.1 (n + (k + i)) =
    Zs π ω (n + k) := by
  rw [Zs, iv_add hL π ω n k (by omega)]
  simp only [add_assoc]

lemma chiF_nonneg (π : AdmissiblePolicy L₀ L) (ω : Sample) : ∀ n j, 0 ≤ chiF π ω n j := by
  have key : ∀ n (i : ℤ), 0 ≤ (run π ω n).1 i := by
    intro n
    induction n with
    | zero => intro i; simp [run, initState]
    | succ n ih =>
      intro i
      rw [run_succ]
      simp only [step, Function.update_apply]
      split_ifs
      · exact (act π ω n).1.2
      · exact ih i
  intro n j
  unfold chiF
  split_ifs
  · exact key n _
  · exact le_rfl


/-! ## P2: independence of the window from the past -/

instance ghat_isProb : IsProbabilityMeasure ghatLaw := by
  constructor
  unfold ghatLaw
  rw [Measure.sum_apply _ MeasurableSet.univ]
  have h : ∀ i : ℕ, ((2 : ℝ≥0∞) ^ (i + 1))⁻¹ = 2⁻¹ * (2⁻¹) ^ i := by
    intro i; rw [ENNReal.inv_pow, pow_succ, mul_comm]
  calc _ = ∑' i : ℕ, ((2 : ℝ≥0∞) ^ (i + 1))⁻¹ := by simp
    _ = 1 := by
      simp only [h]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
        ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

instance pathLaw_isProb (μ : DemandLaw) : IsProbabilityMeasure (pathLaw μ) := by
  unfold pathLaw; infer_instance

instance sampleLaw_isProb (μ : DemandLaw) : IsProbabilityMeasure (sampleLaw μ) := by
  unfold sampleLaw; infer_instance

def DV (m : ℕ) (ω : Sample) : Path := fun j => ω.1 (m + j)

def tailMix (m : ℕ) (p y : Path) : Path := fun n => if n < m then p n else y (n - m)

lemma measurable_tailMix (m : ℕ) : Measurable (fun q : Path × Path => tailMix m q.1 q.2) := by
  refine measurable_pi_lambda _ fun n => ?_
  by_cases h : n < m
  · simp only [tailMix, h, if_true]; fun_prop
  · simp only [tailMix, h, if_false]; fun_prop

lemma mp_tailMix (μ : DemandLaw) (m : ℕ) :
    MeasurePreserving (fun q : Path × Path => tailMix m q.1 q.2)
      ((pathLaw μ).prod (pathLaw μ)) (pathLaw μ) := by
  refine ⟨measurable_tailMix m, ?_⟩
  conv_rhs => rw [pathLaw]
  apply Measure.eq_infinitePi
  intro s t ht
  classical
  rw [Measure.map_apply (measurable_tailMix m)
    (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
  have hpre : (fun q : Path × Path => tailMix m q.1 q.2) ⁻¹' (Set.pi (↑s) t) =
      (Set.pi ↑(s.filter (fun i => i < m)) t) ×ˢ
        (Set.pi ↑((s.filter (fun i => ¬ i < m)).image (fun i => i - m)) (fun j => t (j + m))) := by
    ext ⟨p, y⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Finset.coe_filter, Set.mem_setOf_eq,
      Finset.mem_coe, tailMix, Finset.coe_image, Set.mem_image, forall_exists_index, and_imp]
    constructor
    · intro h
      refine ⟨fun i hi hw => by simpa [hw] using h i hi, ?_⟩
      intro j i hi hw hj
      subst hj
      have := h i hi
      simp only [hw, if_false] at this
      rwa [Nat.sub_add_cancel (by omega)]
    · rintro ⟨h1, h2⟩ i hi
      by_cases hw : i < m
      · simpa [hw] using h1 i hi hw
      · simp only [hw, if_false]
        have := h2 (i - m) i hi hw rfl
        rwa [Nat.sub_add_cancel (by omega)] at this
  rw [hpre, Measure.prod_prod]
  unfold pathLaw
  rw [Measure.infinitePi_pi _ (fun i _ => ht i), Measure.infinitePi_pi _ (fun i _ => ht (i + m))]
  rw [Finset.prod_image (fun a ha b hb h => by
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
    omega)]
  have h2 : ∏ x ∈ s.filter (fun i => ¬ i < m), μ.law (t (x - m + m)) =
      ∏ x ∈ s.filter (fun i => ¬ i < m), μ.law (t x) := by
    refine Finset.prod_congr rfl (fun i hi => ?_)
    simp only [Finset.mem_filter] at hi
    rw [Nat.sub_add_cancel (by omega)]
  rw [h2]
  exact Finset.prod_filter_mul_prod_filter_not s (fun i => i < m) (fun i => μ.law (t i))

lemma mp_Phi (μ : DemandLaw) (m : ℕ) :
    MeasurePreserving (fun z : Sample × Path => ((tailMix m z.1.1 z.2, z.1.2) : Sample))
      ((sampleLaw μ).prod (pathLaw μ)) (sampleLaw μ) := by
  have h1 := measurePreserving_prodAssoc (pathLaw μ) ((pathLaw μ).prod ghatLaw) (pathLaw μ)
  have h2 : MeasurePreserving (Prod.map (id : Path → Path) (Prod.swap))
      ((pathLaw μ).prod (((pathLaw μ).prod ghatLaw).prod (pathLaw μ)))
      ((pathLaw μ).prod ((pathLaw μ).prod ((pathLaw μ).prod ghatLaw))) :=
    (MeasurePreserving.id _).prod (Measure.measurePreserving_swap)
  have h3 := (measurePreserving_prodAssoc (pathLaw μ) (pathLaw μ) ((pathLaw μ).prod ghatLaw)).symm
  have h4 : MeasurePreserving (Prod.map (fun q : Path × Path => tailMix m q.1 q.2)
      (id : Path × ℕ → Path × ℕ))
      (((pathLaw μ).prod (pathLaw μ)).prod ((pathLaw μ).prod ghatLaw))
      ((pathLaw μ).prod ((pathLaw μ).prod ghatLaw)) :=
    (mp_tailMix μ m).prod (MeasurePreserving.id _)
  have := h4.comp (h3.comp (h2.comp h1))
  unfold sampleLaw
  convert this using 1
  funext z
  rfl

lemma law_split (μ : DemandLaw) {X : Type*} [MeasurableSpace X] (m : ℕ) (F : Sample → X)
    (hF : Measurable F) (hloc : ∀ ω y, F (tailMix m ω.1 y, ω.2) = F ω) :
    (sampleLaw μ).map (fun ω => (F ω, DV m ω)) = ((sampleLaw μ).map F).prod (pathLaw μ) := by
  have hDV : Measurable (DV m) := measurable_pi_lambda _ fun j =>
    (measurable_pi_apply _).comp measurable_fst
  conv_lhs => rw [← (mp_Phi μ m).map_eq]
  rw [Measure.map_map (hF.prodMk hDV) (mp_Phi μ m).measurable]
  have : (fun ω => (F ω, DV m ω)) ∘ (fun z : Sample × Path => ((tailMix m z.1.1 z.2, z.1.2) : Sample))
      = Prod.map F id := by
    funext z
    simp only [Function.comp, Prod.map, id]
    refine Prod.ext (hloc z.1 z.2) ?_
    funext j
    simp [DV, tailMix]
  rw [this, ← Measure.map_prod_map _ _ hF measurable_id, Measure.map_id]

lemma law_DV (μ : DemandLaw) (m : ℕ) : (sampleLaw μ).map (DV m) = pathLaw μ := by
  have h := congrArg (fun ρ : Measure (Unit × Path) => ρ.map Prod.snd)
    (law_split μ m (fun _ => ()) measurable_const (fun _ _ => rfl))
  have hDV : Measurable (DV m) := measurable_pi_lambda _ fun j =>
    (measurable_pi_apply _).comp measurable_fst
  rw [Measure.map_map measurable_snd (measurable_const.prodMk hDV)] at h
  rw [Measure.map_snd_prod] at h
  simpa [Function.comp_def, measure_univ] using h

lemma run_tailMix (π : AdmissiblePolicy L₀ L) (m : ℕ) (ω : Sample) (y : Path) :
    ∀ j ≤ m, run π (tailMix m ω.1 y, ω.2) j = run π ω j := by
  intro j hj
  refine (run_local π ω (tailMix m ω.1 y, ω.2) rfl m (fun n hn => ?_) j hj).symm
  simp [tailMix, hn]


lemma measurable_obsN (π : AdmissiblePolicy L₀ L) (n : ℕ) :
    Measurable (fun ω => obsN π ω n) := (measurable_observe _ _ _).comp (measurable_run π n)

lemma measurable_act (π : AdmissiblePolicy L₀ L) (n : ℕ) :
    Measurable (fun ω => act π ω n) := (π.measurable_f _).comp (measurable_obsN π n)

lemma measurable_actE (π : AdmissiblePolicy L₀ L) (n : ℕ) :
    Measurable (fun ω => ((act π ω n).2 : ℝ)) :=
  measurable_subtype_coe.comp (measurable_snd.comp (measurable_act π n))

lemma measurable_chiV (π : AdmissiblePolicy L₀ L) (n : ℕ) :
    Measurable (fun ω => chiV π ω n) := (measurable_truncPipeline L₀ L).comp (measurable_obsN π n)

lemma measurable_IV (π : AdmissiblePolicy L₀ L) (n : ℕ) :
    Measurable (fun ω => IV π ω n) :=
  (measurable_expeditedPosition L₀ L).comp (measurable_obsN π n)

lemma measurable_qV (π : AdmissiblePolicy L₀ L) (n : ℕ) :
    Measurable (fun ω => qV π ω n) :=
  measurable_pi_lambda _ fun k => measurable_actE π (n + k)

lemma measurable_DV (m : ℕ) : Measurable (DV m) :=
  measurable_pi_lambda _ fun j => (measurable_pi_apply _).comp measurable_fst

lemma split_chiI (μ : DemandLaw) (π : AdmissiblePolicy L₀ L) (n : ℕ) :
    (sampleLaw μ).map (fun ω => ((chiV π ω n, IV π ω n), DV n ω)) =
      ((sampleLaw μ).map (fun ω => (chiV π ω n, IV π ω n))).prod (pathLaw μ) :=
  law_split μ n _ ((measurable_chiV π n).prodMk (measurable_IV π n)) (fun ω y => by
    simp only [chiV, IV, obsN, run_tailMix π n ω y n le_rfl])

lemma split_q (μ : DemandLaw) (π : AdmissiblePolicy L₀ L) (n k : ℕ) :
    (sampleLaw μ).map (fun ω => (((act π ω (n + k)).2 : ℝ), DV (n + k) ω)) =
      ((sampleLaw μ).map (fun ω => ((act π ω (n + k)).2 : ℝ))).prod (pathLaw μ) :=
  law_split μ (n + k) _ (measurable_actE π (n + k)) (fun ω y => by
    simp only [act, obsN, run_tailMix π (n + k) ω y (n + k) le_rfl])


/-! ## P3: Cesàro laws on the window space -/

abbrev E (L₀ L : ℕ) := (Fin (L - L₀ - 1) → ℝ) × (Fin (L - L₀) → ℝ) × ℝ × Path

def V (π : AdmissiblePolicy L₀ L) (n : ℕ) (ω : Sample) : E L₀ L :=
  (chiV π ω n, qV π ω n, IV π ω n, DV n ω)

lemma measurable_V (π : AdmissiblePolicy L₀ L) (n : ℕ) : Measurable (V π n) :=
  (measurable_chiV π n).prodMk ((measurable_qV π n).prodMk
    ((measurable_IV π n).prodMk (measurable_DV n)))

noncomputable def nuT (μ : DemandLaw) (π : AdmissiblePolicy L₀ L) (T : ℕ) : Measure (E L₀ L) :=
  ∑ n ∈ Finset.range T, ((T : ℝ≥0∞)⁻¹) • (sampleLaw μ).map (V π n)

lemma nuT_apply (μ : DemandLaw) (π : AdmissiblePolicy L₀ L) (T : ℕ) (s : Set (E L₀ L))
    (hs : MeasurableSet s) :
    nuT μ π T s = (T : ℝ≥0∞)⁻¹ * ∑ n ∈ Finset.range T, sampleLaw μ (V π n ⁻¹' s) := by
  simp only [nuT, Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    Finset.mul_sum, Measure.map_apply (measurable_V π _) hs]

lemma nuT_isProb (μ : DemandLaw) (π : AdmissiblePolicy L₀ L) (T : ℕ) (hT : 0 < T) :
    IsProbabilityMeasure (nuT μ π T) := by
  constructor
  rw [nuT_apply μ π T _ MeasurableSet.univ]
  simp only [Set.preimage_univ, measure_univ, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hT.ne') (ENNReal.natCast_ne_top T)

lemma lintegral_nuT (μ : DemandLaw) (π : AdmissiblePolicy L₀ L) (T : ℕ) (f : E L₀ L → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ x, f x ∂nuT μ π T =
      (T : ℝ≥0∞)⁻¹ * ∑ n ∈ Finset.range T, ∫⁻ ω, f (V π n ω) ∂sampleLaw μ := by
  rw [nuT, lintegral_finset_sum_measure, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [lintegral_smul_measure, lintegral_map hf (measurable_V π n), smul_eq_mul]

lemma integral_nuT (μ : DemandLaw) (π : AdmissiblePolicy L₀ L) (T : ℕ) (f : E L₀ L → ℝ)
    (hf : Measurable f) (C : ℝ) (hC : ∀ x, |f x| ≤ C) :
    ∫ x, f x ∂nuT μ π T =
      (T : ℝ)⁻¹ * ∑ n ∈ Finset.range T, ∫ ω, f (V π n ω) ∂sampleLaw μ := by
  have hint : ∀ n, Integrable f ((sampleLaw μ).map (V π n)) := fun n =>
    Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact hC x)
  rw [nuT, integral_finset_sum_measure (fun n _ => (hint n).smul_measure
    (ENNReal.inv_ne_top.2 (by
      rcases Nat.eq_zero_or_pos T with h | h
      · simp [h] at *
      · exact_mod_cast h.ne'))), Finset.mul_sum]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_smul_measure, integral_map (measurable_V π n).aemeasurable
      hf.aestronglyMeasurable, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]

lemma sum_shift_bound (a : ℕ → ℝ) (C : ℝ) (ha : ∀ n, |a n| ≤ C) (T k : ℕ) :
    |∑ n ∈ Finset.range T, a (n + k) - ∑ n ∈ Finset.range T, a n| ≤ 2 * k * C := by
  have h1 := Finset.sum_range_add a k T
  have h2 := Finset.sum_range_add a T k
  rw [add_comm k T] at h1
  have e : ∑ n ∈ Finset.range T, a (n + k) - ∑ n ∈ Finset.range T, a n =
      ∑ n ∈ Finset.range k, a (T + n) - ∑ n ∈ Finset.range k, a n := by
    have : ∑ n ∈ Finset.range T, a (n + k) = ∑ n ∈ Finset.range T, a (k + n) :=
      Finset.sum_congr rfl fun n _ => by rw [add_comm]
    rw [this]; linarith
  rw [e]
  have b1 : |∑ n ∈ Finset.range k, a (T + n)| ≤ k * C := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun n _ => ha (T + n)).trans ?_
    simp
  have b2 : |∑ n ∈ Finset.range k, a n| ≤ k * C := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun n _ => ha n).trans ?_
    simp
  calc _ ≤ |∑ n ∈ Finset.range k, a (T + n)| + |∑ n ∈ Finset.range k, a n| := abs_sub _ _
    _ ≤ 2 * k * C := by linarith

/-- Cesàro defect for a shift relation `g ∘ V n = g' ∘ V (n + k)`. -/
lemma defect (μ : DemandLaw) (π : AdmissiblePolicy L₀ L) (T : ℕ) (hT : 0 < T)
    (g g' : E L₀ L → ℝ) (hg : Measurable g) (hg' : Measurable g') (k : ℕ)
    (hrel : ∀ n ω, g (V π n ω) = g' (V π (n + k) ω)) (φ : ℝ →ᵇ ℝ) :
    |∫ x, φ (g x) ∂nuT μ π T - ∫ x, φ (g' x) ∂nuT μ π T| ≤ 2 * k * ‖φ‖ / T := by
  have hb : ∀ y, |φ y| ≤ ‖φ‖ := fun y => by
    rw [← Real.norm_eq_abs]; exact φ.norm_coe_le_norm y
  rw [integral_nuT μ π T (fun x => φ (g x)) (φ.continuous.measurable.comp hg) ‖φ‖ (fun x => hb _),
    integral_nuT μ π T (fun x => φ (g' x)) (φ.continuous.measurable.comp hg') ‖φ‖ (fun x => hb _)]
  set a : ℕ → ℝ := fun n => ∫ ω, φ (g' (V π n ω)) ∂sampleLaw μ with ha
  have hrel' : ∀ n, ∫ ω, φ (g (V π n ω)) ∂sampleLaw μ = a (n + k) := fun n => by
    simp only [ha, hrel]
  simp only [hrel']
  have hab : ∀ n, |a n| ≤ ‖φ‖ := fun n => by
    have := norm_integral_le_of_norm_le_const (μ := sampleLaw μ)
      (f := fun ω => φ (g' (V π n ω))) (C := ‖φ‖) (ae_of_all _ fun ω => φ.norm_coe_le_norm _)
    simpa [Real.norm_eq_abs] using this
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hTr), inv_mul_eq_div]
  exact div_le_div_of_nonneg_right (sum_shift_bound a ‖φ‖ hab T k) hTr.le

/-- Mixtures keep "independent of a fixed law `β`". -/
lemma mix_indep (μ : DemandLaw) (π : AdmissiblePolicy L₀ L) (T : ℕ) (hT : 0 < T)
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (f : E L₀ L → X) (g : E L₀ L → Y)
    (hf : Measurable f) (hg : Measurable g) (β : Measure Y) [IsProbabilityMeasure β]
    (h : ∀ n, (sampleLaw μ).map (fun ω => (f (V π n ω), g (V π n ω))) =
      ((sampleLaw μ).map (fun ω => f (V π n ω))).prod β) :
    (nuT μ π T).map (fun x => (f x, g x)) = ((nuT μ π T).map f).prod β := by
  haveI := nuT_isProb μ π T hT
  symm
  apply Measure.prod_eq
  intro s t hs ht
  rw [Measure.map_apply (hf.prodMk hg) (hs.prod ht), Measure.map_apply hf hs,
    nuT_apply μ π T _ ((hf.prodMk hg) (hs.prod ht)), nuT_apply μ π T _ (hf hs), mul_assoc,
    Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  have e := congrArg (fun ρ : Measure (X × Y) => ρ (s ×ˢ t)) (h n)
  have m1 : Measurable (fun ω => (f (V π n ω), g (V π n ω))) :=
    (hf.comp (measurable_V π n)).prodMk (hg.comp (measurable_V π n))
  have m2 : Measurable (fun ω => f (V π n ω)) := hf.comp (measurable_V π n)
  rw [Measure.map_apply m1 (hs.prod ht), Measure.prod_prod, Measure.map_apply m2 hs] at e
  exact e

lemma nuT_path (μ : DemandLaw) (π : AdmissiblePolicy L₀ L) (T : ℕ) (hT : 0 < T) :
    (nuT μ π T).map (fun x => x.2.2.2) = pathLaw μ := by
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs, nuT_apply μ π T _ ((by fun_prop : Measurable
    (fun x : E L₀ L => x.2.2.2)) hs)]
  have : ∀ n, sampleLaw μ (V π n ⁻¹' ((fun x : E L₀ L => x.2.2.2) ⁻¹' s)) = pathLaw μ s := by
    intro n
    rw [← law_DV μ n, Measure.map_apply (measurable_DV n) hs]
    rfl
  simp only [this, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc]
  rw [ENNReal.inv_mul_cancel (by exact_mod_cast hT.ne') (ENNReal.natCast_ne_top T), one_mul]

lemma nuT_indep_chiI (μ : DemandLaw) (π : AdmissiblePolicy L₀ L) (T : ℕ) (hT : 0 < T) :
    (nuT μ π T).map (fun x => ((x.1, x.2.2.1), x.2.2.2)) =
      ((nuT μ π T).map (fun x => (x.1, x.2.2.1))).prod (pathLaw μ) :=
  mix_indep μ π T hT (fun x : E L₀ L => (x.1, x.2.2.1)) (fun x => x.2.2.2) (by fun_prop)
    (by fun_prop) _ (fun n => split_chiI μ π n)

lemma nuT_indep_q (μ : DemandLaw) (π : AdmissiblePolicy L₀ L) (T : ℕ) (hT : 0 < T)
    (k : Fin (L - L₀)) :
    (nuT μ π T).map (fun x => (x.2.1 k, fun j => x.2.2.2 (k.val + j))) =
      ((nuT μ π T).map (fun x => x.2.1 k)).prod (pathLaw μ) := by
  refine mix_indep μ π T hT (fun x : E L₀ L => x.2.1 k) (fun x j => x.2.2.2 (k.val + j))
    (by fun_prop) (by fun_prop) _ (fun n => ?_)
  have := split_q μ π n k.val
  convert this using 3
  all_goals first | rfl | (refine Prod.ext rfl ?_; funext j; simp [V, DV, add_assoc])


/-! ## P5: a stationary witness from a limit law on `E` -/

def qE0 (x : E L₀ L) : ℝ := qN L₀ L (fun y : E L₀ L => y.2.1) x 0

def stat0 (x : E L₀ L) : ℝ :=
  x.2.2.1 + qN L₀ L (fun y : E L₀ L => y.2.1) x 0 - ∑ i ∈ Finset.range (L₀ + 1), x.2.2.2 i

def statF (k : Fin (L - L₀)) (x : E L₀ L) : ℝ :=
  x.2.2.1 + ∑ i ∈ Finset.range k.val, (qN L₀ L (fun y : E L₀ L => y.2.1) x i +
    chiN L₀ L (fun y : E L₀ L => y.1) x i - x.2.2.2 i) + x.2.1 k -
    ∑ i ∈ Finset.range (L₀ + 1), x.2.2.2 (k.val + i)

lemma continuous_qN (i : ℕ) : Continuous (fun x : E L₀ L => qN L₀ L (fun y : E L₀ L => y.2.1) x i) := by
  unfold qN
  split_ifs
  · fun_prop
  · exact continuous_const

lemma continuous_chiN (i : ℕ) : Continuous (fun x : E L₀ L => chiN L₀ L (fun y : E L₀ L => y.1) x i) := by
  unfold chiN
  split_ifs
  · fun_prop
  · exact continuous_const

lemma continuous_stat0 : Continuous (stat0 : E L₀ L → ℝ) := by
  unfold stat0
  refine ((continuous_snd.comp continuous_snd).fst.add (continuous_qN 0)).sub ?_
  exact continuous_finsetSum _ fun i _ => by fun_prop

lemma continuous_statF (k : Fin (L - L₀)) : Continuous (statF k : E L₀ L → ℝ) := by
  unfold statF
  refine (((continuous_snd.comp continuous_snd).fst.add ?_).add ?_).sub ?_
  · exact continuous_finsetSum _ fun i _ => ((continuous_qN i).add (continuous_chiN i)).sub
      (by fun_prop)
  · fun_prop
  · exact continuous_finsetSum _ fun i _ => by fun_prop

lemma witness_of (μ : DemandLaw) (κ : Costs) (hL : L₀ + 1 < L) (ν : Measure (E L₀ L))
    [IsProbabilityMeasure ν]
    (W1 : ν.map (fun x => x.2.2.2) = pathLaw μ)
    (W2 : ν.map (fun x => ((x.1, x.2.2.1), x.2.2.2)) =
      (ν.map (fun x => (x.1, x.2.2.1))).prod (pathLaw μ))
    (W3 : ∀ k : Fin (L - L₀), ν.map (fun x => (x.2.1 k, fun j => x.2.2.2 (k.val + j))) =
      (ν.map (fun x => x.2.1 k)).prod (pathLaw μ))
    (W4 : ∀ᵐ x ∂ν, (∀ j, 0 ≤ x.1 j) ∧ ∀ j, 0 ≤ x.2.1 j)
    (W5c : ∀ i : Fin (L - L₀ - 1), ν.map (fun x => x.1 i) = ν.map (fun x => x.1 ⟨0, by omega⟩))
    (W5q : ∀ i : Fin (L - L₀), ν.map (fun x => x.2.1 i) = ν.map (fun x => x.2.1 ⟨0, by omega⟩))
    (W5s : ∀ k : Fin (L - L₀), ν.map (statF k) = ν.map stat0)
    (W6c : ∀ j, ∫⁻ x, ENNReal.ofReal |x.1 j| ∂ν ≠ ⊤)
    (W6q : ∀ j, ∫⁻ x, ENNReal.ofReal |x.2.1 j| ∂ν ≠ ⊤)
    (W6I : ∫⁻ x, ENNReal.ofReal |x.2.2.1| ∂ν ≠ ⊤)
    (W7 : ∫⁻ x, (ENNReal.ofReal (κ.c * qE0 x) + ENNReal.ofReal (G κ (stat0 x))) ∂ν ≤
      OPT μ κ L₀ L) :
    IsStationaryWitness ν μ κ L₀ L (fun x => x.1) (fun x => x.2.1) (fun x => x.2.2.1)
      (fun j x => x.2.2.2 j) := by
  have h0c : 0 < L - L₀ - 1 := by omega
  have h0q : 0 < L - L₀ := by omega
  have hmD : ∀ j, Measurable (fun x : E L₀ L => x.2.2.2 j) := fun j => by fun_prop
  have lawD : ∀ j, ν.map (fun x : E L₀ L => x.2.2.2 j) = μ.law := by
    intro j
    have : (fun x : E L₀ L => x.2.2.2 j) = (fun p : Path => p j) ∘ (fun x : E L₀ L => x.2.2.2) :=
      rfl
    rw [this, ← Measure.map_map (measurable_pi_apply j) (by fun_prop), W1]
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => μ.law) j).map_eq
  have intD : ∀ j, Integrable (fun x : E L₀ L => x.2.2.2 j) ν := by
    intro j
    have h : Integrable id (ν.map (fun x : E L₀ L => x.2.2.2 j)) := by
      rw [lawD j]; exact μ.integrable
    exact (integrable_map_measure h.1 (hmD j).aemeasurable).1 h
  have meanD : ∀ j, ∫ x, x.2.2.2 j ∂ν = μ.mean := by
    intro j
    rw [DemandLaw.mean, ← lawD j]
    exact (integral_map (f := fun d : ℝ => d) (hmD j).aemeasurable aestronglyMeasurable_id).symm
  have intOf : ∀ f : E L₀ L → ℝ, Measurable f → ∫⁻ x, ENNReal.ofReal |f x| ∂ν ≠ ⊤ →
      Integrable f ν := fun f hf h =>
    ⟨hf.aestronglyMeasurable, by
      simpa [HasFiniteIntegral, Real.enorm_eq_ofReal_abs, lt_top_iff_ne_top] using h⟩
  have iC : ∀ j, Integrable (fun x : E L₀ L => x.1 j) ν := fun j => intOf _ (by fun_prop) (W6c j)
  have iQ : ∀ j, Integrable (fun x : E L₀ L => x.2.1 j) ν := fun j => intOf _ (by fun_prop) (W6q j)
  have iI : Integrable (fun x : E L₀ L => x.2.2.1) ν := intOf _ (by fun_prop) W6I
  have eq0 : (fun x : E L₀ L => qN L₀ L (fun y : E L₀ L => y.2.1) x 0) =
      fun x => x.2.1 ⟨0, h0q⟩ := funext fun x => dif_pos h0q
  have hq0 : ∀ x : E L₀ L, qN L₀ L (fun y : E L₀ L => y.2.1) x 0 = x.2.1 ⟨0, h0q⟩ :=
    fun x => dif_pos h0q
  have ec0 : (fun x : E L₀ L => chiN L₀ L (fun y : E L₀ L => y.1) x 0) =
      fun x => x.1 ⟨0, h0c⟩ := funext fun x => dif_pos h0c
  -- mean balance from stationarity at k = 1
  have h01 : 1 < L - L₀ := by omega
  have hdiff : ∀ x : E L₀ L, statF ⟨1, h01⟩ x =
      stat0 x + (x.1 ⟨0, h0c⟩ + x.2.1 ⟨1, h01⟩ - x.2.2.2 (L₀ + 1)) := by
    intro x
    have a1 := congrFun eq0 x
    have a2 := congrFun ec0 x
    simp only [statF, stat0, Finset.sum_range_one, a1, a2]
    rw [Finset.sum_range_succ' (fun i => x.2.2.2 i), Finset.sum_range_succ (fun i => x.2.2.2 (1 + i))]
    have : ∑ i ∈ Finset.range L₀, x.2.2.2 (1 + i) = ∑ i ∈ Finset.range L₀, x.2.2.2 (i + 1) :=
      Finset.sum_congr rfl fun i _ => by rw [add_comm]
    rw [this, add_comm 1 L₀]
    ring
  have iS0 : Integrable (stat0 : E L₀ L → ℝ) ν := by
    have : (stat0 : E L₀ L → ℝ) = fun x => x.2.2.1 + x.2.1 ⟨0, h0q⟩ -
        ∑ i ∈ Finset.range (L₀ + 1), x.2.2.2 i := by
      funext x; simp only [stat0, congrFun eq0 x]
    rw [this]
    exact (iI.add (iQ _)).sub (integrable_finset_sum _ fun i _ => intD i)
  have iDf : Integrable (fun x : E L₀ L => x.1 ⟨0, h0c⟩ + x.2.1 ⟨1, h01⟩ - x.2.2.2 (L₀ + 1)) ν :=
    ((iC _).add (iQ _)).sub (intD _)
  have hid1 : IdentDistrib (statF ⟨1, h01⟩) stat0 ν ν :=
    ⟨(continuous_statF _).measurable.aemeasurable, continuous_stat0.measurable.aemeasurable,
      W5s ⟨1, h01⟩⟩
  have hint := hid1.integral_eq
  rw [funext hdiff, integral_add iS0 iDf] at hint
  have hD0 : ∫ x, (x.1 ⟨0, h0c⟩ + x.2.1 ⟨1, h01⟩ - x.2.2.2 (L₀ + 1)) ∂ν = 0 := by linarith
  have iA : Integrable (fun x : E L₀ L => x.1 ⟨0, h0c⟩ + x.2.1 ⟨1, h01⟩) ν := (iC _).add (iQ _)
  rw [integral_sub iA (intD _), integral_add (iC _) (iQ _), meanD] at hD0
  have hq1 : ∫ x, x.2.1 ⟨1, h01⟩ ∂ν = ∫ x, x.2.1 ⟨0, h0q⟩ ∂ν :=
    (IdentDistrib.integral_eq ⟨by fun_prop, by fun_prop, W5q ⟨1, h01⟩⟩)
  have hmean : (∫ x, chiN L₀ L (fun y : E L₀ L => y.1) x 0 ∂ν) +
      (∫ x, qN L₀ L (fun y : E L₀ L => y.2.1) x 0 ∂ν) = μ.mean := by
    rw [ec0, eq0]; linarith
  refine
    { isProb := inferInstance
      measurable_chi := measurable_fst
      measurable_q := by fun_prop
      measurable_I := by fun_prop
      measurable_D := hmD
      law_D := lawD
      indep_D := ?_
      nonneg := W4
      indep_chi_I := ?_
      indep_q := ?_
      ident_chi := fun i j => ⟨by fun_prop, by fun_prop, (W5c i).trans (W5c j).symm⟩
      ident_q := fun i j => ⟨by fun_prop, by fun_prop, (W5q i).trans (W5q j).symm⟩
      stationary := fun k => ⟨(continuous_statF k).measurable.aemeasurable,
        continuous_stat0.measurable.aemeasurable, W5s k⟩
      integrable_chi := iC
      integrable_q := iQ
      integrable_I := iI
      mean_eq := hmean
      opt_ge := ?_ }
  · rw [iIndepFun_iff_map_fun_eq_infinitePi_map₀' (fun i => (hmD i).aemeasurable)]
    simp only [lawD]
    exact W1
  · rw [indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)]
    have e : ν.map (fun (ω : E L₀ L) (j : ℕ) => ω.2.2.2 j) = pathLaw μ := W1
    rw [e]
    exact W2
  · intro k
    rw [indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)]
    have e : ν.map (fun (ω : E L₀ L) (j : ℕ) => ω.2.2.2 (k.val + j)) = pathLaw μ := by
      have h := congrArg (fun ρ : Measure (ℝ × Path) => ρ.map Prod.snd) (W3 k)
      rw [Measure.map_map measurable_snd (by fun_prop), Measure.map_snd_prod,
        Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ, measure_univ,
        one_smul] at h
      exact h
    rw [e]
    exact W3 k
  · have hm := hmean
    have hsub : μ.mean - ∫ x, chiN L₀ L (fun y : E L₀ L => y.1) x 0 ∂ν = ∫ x, qE0 x ∂ν := by
      unfold qE0; linarith
    rw [hsub, ← integral_const_mul, ofReal_integral_eq_lintegral_ofReal]
    · rw [← lintegral_add_left]
      · exact W7
      · exact (ENNReal.measurable_ofReal.comp ((continuous_qN 0).measurable.const_mul κ.c))
    · exact ((iQ ⟨0, h0q⟩).const_mul κ.c).congr (ae_of_all _ fun x => by
        show κ.c * x.2.1 ⟨0, h0q⟩ = κ.c * qN L₀ L (fun y : E L₀ L => y.2.1) x 0
        rw [hq0])
    · filter_upwards [W4] with x hx
      show 0 ≤ κ.c * qN L₀ L (fun y : E L₀ L => y.2.1) x 0
      rw [hq0]
      exact mul_nonneg κ.c_pos.le (hx.2 _)


/-! ## P4: tightness, Prokhorov and passage to the limit -/

lemma G_nonneg (κ : Costs) (z : ℝ) : 0 ≤ G κ z := by
  unfold G
  have := κ.h_pos; have := κ.b_pos
  positivity

lemma G_ge (κ : Costs) (z : ℝ) : min κ.b κ.h * |z| ≤ G κ z := by
  unfold G
  have hb := min_le_left κ.b κ.h
  have hh := min_le_right κ.b κ.h
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz, max_eq_left hz, max_eq_right (by linarith : -z ≤ 0)]
    nlinarith
  · rw [abs_of_nonpos hz, max_eq_right hz, max_eq_left (by linarith : 0 ≤ -z)]
    nlinarith

lemma continuous_G (κ : Costs) : Continuous (G κ) := by
  unfold G
  exact (continuous_const.mul (continuous_id.max continuous_const)).add
    (continuous_const.mul (continuous_neg.max continuous_const))

lemma isClosed_lintegral_le {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (h : X → ℝ) (hc : Continuous h) (h0 : ∀ x, 0 ≤ h x) (M : ℝ)
    (hM : 0 ≤ M) :
    IsClosed {ρ : ProbabilityMeasure X |
      ∫⁻ x, ENNReal.ofReal (h x) ∂(ρ : Measure X) ≤ ENNReal.ofReal M} := by
  have hb : ∀ n : ℕ, ∀ x, ‖min (h x) (n : ℝ)‖ ≤ n := fun n x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (h0 x) n.cast_nonneg)]; exact min_le_right _ _
  have hint : ∀ (ρ : ProbabilityMeasure X) (n : ℕ),
      Integrable (fun x => min (h x) (n : ℝ)) (ρ : Measure X) := fun ρ n =>
    Integrable.of_bound (hc.min continuous_const).aestronglyMeasurable n (ae_of_all _ (hb n))
  have hnn : ∀ (ρ : ProbabilityMeasure X) (n : ℕ),
      0 ≤ᵐ[(ρ : Measure X)] (fun x => min (h x) (n : ℝ)) :=
    fun ρ n => ae_of_all _ fun x => le_min (h0 x) n.cast_nonneg
  have hset : {ρ : ProbabilityMeasure X |
      ∫⁻ x, ENNReal.ofReal (h x) ∂(ρ : Measure X) ≤ ENNReal.ofReal M} =
      ⋂ n : ℕ, {ρ : ProbabilityMeasure X | ∫ x, min (h x) (n : ℝ) ∂(ρ : Measure X) ≤ M} := by
    ext ρ
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro H n
      have : ENNReal.ofReal (∫ x, min (h x) (n : ℝ) ∂(ρ : Measure X)) ≤ ENNReal.ofReal M := by
        rw [ofReal_integral_eq_lintegral_ofReal (hint ρ n) (hnn ρ n)]
        exact (lintegral_mono fun x => ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans H
      exact (ENNReal.ofReal_le_ofReal_iff hM).1 this
    · intro H
      have hsup : ∀ x, ENNReal.ofReal (h x) = ⨆ n : ℕ, ENNReal.ofReal (min (h x) (n : ℝ)) := by
        intro x
        refine le_antisymm ?_ (iSup_le fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _))
        obtain ⟨n, hn⟩ := exists_nat_ge (h x)
        exact le_iSup_of_le n (by rw [min_eq_left hn])
      have hm : ∀ n : ℕ, Measurable (fun x => ENNReal.ofReal (min (h x) (n : ℝ))) :=
        fun n => ENNReal.measurable_ofReal.comp (hc.min continuous_const).measurable
      rw [lintegral_congr hsup, lintegral_iSup hm
        (fun a b hab x => ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.2 hab)))]
      refine iSup_le fun n => ?_
      rw [← ofReal_integral_eq_lintegral_ofReal (hint ρ n) (hnn ρ n)]
      exact ENNReal.ofReal_le_ofReal (H n)
  rw [hset]
  refine isClosed_iInter fun n => isClosed_le ?_ continuous_const
  exact ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (BoundedContinuousFunction.ofNormedAddCommGroup (fun x => min (h x) (n : ℝ))
      (hc.min continuous_const) n (hb n))

lemma tight_of_moment {W : Type*} [NormedAddCommGroup W] [ProperSpace W] [MeasurableSpace W]
    [BorelSpace W] (S : Set (Measure W)) (M : ℝ≥0∞) (hM : M ≠ ⊤)
    (h : ∀ ρ ∈ S, ∫⁻ w, ENNReal.ofReal ‖w‖ ∂ρ ≤ M) : IsTightMeasureSet S := by
  apply isTightMeasureSet_of_tendsto_measure_norm_gt
  have hb : ∀ r : ℝ, 0 < r → (⨆ ρ ∈ S, ρ {x | r < ‖x‖}) ≤ M / ENNReal.ofReal r := by
    intro r hr
    refine iSup₂_le fun ρ hρ => ?_
    calc ρ {x | r < ‖x‖} ≤ ρ {x | ENNReal.ofReal r ≤ ENNReal.ofReal ‖x‖} :=
          measure_mono fun x hx => ENNReal.ofReal_le_ofReal (le_of_lt hx)
      _ ≤ (∫⁻ w, ENNReal.ofReal ‖w‖ ∂ρ) / ENNReal.ofReal r :=
          meas_ge_le_lintegral_div (by fun_prop) (ENNReal.ofReal_pos.2 hr).ne'
            ENNReal.ofReal_ne_top
      _ ≤ M / ENNReal.ofReal r := by gcongr; exact h ρ hρ
  have ht : Tendsto (fun r : ℝ => M / ENNReal.ofReal r) atTop (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => ENNReal.ofReal r) atTop (𝓝 ⊤) := ENNReal.tendsto_ofReal_atTop
    have h3 : Tendsto (fun r : ℝ => (ENNReal.ofReal r)⁻¹) atTop (𝓝 0) := by
      rw [← ENNReal.inv_top]; exact ENNReal.tendsto_inv_iff.2 h1
    have := ENNReal.Tendsto.const_mul h3 (Or.inr hM)
    simpa [div_eq_mul_inv] using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Eventually.of_forall fun r => bot_le) ?_
  filter_upwards [eventually_gt_atTop 0] with r hr using hb r hr

lemma mem_of_cluster {X : Type*} [TopologicalSpace X] {u : ℕ → X} {ν : X}
    (hν : ClusterPt ν (Filter.map u atTop)) {C : Set X} (hC : IsClosed C)
    (hev : ∀ᶠ N in atTop, u N ∈ C) : ν ∈ C := by
  have h1 : ClusterPt ν (𝓟 C) := hν.mono (Filter.le_principal_iff.2 (Filter.mem_map.2 hev))
  have : ν ∈ closure C := mem_closure_iff_clusterPt.2 h1
  rwa [hC.closure_eq] at this

lemma eq_of_abs_le_all {a b : ℝ} (h : ∀ ε > 0, |a - b| ≤ ε) : a = b := by
  by_contra hne
  have hp : 0 < |a - b| := abs_pos.2 (sub_ne_zero.2 hne)
  have := h (|a - b| / 2) (by linarith)
  linarith

/-- The `ℝ≥0∞` cost integrand of (vi) as `ofReal` of a continuous nonnegative function. -/
def Jh (κ : Costs) (x : E L₀ L) : ℝ := max (κ.c * qE0 x) 0 + G κ (stat0 x)

lemma Jh_nonneg (κ : Costs) (x : E L₀ L) : 0 ≤ Jh κ x :=
  add_nonneg (le_max_right _ _) (G_nonneg _ _)

lemma continuous_Jh (κ : Costs) : Continuous (Jh κ : E L₀ L → ℝ) := by
  unfold Jh qE0
  exact ((continuous_const.mul (continuous_qN 0)).max continuous_const).add
    ((continuous_G κ).comp continuous_stat0)

lemma ofReal_Jh (κ : Costs) (x : E L₀ L) :
    ENNReal.ofReal (Jh κ x) = ENNReal.ofReal (κ.c * qE0 x) + ENNReal.ofReal (G κ (stat0 x)) := by
  unfold Jh
  rw [ENNReal.ofReal_add (le_max_right _ _) (G_nonneg _ _)]
  congr 1
  rcases le_total 0 (κ.c * qE0 x) with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]

/-- Negativity detector. -/
def negF (x : E L₀ L) : ℝ :=
  ∑ j, min 1 (max (-x.1 j) 0) + ∑ k, min 1 (max (-x.2.1 k) 0)

lemma continuous_negF : Continuous (negF : E L₀ L → ℝ) := by
  unfold negF
  refine (continuous_finsetSum _ fun j _ => ?_).add (continuous_finsetSum _ fun k _ => ?_)
  · fun_prop
  · fun_prop

lemma negF_nonneg (x : E L₀ L) : 0 ≤ negF x := by
  unfold negF
  exact add_nonneg (Finset.sum_nonneg fun j _ => le_min zero_le_one (le_max_right _ _))
    (Finset.sum_nonneg fun j _ => le_min zero_le_one (le_max_right _ _))

lemma negF_le (x : E L₀ L) : ‖negF x‖ ≤ (L - L₀ - 1 : ℕ) + (L - L₀ : ℕ) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (negF_nonneg x)]
  unfold negF
  have h1 : ∑ j, min 1 (max (-x.1 j) 0) ≤ ∑ _j : Fin (L - L₀ - 1), (1 : ℝ) :=
    Finset.sum_le_sum fun j _ => min_le_left _ _
  have h2 : ∑ k, min 1 (max (-x.2.1 k) 0) ≤ ∑ _k : Fin (L - L₀), (1 : ℝ) :=
    Finset.sum_le_sum fun j _ => min_le_left _ _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h1 h2
  linarith

lemma negF_zero_of (x : E L₀ L) (hx : (∀ j, 0 ≤ x.1 j) ∧ ∀ j, 0 ≤ x.2.1 j) : negF x = 0 := by
  unfold negF
  rw [Finset.sum_eq_zero fun j _ => by rw [max_eq_right (by linarith [hx.1 j]), min_eq_right zero_le_one],
    Finset.sum_eq_zero fun j _ => by rw [max_eq_right (by linarith [hx.2 j]), min_eq_right zero_le_one]]
  simp

lemma nonneg_of_negF (x : E L₀ L) (hx : negF x = 0) : (∀ j, 0 ≤ x.1 j) ∧ ∀ j, 0 ≤ x.2.1 j := by
  unfold negF at hx
  have hA := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) =>
    le_min zero_le_one (le_max_right (-x.1 j) 0)
  have hB := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) =>
    le_min zero_le_one (le_max_right (-x.2.1 j) 0)
  have h1 : ∑ j, min 1 (max (-x.1 j) 0) = 0 := by linarith
  have h2 : ∑ k, min 1 (max (-x.2.1 k) 0) = 0 := by linarith
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => le_min zero_le_one (le_max_right _ _))] at h1 h2
  have key : ∀ a : ℝ, min 1 (max (-a) 0) = 0 → 0 ≤ a := by
    intro a ha
    by_contra hneg
    push_neg at hneg
    have : 0 < min 1 (max (-a) 0) := lt_min one_pos (lt_max_of_lt_left (by linarith))
    linarith
  exact ⟨fun j => key _ (h1 j (Finset.mem_univ _)), fun j => key _ (h2 j (Finset.mem_univ _))⟩


lemma norm_le_sum_abs {n : ℕ} (v : Fin n → ℝ) : ‖v‖ ≤ ∑ j, |v j| :=
  (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)).2 fun j => by
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun j => |v j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)

lemma lint_norm_pi {n : ℕ} (ρ : Measure (E L₀ L)) (f : E L₀ L → Fin n → ℝ) (hf : Continuous f)
    (Mc : ℝ) (h : ∀ j, ∫⁻ x, ENNReal.ofReal |f x j| ∂ρ ≤ ENNReal.ofReal Mc) :
    ∫⁻ x, ENNReal.ofReal ‖f x‖ ∂ρ ≤ n * ENNReal.ofReal Mc := by
  calc ∫⁻ x, ENNReal.ofReal ‖f x‖ ∂ρ ≤ ∫⁻ x, ∑ j, ENNReal.ofReal |f x j| ∂ρ := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => abs_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (norm_le_sum_abs _)
    _ = ∑ j, ∫⁻ x, ENNReal.ofReal |f x j| ∂ρ :=
        lintegral_finset_sum _ (fun j _ => ENNReal.measurable_ofReal.comp
          ((continuous_apply j).comp hf).abs.measurable)
    _ ≤ ∑ _j : Fin n, ENNReal.ofReal Mc := Finset.sum_le_sum fun j _ => h j
    _ = n * ENNReal.ofReal Mc := by simp

theorem witness_of_seq (μ : DemandLaw) (κ : Costs) (hL : L₀ + 1 < L)
    (u : ℕ → ProbabilityMeasure (E L₀ L)) (Or : ℝ) (hOr : 0 ≤ Or)
    (hOPT : OPT μ κ L₀ L = ENNReal.ofReal Or) (Mc : ℝ) (hMc : 0 ≤ Mc)
    (U1 : ∀ N, (u N : Measure (E L₀ L)).map (fun x => x.2.2.2) = pathLaw μ)
    (U2 : ∀ N, (u N : Measure (E L₀ L)).map (fun x => ((x.1, x.2.2.1), x.2.2.2)) =
      ((u N : Measure (E L₀ L)).map (fun x => (x.1, x.2.2.1))).prod (pathLaw μ))
    (U3 : ∀ N (k : Fin (L - L₀)),
      (u N : Measure (E L₀ L)).map (fun x => (x.2.1 k, fun j => x.2.2.2 (k.val + j))) =
        ((u N : Measure (E L₀ L)).map (fun x => x.2.1 k)).prod (pathLaw μ))
    (U4 : ∀ N, ∀ᵐ x ∂(u N : Measure (E L₀ L)), (∀ j, 0 ≤ x.1 j) ∧ ∀ j, 0 ≤ x.2.1 j)
    (U5c : ∀ i : Fin (L - L₀ - 1), ∀ φ : ℝ →ᵇ ℝ, ∀ ε > 0, ∀ᶠ N in atTop,
      |∫ x, φ (x.1 i) ∂(u N : Measure (E L₀ L)) -
        ∫ x, φ (x.1 ⟨0, by omega⟩) ∂(u N : Measure (E L₀ L))| ≤ ε)
    (U5q : ∀ i : Fin (L - L₀), ∀ φ : ℝ →ᵇ ℝ, ∀ ε > 0, ∀ᶠ N in atTop,
      |∫ x, φ (x.2.1 i) ∂(u N : Measure (E L₀ L)) -
        ∫ x, φ (x.2.1 ⟨0, by omega⟩) ∂(u N : Measure (E L₀ L))| ≤ ε)
    (U5s : ∀ k : Fin (L - L₀), ∀ φ : ℝ →ᵇ ℝ, ∀ ε > 0, ∀ᶠ N in atTop,
      |∫ x, φ (statF k x) ∂(u N : Measure (E L₀ L)) -
        ∫ x, φ (stat0 x) ∂(u N : Measure (E L₀ L))| ≤ ε)
    (U6 : ∀ N, (∀ j, ∫⁻ x, ENNReal.ofReal |x.1 j| ∂(u N : Measure (E L₀ L)) ≤ ENNReal.ofReal Mc) ∧
      (∀ j, ∫⁻ x, ENNReal.ofReal |x.2.1 j| ∂(u N : Measure (E L₀ L)) ≤ ENNReal.ofReal Mc) ∧
      ∫⁻ x, ENNReal.ofReal |x.2.2.1| ∂(u N : Measure (E L₀ L)) ≤ ENNReal.ofReal Mc)
    (U7 : ∀ ε > 0, ∀ᶠ N in atTop,
      ∫⁻ x, ENNReal.ofReal (Jh κ x) ∂(u N : Measure (E L₀ L)) ≤ ENNReal.ofReal (Or + ε)) :
    ∃ ν : Measure (E L₀ L), IsProbabilityMeasure ν ∧
      IsStationaryWitness ν μ κ L₀ L (fun x => x.1) (fun x => x.2.1) (fun x => x.2.2.1)
        (fun j x => x.2.2.2 j) := by
  -- tightness
  have hT : IsTightMeasureSet
      {m | ∃ ρ ∈ Set.range u, (ρ : Measure (E L₀ L)) = m} := by
    apply IsTightMeasureSet.prodMk
    · refine tight_of_moment _ ((L - L₀ - 1 : ℕ) * ENNReal.ofReal Mc)
        (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top) ?_
      rintro _ ⟨_, ⟨_, ⟨N, rfl⟩, rfl⟩, rfl⟩
      rw [Measure.fst, lintegral_map (by fun_prop) measurable_fst]
      exact lint_norm_pi _ (fun x => x.1) continuous_fst Mc (U6 N).1
    · apply IsTightMeasureSet.prodMk
      · refine tight_of_moment _ ((L - L₀ : ℕ) * ENNReal.ofReal Mc)
          (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top) ?_
        rintro _ ⟨_, ⟨_, ⟨_, ⟨N, rfl⟩, rfl⟩, rfl⟩, rfl⟩
        rw [Measure.fst, Measure.snd, lintegral_map (by fun_prop) measurable_fst,
          lintegral_map (by fun_prop) measurable_snd]
        exact lint_norm_pi _ (fun x => x.2.1) (by fun_prop) Mc (U6 N).2.1
      · apply IsTightMeasureSet.prodMk
        · refine tight_of_moment _ (ENNReal.ofReal Mc) ENNReal.ofReal_ne_top ?_
          rintro _ ⟨_, ⟨_, ⟨_, ⟨_, ⟨N, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
          rw [Measure.fst, Measure.snd, Measure.snd, lintegral_map (by fun_prop) measurable_fst,
            lintegral_map (by fun_prop) measurable_snd, lintegral_map (by fun_prop) measurable_snd]
          simpa [Real.norm_eq_abs] using (U6 N).2.2
        · refine (isTightMeasureSet_singleton (μ := pathLaw μ)).subset ?_
          rintro _ ⟨_, ⟨_, ⟨_, ⟨_, ⟨N, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
          rw [Set.mem_singleton_iff, Measure.snd, Measure.snd, Measure.snd,
            Measure.map_map measurable_snd measurable_snd,
            Measure.map_map (measurable_snd.comp measurable_snd) measurable_snd]
          exact U1 N
  have hK := isCompact_closure_of_isTightMeasureSet (S := Set.range u) hT
  obtain ⟨ν, -, hν⟩ := hK.exists_clusterPt (f := Filter.map u atTop)
    (Filter.tendsto_principal.2 (Eventually.of_forall fun N =>
      subset_closure (Set.mem_range_self N)))
  let P0 : ProbabilityMeasure Path := ⟨pathLaw μ, inferInstance⟩
  -- W1
  have c1 : Continuous (fun x : E L₀ L => x.2.2.2) := by fun_prop
  have W1 : (ν : Measure (E L₀ L)).map (fun x => x.2.2.2) = pathLaw μ := by
    have h1 := mem_of_cluster hν (C := {ρ | ρ.map c1.measurable.aemeasurable = P0})
      (isClosed_eq (ProbabilityMeasure.continuous_map c1) continuous_const)
      (Eventually.of_forall fun N => ProbabilityMeasure.toMeasure_injective (by
        rw [ProbabilityMeasure.toMeasure_map]; exact U1 N))
    have := congrArg ProbabilityMeasure.toMeasure h1
    rw [ProbabilityMeasure.toMeasure_map] at this
    exact this
  -- W2
  have c2 : Continuous (fun x : E L₀ L => ((x.1, x.2.2.1), x.2.2.2)) := by fun_prop
  have c2' : Continuous (fun x : E L₀ L => (x.1, x.2.2.1)) := by fun_prop
  have W2 : (ν : Measure (E L₀ L)).map (fun x => ((x.1, x.2.2.1), x.2.2.2)) =
      ((ν : Measure (E L₀ L)).map (fun x => (x.1, x.2.2.1))).prod (pathLaw μ) := by
    have h1 := mem_of_cluster hν (C := {ρ | ρ.map c2.measurable.aemeasurable =
        (ρ.map c2'.measurable.aemeasurable).prod P0})
      (isClosed_eq (ProbabilityMeasure.continuous_map c2)
        (ProbabilityMeasure.continuous_prod.comp
          ((ProbabilityMeasure.continuous_map c2').prodMk continuous_const)))
      (Eventually.of_forall fun N => ProbabilityMeasure.toMeasure_injective (by
        rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_prod,
          ProbabilityMeasure.toMeasure_map]
        exact U2 N))
    have := congrArg ProbabilityMeasure.toMeasure h1
    rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_prod,
      ProbabilityMeasure.toMeasure_map] at this
    exact this
  -- W3
  have W3 : ∀ k : Fin (L - L₀), (ν : Measure (E L₀ L)).map
      (fun x => (x.2.1 k, fun j => x.2.2.2 (k.val + j))) =
      ((ν : Measure (E L₀ L)).map (fun x => x.2.1 k)).prod (pathLaw μ) := by
    intro k
    have c3 : Continuous (fun x : E L₀ L => (x.2.1 k, fun j => x.2.2.2 (k.val + j))) := by
      fun_prop
    have c3' : Continuous (fun x : E L₀ L => x.2.1 k) := by fun_prop
    have h1 := mem_of_cluster hν (C := {ρ | ρ.map c3.measurable.aemeasurable =
        (ρ.map c3'.measurable.aemeasurable).prod P0})
      (isClosed_eq (ProbabilityMeasure.continuous_map c3)
        (ProbabilityMeasure.continuous_prod.comp
          ((ProbabilityMeasure.continuous_map c3').prodMk continuous_const)))
      (Eventually.of_forall fun N => ProbabilityMeasure.toMeasure_injective (by
        rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_prod,
          ProbabilityMeasure.toMeasure_map]
        exact U3 N k))
    have := congrArg ProbabilityMeasure.toMeasure h1
    rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_prod,
      ProbabilityMeasure.toMeasure_map] at this
    exact this
  -- W4
  have W4 : ∀ᵐ x ∂(ν : Measure (E L₀ L)), (∀ j, 0 ≤ x.1 j) ∧ ∀ j, 0 ≤ x.2.1 j := by
    have hc : Continuous (fun ρ : ProbabilityMeasure (E L₀ L) =>
        ∫ x, negF (L₀ := L₀) (L := L) x ∂(ρ : Measure (E L₀ L))) :=
      ProbabilityMeasure.continuous_integral_boundedContinuousFunction
        (BoundedContinuousFunction.ofNormedAddCommGroup (negF (L₀ := L₀) (L := L))
          (continuous_negF (L₀ := L₀) (L := L)) _ (negF_le (L₀ := L₀) (L := L)))
    have h4 := mem_of_cluster hν (C := {ρ | ∫ x, negF x ∂(ρ : Measure (E L₀ L)) = 0})
      (isClosed_eq hc continuous_const)
      (Eventually.of_forall fun N => integral_eq_zero_of_ae
        ((U4 N).mono fun x hx => negF_zero_of x hx))
    have hi : Integrable (negF : E L₀ L → ℝ) (ν : Measure _) :=
      Integrable.of_bound continuous_negF.aestronglyMeasurable _ (ae_of_all _ negF_le)
    have hz := (integral_eq_zero_iff_of_nonneg (fun x => negF_nonneg x) hi).1 h4
    exact hz.mono fun x hx => nonneg_of_negF x hx
  -- W5
  have LI : ∀ g g' : E L₀ L → ℝ, Continuous g → Continuous g' →
      (∀ φ : ℝ →ᵇ ℝ, ∀ ε > 0, ∀ᶠ N in atTop,
        |∫ x, φ (g x) ∂(u N : Measure (E L₀ L)) - ∫ x, φ (g' x) ∂(u N : Measure (E L₀ L))| ≤ ε) →
      (ν : Measure (E L₀ L)).map g = (ν : Measure (E L₀ L)).map g' := by
    intro g g' hg hg' hA
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro φ
    rw [integral_map hg.measurable.aemeasurable φ.continuous.aestronglyMeasurable,
      integral_map hg'.measurable.aemeasurable φ.continuous.aestronglyMeasurable]
    apply eq_of_abs_le_all
    intro ε hε
    have hc1 : Continuous (fun ρ : ProbabilityMeasure (E L₀ L) => ∫ x, φ (g x) ∂(ρ : Measure _)) :=
      ProbabilityMeasure.continuous_integral_boundedContinuousFunction (φ.compContinuous ⟨g, hg⟩)
    have hc2 : Continuous (fun ρ : ProbabilityMeasure (E L₀ L) => ∫ x, φ (g' x) ∂(ρ : Measure _)) :=
      ProbabilityMeasure.continuous_integral_boundedContinuousFunction (φ.compContinuous ⟨g', hg'⟩)
    exact mem_of_cluster hν (C := {ρ | |∫ x, φ (g x) ∂(ρ : Measure (E L₀ L)) -
        ∫ x, φ (g' x) ∂(ρ : Measure (E L₀ L))| ≤ ε})
      (isClosed_le (continuous_abs.comp (hc1.sub hc2)) continuous_const) (hA φ ε hε)
  -- W6
  have W6 : ∀ (h : E L₀ L → ℝ), Continuous h →
      (∀ N, ∫⁻ x, ENNReal.ofReal |h x| ∂(u N : Measure (E L₀ L)) ≤ ENNReal.ofReal Mc) →
      ∫⁻ x, ENNReal.ofReal |h x| ∂(ν : Measure (E L₀ L)) ≠ ⊤ := by
    intro h hh hN
    have := mem_of_cluster hν (isClosed_lintegral_le (fun x => |h x|) hh.abs
      (fun x => abs_nonneg _) Mc hMc) (Eventually.of_forall hN)
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top this
  -- W7
  have W7 : ∫⁻ x, (ENNReal.ofReal (κ.c * qE0 x) + ENNReal.ofReal (G κ (stat0 x)))
      ∂(ν : Measure (E L₀ L)) ≤ OPT μ κ L₀ L := by
    rw [lintegral_congr fun x => (ofReal_Jh κ x).symm, hOPT]
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hε' : (0 : ℝ) < ε := hε
    have := mem_of_cluster hν (isClosed_lintegral_le (Jh κ) (continuous_Jh κ) (Jh_nonneg κ)
      (Or + ε) (by linarith)) (U7 ε hε')
    refine this.trans (le_of_eq ?_)
    first
      | rw [ENNReal.ofReal_add hOr (NNReal.coe_nonneg ε), ENNReal.ofReal_coe_nnreal]
      | simp [ENNReal.ofReal_add hOr]
  refine ⟨ν, inferInstance, witness_of μ κ hL (ν : Measure (E L₀ L)) W1 W2 W3 W4
    (fun i => LI _ _ (by fun_prop) (by fun_prop) (U5c i))
    (fun i => LI _ _ (by fun_prop) (by fun_prop) (U5q i))
    (fun k => LI _ _ (continuous_statF k) continuous_stat0 (U5s k))
    (fun j => W6 (fun x => x.1 j) (by fun_prop) (fun N => (U6 N).1 j))
    (fun j => W6 (fun x => x.2.1 j) (by fun_prop) (fun N => (U6 N).2.1 j))
    (W6 (fun x => x.2.2.1) (by fun_prop) (fun N => (U6 N).2.2)) W7⟩


/-! ## P6: moment and cost bounds for the Cesàro laws -/

lemma mp_fstS (μ : DemandLaw) : MeasurePreserving Prod.fst (sampleLaw μ) (pathLaw μ) :=
  ⟨measurable_fst, by unfold sampleLaw; rw [Measure.map_fst_prod, measure_univ, one_smul]⟩

lemma mp_sndS (μ : DemandLaw) :
    MeasurePreserving Prod.snd (sampleLaw μ) ((pathLaw μ).prod ghatLaw) :=
  ⟨measurable_snd, by unfold sampleLaw; rw [Measure.map_snd_prod, measure_univ, one_smul]⟩

lemma mp_evalP (μ : DemandLaw) (n : ℕ) :
    MeasurePreserving (fun p : Path => p n) (pathLaw μ) μ.law := by
  unfold pathLaw; exact measurePreserving_eval_infinitePi _ n

lemma lintegral_coord (μ : DemandLaw) (j : ℕ) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ ω, f (ω.1 j) ∂sampleLaw μ = ∫⁻ d, f d ∂μ.law :=
  ((mp_evalP μ j).comp (mp_fstS μ)).lintegral_comp hf

noncomputable def EDa (μ : DemandLaw) : ℝ≥0∞ := ∫⁻ d, ENNReal.ofReal |d| ∂μ.law

lemma EDa_ne_top (μ : DemandLaw) : EDa μ ≠ ⊤ :=
  (Integrable.lintegral_lt_top μ.integrable.abs).ne

lemma real_bound (i : ℕ) : (1 / 2 : ℝ) ^ (i + 1) * ((i : ℝ) + 1) ≤ (3 / 4) ^ i := by
  have h1 : ((i : ℝ) + 1) ≤ 2 * (3 / 2) ^ i := by
    induction i with
    | zero => norm_num
    | succ n ih =>
      have := one_le_pow₀ (show (1 : ℝ) ≤ 3 / 2 by norm_num) (n := n)
      push_cast; rw [pow_succ]; nlinarith
  calc (1 / 2 : ℝ) ^ (i + 1) * ((i : ℝ) + 1) ≤ (1 / 2) ^ (i + 1) * (2 * (3 / 2) ^ i) := by
        gcongr
    _ = (3 / 4) ^ i := by
        rw [pow_succ, show (3 / 4 : ℝ) = (1 / 2) * (3 / 2) by norm_num, mul_pow]; ring

lemma ghat_mean_ne_top : ∫⁻ k, (k : ℝ≥0∞) ∂ghatLaw ≠ ⊤ := by
  unfold ghatLaw
  rw [lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac]
  refine ne_top_of_le_ne_top (ENNReal.tsum_coe_ne_top_iff_summable.2
    (NNReal.summable_geometric (r := 3 / 4) (by norm_num))) (ENNReal.tsum_le_tsum fun i => ?_)
  rw [ENNReal.smul_def, smul_eq_mul, ← ENNReal.coe_natCast, ← ENNReal.coe_mul,
    ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
  push_cast
  exact real_bound i

noncomputable def I0 (μ : DemandLaw) : ℝ≥0∞ :=
  ∫⁻ ω, ∑ i ∈ Finset.range ω.2.2, ENNReal.ofReal |ω.2.1 i| ∂sampleLaw μ

lemma I0_ne_top (μ : DemandLaw) : I0 μ ≠ ⊤ := by
  have hq : Measurable (fun q : Path × ℕ => ∑ i ∈ Finset.range q.2, ENNReal.ofReal |q.1 i|) := by
    refine measurable_from_prod_countable_left fun k => ?_
    simp only
    exact Finset.measurable_sum _ fun i _ =>
      ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp (measurable_pi_apply i))
  have hc := (mp_sndS μ).lintegral_comp hq
  unfold I0
  rw [hc, lintegral_prod_symm _ hq.aemeasurable]
  have inner : ∀ k : ℕ, ∫⁻ x, ∑ i ∈ Finset.range k, ENNReal.ofReal |x i| ∂pathLaw μ =
      (k : ℝ≥0∞) * EDa μ := by
    intro k
    have hmi : ∀ i ∈ Finset.range k, Measurable (fun x : Path => ENNReal.ofReal |x i|) :=
      fun i _ => ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp (measurable_pi_apply i))
    rw [lintegral_finset_sum _ hmi]
    rw [Finset.sum_congr rfl fun i _ =>
      (mp_evalP μ i).lintegral_comp (f := fun d : ℝ => ENNReal.ofReal |d|)
        (ENNReal.measurable_ofReal.comp continuous_abs.measurable)]
    simp [EDa]
  simp only [inner]
  rw [lintegral_mul_const _ (Measurable.of_discrete)]
  exact ENNReal.mul_ne_top ghat_mean_ne_top (EDa_ne_top μ)

lemma IV_zero (π : AdmissiblePolicy L₀ L) (ω : Sample) :
    IV π ω 0 = -∑ i ∈ Finset.range ω.2.2, ω.2.1 i := by
  simp [IV, obsN, run, initState, expeditedPosition, observe]

/-- Partial sums of period costs. -/
noncomputable def Ssum (μ : DemandLaw) (κ : Costs) (π : AdmissiblePolicy L₀ L) (m : ℕ) : ℝ≥0∞ :=
  ∑ n ∈ Finset.range m, ∫⁻ ω, periodCost κ π ω (n + (L₀ + 1)) ∂sampleLaw μ

/-- The Cesàro averages whose `limsup` is `policyCost`. -/
noncomputable def Aavg (μ : DemandLaw) (κ : Costs) (π : AdmissiblePolicy L₀ L) (T : ℕ) : ℝ≥0∞ :=
  (∑ t ∈ Finset.Icc (L₀ + 1) T, ∫⁻ ω, periodCost κ π ω t ∂sampleLaw μ) / (T : ℝ≥0∞)

lemma Ssum_eq (μ : DemandLaw) (κ : Costs) (π : AdmissiblePolicy L₀ L) (m : ℕ) :
    Ssum μ κ π m = ∑ t ∈ Finset.Icc (L₀ + 1) (m + L₀), ∫⁻ ω, periodCost κ π ω t ∂sampleLaw μ := by
  have : Finset.Icc (L₀ + 1) (m + L₀) = Finset.Ico (L₀ + 1) (L₀ + 1 + m) := by
    ext t; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [this, Finset.sum_Ico_eq_sum_range, show L₀ + 1 + m - (L₀ + 1) = m by omega, Ssum]
  exact Finset.sum_congr rfl fun n _ => by rw [add_comm n]

lemma Ssum_le (μ : DemandLaw) (κ : Costs) (π : AdmissiblePolicy L₀ L) (B : ℝ≥0∞) (T0 : ℕ)
    (hB : ∀ T ≥ T0, Aavg μ κ π T ≤ B) (m : ℕ) (hm : T0 ≤ m + L₀) (hm1 : 1 ≤ m + L₀) :
    Ssum μ κ π m ≤ ((m + L₀ : ℕ) : ℝ≥0∞) * B := by
  rw [Ssum_eq]
  have h := hB (m + L₀) hm
  unfold Aavg at h
  have hne : ((m + L₀ : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show m + L₀ ≠ 0 by omega)
  rw [ENNReal.div_le_iff hne (ENNReal.natCast_ne_top _)] at h
  rw [mul_comm]; exact h

lemma Ssum_mono (μ : DemandLaw) (κ : Costs) (π : AdmissiblePolicy L₀ L) {a b : ℕ} (h : a ≤ b) :
    Ssum μ κ π a ≤ Ssum μ κ π b :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

lemma sum_shift_le (f : ℕ → ℝ≥0∞) (T j : ℕ) :
    ∑ n ∈ Finset.range T, f (n + j) ≤ ∑ n ∈ Finset.range (T + j), f n := by
  rw [add_comm T j, Finset.sum_range_add]
  have : ∑ n ∈ Finset.range T, f (n + j) = ∑ n ∈ Finset.range T, f (j + n) :=
    Finset.sum_congr rfl fun n _ => by rw [add_comm]
  rw [this]
  exact le_add_self

lemma inv_mul_add_le (T : ℕ) (hT : 1 ≤ T) (c : ℝ≥0∞) :
    (T : ℝ≥0∞)⁻¹ * ((T : ℝ≥0∞) + c) ≤ 1 + c := by
  have hT0 : (T : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show T ≠ 0 by omega)
  rw [mul_add, ENNReal.inv_mul_cancel hT0 (ENNReal.natCast_ne_top T)]
  gcongr
  calc (T : ℝ≥0∞)⁻¹ * c ≤ 1 * c := by
        gcongr
        exact ENNReal.inv_le_one.2 (by exact_mod_cast hT)
    _ = c := one_mul c

lemma pc_ge (hL : L₀ + 1 < L) (κ : Costs) (π : AdmissiblePolicy L₀ L) (ω : Sample) (n : ℕ) :
    ENNReal.ofReal (κ.c * ((act π ω n).2 : ℝ)) ≤ periodCost κ π ω (n + (L₀ + 1)) ∧
    ENNReal.ofReal (G κ (Zs π ω n)) ≤ periodCost κ π ω (n + (L₀ + 1)) := by
  rw [periodCost_eq hL]
  exact ⟨le_self_add, le_add_self⟩

lemma ofReal_le_inv_c (κ : Costs) (a : ℝ) (ha : 0 ≤ a) :
    ENNReal.ofReal a ≤ ENNReal.ofReal (1 / κ.c) * ENNReal.ofReal (κ.c * a) := by
  rw [← ENNReal.ofReal_mul (by have := κ.c_pos; positivity)]
  apply le_of_eq; congr 1; field_simp [κ.c_pos.ne']

/-- `K₁` bounds `|IV|` by the period cost. -/
noncomputable def K1 (κ : Costs) : ℝ≥0∞ := ENNReal.ofReal (1 / min κ.b κ.h) + ENNReal.ofReal (1 / κ.c)

lemma IV_pt (hL : L₀ + 1 < L) (κ : Costs) (π : AdmissiblePolicy L₀ L) (ω : Sample) (n : ℕ) :
    ENNReal.ofReal |IV π ω n| ≤ K1 κ * periodCost κ π ω (n + (L₀ + 1)) +
      ∑ i ∈ Finset.range (L₀ + 1), ENNReal.ofReal |ω.1 (n + i)| := by
  have hm : 0 < min κ.b κ.h := lt_min κ.b_pos κ.h_pos
  have ha : (0 : ℝ) ≤ (act π ω n).2 := (act π ω n).2.2
  have hZ : |Zs π ω n| ≤ (1 / min κ.b κ.h) * G κ (Zs π ω n) := by
    have := G_ge κ (Zs π ω n)
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hm]; linarith
  have hIV : |IV π ω n| ≤ (1 / min κ.b κ.h) * G κ (Zs π ω n) + ((act π ω n).2 : ℝ) +
      ∑ i ∈ Finset.range (L₀ + 1), |ω.1 (n + i)| := by
    have e : IV π ω n = Zs π ω n - (act π ω n).2 + ∑ i ∈ Finset.range (L₀ + 1), ω.1 (n + i) := by
      unfold Zs; ring
    rw [e]
    have := Finset.abs_sum_le_sum_abs (fun i => ω.1 (n + i)) (Finset.range (L₀ + 1))
    calc |Zs π ω n - (act π ω n).2 + ∑ i ∈ Finset.range (L₀ + 1), ω.1 (n + i)|
        ≤ |Zs π ω n| + |((act π ω n).2 : ℝ)| + |∑ i ∈ Finset.range (L₀ + 1), ω.1 (n + i)| := by
          have := abs_add_le (Zs π ω n - (act π ω n).2) (∑ i ∈ Finset.range (L₀ + 1), ω.1 (n + i))
          have := abs_sub (Zs π ω n) ((act π ω n).2 : ℝ)
          linarith
      _ ≤ _ := by rw [abs_of_nonneg ha]; linarith
  obtain ⟨p1, p2⟩ := pc_ge hL κ π ω n
  calc ENNReal.ofReal |IV π ω n|
      ≤ ENNReal.ofReal ((1 / min κ.b κ.h) * G κ (Zs π ω n)) + ENNReal.ofReal ((act π ω n).2 : ℝ) +
        ∑ i ∈ Finset.range (L₀ + 1), ENNReal.ofReal |ω.1 (n + i)| := by
        refine (ENNReal.ofReal_le_ofReal hIV).trans ?_
        rw [ENNReal.ofReal_add (by have := G_nonneg κ (Zs π ω n); positivity)
          (Finset.sum_nonneg fun i _ => abs_nonneg _),
          ENNReal.ofReal_add (by have := G_nonneg κ (Zs π ω n); positivity) ha,
          ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
    _ ≤ (ENNReal.ofReal (1 / min κ.b κ.h) * periodCost κ π ω (n + (L₀ + 1)) +
          ENNReal.ofReal (1 / κ.c) * periodCost κ π ω (n + (L₀ + 1))) +
        ∑ i ∈ Finset.range (L₀ + 1), ENNReal.ofReal |ω.1 (n + i)| := by
        gcongr
        · rw [ENNReal.ofReal_mul (by positivity)]; gcongr
        · exact (ofReal_le_inv_c κ _ ha).trans (by gcongr)
    _ = _ := by rw [K1, add_mul]

lemma lint_IV (hL : L₀ + 1 < L) (μ : DemandLaw) (κ : Costs) (π : AdmissiblePolicy L₀ L) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal |IV π ω n| ∂sampleLaw μ ≤
      K1 κ * ∫⁻ ω, periodCost κ π ω (n + (L₀ + 1)) ∂sampleLaw μ + ((L₀ + 1 : ℕ) : ℝ≥0∞) * EDa μ := by
  have hpc : Measurable (fun ω => periodCost κ π ω (n + (L₀ + 1))) := by
    unfold periodCost
    have := measurable_run π (n + (L₀ + 1))
    have hG := continuous_G κ
    fun_prop
  calc ∫⁻ ω, ENNReal.ofReal |IV π ω n| ∂sampleLaw μ
      ≤ ∫⁻ ω, (K1 κ * periodCost κ π ω (n + (L₀ + 1)) +
          ∑ i ∈ Finset.range (L₀ + 1), ENNReal.ofReal |ω.1 (n + i)|) ∂sampleLaw μ :=
        lintegral_mono fun ω => IV_pt hL κ π ω n
    _ = K1 κ * ∫⁻ ω, periodCost κ π ω (n + (L₀ + 1)) ∂sampleLaw μ +
          ∑ i ∈ Finset.range (L₀ + 1), ∫⁻ ω, ENNReal.ofReal |ω.1 (n + i)| ∂sampleLaw μ := by
        have hmi : ∀ i ∈ Finset.range (L₀ + 1),
            Measurable (fun ω : Sample => ENNReal.ofReal |ω.1 (n + i)|) := fun i _ =>
          ENNReal.measurable_ofReal.comp
            (continuous_abs.measurable.comp ((measurable_pi_apply _).comp measurable_fst))
        rw [lintegral_add_left (hpc.const_mul _), lintegral_const_mul _ hpc,
          lintegral_finset_sum _ hmi]
    _ = _ := by
        congr 1
        rw [Finset.sum_congr rfl fun i _ => lintegral_coord μ (n + i) (fun d => ENNReal.ofReal |d|)
          (ENNReal.measurable_ofReal.comp continuous_abs.measurable)]
        simp [EDa]


/-! ## P7: bounds for the Cesàro laws and assembly -/

lemma measurable_pc (κ : Costs) (π : AdmissiblePolicy L₀ L) (t : ℕ) :
    Measurable (fun ω => periodCost κ π ω t) := by
  unfold periodCost
  have := measurable_run π t
  have hG := continuous_G κ
  fun_prop

lemma chi_tel (hL : L₀ + 1 < L) (π : AdmissiblePolicy L₀ L) (ω : Sample) (m : ℕ) :
    ∑ n ∈ Finset.range m, chiF π ω n 0 = IV π ω m - IV π ω 0 -
      ∑ n ∈ Finset.range m, ((act π ω n).2 : ℝ) + ∑ n ∈ Finset.range m, ω.1 n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, iv_succ hL, Finset.sum_range_succ, Finset.sum_range_succ]
    ring

lemma chi_pt (hL : L₀ + 1 < L) (π : AdmissiblePolicy L₀ L) (ω : Sample) (m : ℕ) :
    ∑ n ∈ Finset.range m, ENNReal.ofReal (chiF π ω n 0) ≤ ENNReal.ofReal |IV π ω m| +
      ∑ i ∈ Finset.range ω.2.2, ENNReal.ofReal |ω.2.1 i| +
      ∑ n ∈ Finset.range m, ENNReal.ofReal |ω.1 n| := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => chiF_nonneg π ω n 0),
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _),
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _),
    ← ENNReal.ofReal_add (abs_nonneg _) (Finset.sum_nonneg fun i _ => abs_nonneg _),
    ← ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun i _ => abs_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  rw [chi_tel hL]
  have h0 : -IV π ω 0 ≤ ∑ i ∈ Finset.range ω.2.2, |ω.2.1 i| := by
    rw [IV_zero, neg_neg]
    exact Finset.sum_le_sum fun i _ => le_abs_self _
  have h1 : 0 ≤ ∑ n ∈ Finset.range m, ((act π ω n).2 : ℝ) :=
    Finset.sum_nonneg fun n _ => (act π ω n).2.2
  have h2 : ∑ n ∈ Finset.range m, ω.1 n ≤ ∑ n ∈ Finset.range m, |ω.1 n| :=
    Finset.sum_le_sum fun n _ => le_abs_self _
  have h3 := le_abs_self (IV π ω m)
  linarith

lemma aux2 (T : ℕ) (hT : 1 ≤ T) (a c B : ℝ≥0∞) :
    (T : ℝ≥0∞)⁻¹ * (a * (((T : ℝ≥0∞) + c) * B)) ≤ a * ((1 + c) * B) := by
  rw [mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ bot_le
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (inv_mul_add_le T hT c) bot_le

lemma aux1 (T : ℕ) (hT : 1 ≤ T) (x : ℝ≥0∞) : (T : ℝ≥0∞)⁻¹ * x ≤ x := by
  have hinv : (T : ℝ≥0∞)⁻¹ ≤ 1 := ENNReal.inv_le_one.2 (by exact_mod_cast hT)
  calc (T : ℝ≥0∞)⁻¹ * x ≤ 1 * x := mul_le_mul_of_nonneg_right hinv bot_le
    _ = x := one_mul x

/-- The three moment bounds for `nuT`. -/
lemma nuT_moments (hL : L₀ + 1 < L) (μ : DemandLaw) (κ : Costs) (π : AdmissiblePolicy L₀ L)
    (B : ℝ≥0∞) (T0 : ℕ) (hB : ∀ T ≥ T0, Aavg μ κ π T ≤ B) (T : ℕ) (hT0 : T0 ≤ T) (hT : 1 ≤ T) :
    (∀ j : Fin (L - L₀), ∫⁻ x, ENNReal.ofReal |x.2.1 j| ∂nuT μ π T ≤
        ENNReal.ofReal (1 / κ.c) * ((1 + L) * B)) ∧
    ∫⁻ x, ENNReal.ofReal |x.2.2.1| ∂nuT μ π T ≤
        K1 κ * ((1 + L) * B) + ((L₀ + 1 : ℕ) : ℝ≥0∞) * EDa μ ∧
    (∀ j : Fin (L - L₀ - 1), ∫⁻ x, ENNReal.ofReal |x.1 j| ∂nuT μ π T ≤
        K1 κ * ((1 + L) * B) + ((L₀ + 1 : ℕ) : ℝ≥0∞) * EDa μ + I0 μ + (1 + L) * EDa μ) := by
  have hTr : ((T : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show T ≠ 0 by omega)
  have hSL : ∀ m, m + L₀ ≤ T + L → T0 ≤ m + L₀ → 1 ≤ m + L₀ →
      Ssum μ κ π m ≤ ((T : ℝ≥0∞) + L) * B := by
    intro m hm h1 h2
    refine (Ssum_le μ κ π B T0 hB m h1 h2).trans ?_
    gcongr
    exact_mod_cast hm
  have hfin : ∀ (a : ℝ≥0∞), (T : ℝ≥0∞)⁻¹ * (((T : ℝ≥0∞) + L) * a) ≤ (1 + L) * a := by
    intro a
    rw [← mul_assoc]; gcongr; exact inv_mul_add_le T hT _
  refine ⟨fun j => ?_, ?_, fun j => ?_⟩
  · -- expedite coordinates
    have hj := j.isLt
    rw [lintegral_nuT μ π T (fun x => ENNReal.ofReal |x.2.1 j|) (by fun_prop)]
    have hterm : ∀ n, ∫⁻ ω, ENNReal.ofReal |(V π n ω).2.1 j| ∂sampleLaw μ ≤
        ENNReal.ofReal (1 / κ.c) * ∫⁻ ω, periodCost κ π ω ((n + j) + (L₀ + 1)) ∂sampleLaw μ := by
      intro n
      rw [← lintegral_const_mul _ (measurable_pc κ π _)]
      refine lintegral_mono fun ω => ?_
      have ha : (0 : ℝ) ≤ (act π ω (n + j)).2 := (act π ω (n + j)).2.2
      show ENNReal.ofReal |((act π ω (n + j)).2 : ℝ)| ≤ _
      rw [abs_of_nonneg ha]
      exact (ofReal_le_inv_c κ _ ha).trans (by gcongr; exact (pc_ge hL κ π ω (n + j)).1)
    calc (T : ℝ≥0∞)⁻¹ * ∑ n ∈ Finset.range T, ∫⁻ ω, ENNReal.ofReal |(V π n ω).2.1 j| ∂sampleLaw μ
        ≤ (T : ℝ≥0∞)⁻¹ * (ENNReal.ofReal (1 / κ.c) *
            ∑ n ∈ Finset.range T, ∫⁻ ω, periodCost κ π ω ((n + j) + (L₀ + 1)) ∂sampleLaw μ) := by
          gcongr; rw [Finset.mul_sum]; exact Finset.sum_le_sum fun n _ => hterm n
      _ ≤ (T : ℝ≥0∞)⁻¹ * (ENNReal.ofReal (1 / κ.c) * Ssum μ κ π (T + j)) := by
          gcongr
          exact sum_shift_le (fun n => ∫⁻ ω, periodCost κ π ω (n + (L₀ + 1)) ∂sampleLaw μ) T j
      _ ≤ (T : ℝ≥0∞)⁻¹ * (ENNReal.ofReal (1 / κ.c) * (((T : ℝ≥0∞) + L) * B)) := by
          gcongr; exact hSL _ (by omega) (by omega) (by omega)
      _ ≤ ENNReal.ofReal (1 / κ.c) * ((1 + L) * B) := aux2 T hT _ _ _
  · -- inventory coordinate
    rw [lintegral_nuT μ π T (fun x => ENNReal.ofReal |x.2.2.1|) (by fun_prop)]
    calc (T : ℝ≥0∞)⁻¹ * ∑ n ∈ Finset.range T, ∫⁻ ω, ENNReal.ofReal |(V π n ω).2.2.1| ∂sampleLaw μ
        ≤ (T : ℝ≥0∞)⁻¹ * ∑ n ∈ Finset.range T, (K1 κ *
            ∫⁻ ω, periodCost κ π ω (n + (L₀ + 1)) ∂sampleLaw μ + ((L₀ + 1 : ℕ) : ℝ≥0∞) * EDa μ) := by
          gcongr with n hn; exact lint_IV hL μ κ π n
      _ = (T : ℝ≥0∞)⁻¹ * (K1 κ * Ssum μ κ π T) + ((L₀ + 1 : ℕ) : ℝ≥0∞) * EDa μ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul, mul_add, ← mul_assoc ((T : ℝ≥0∞)⁻¹) (T : ℝ≥0∞),
            ENNReal.inv_mul_cancel hTr (ENNReal.natCast_ne_top T), one_mul, Ssum]
      _ ≤ (T : ℝ≥0∞)⁻¹ * (K1 κ * (((T : ℝ≥0∞) + L) * B)) + ((L₀ + 1 : ℕ) : ℝ≥0∞) * EDa μ := by
          gcongr; exact hSL _ (by omega) (by omega) (by omega)
      _ ≤ K1 κ * ((1 + L) * B) + ((L₀ + 1 : ℕ) : ℝ≥0∞) * EDa μ :=
          add_le_add_left (aux2 T hT _ _ _) _
  · -- regular pipeline coordinates
    have hj := j.isLt
    rw [lintegral_nuT μ π T (fun x => ENNReal.ofReal |x.1 j|) (by fun_prop)]
    have hterm : ∀ n, ∫⁻ ω, ENNReal.ofReal |(V π n ω).1 j| ∂sampleLaw μ =
        ∫⁻ ω, ENNReal.ofReal (chiF π ω (n + j) 0) ∂sampleLaw μ := by
      intro n
      refine lintegral_congr fun ω => ?_
      have e1 : (V π n ω).1 j = chiF π ω n j := by
        simp only [V, chiF, dif_pos hj]
      rw [e1, abs_of_nonneg (chiF_nonneg π ω n j), chi_shift π ω n j hj]
    have hmeas : ∀ n, Measurable (fun ω => ENNReal.ofReal (chiF π ω n 0)) := by
      intro n
      have h0 : 0 < L - L₀ - 1 := by omega
      simp only [chiF, dif_pos h0]
      exact ENNReal.measurable_ofReal.comp ((measurable_pi_apply _).comp (measurable_chiV π n))
    have hpt := fun ω => chi_pt hL π ω (T + j)
    have hint : ∑ n ∈ Finset.range (T + j), ∫⁻ ω, ENNReal.ofReal (chiF π ω n 0) ∂sampleLaw μ ≤
        (K1 κ * Ssum μ κ π (T + j + 1) + ((L₀ + 1 : ℕ) : ℝ≥0∞) * EDa μ) + I0 μ +
          ((T + j : ℕ) : ℝ≥0∞) * EDa μ := by
      have hmi : ∀ n ∈ Finset.range (T + j), Measurable (fun ω => ENNReal.ofReal (chiF π ω n 0)) :=
        fun n _ => hmeas n
      rw [← lintegral_finset_sum _ hmi]
      have hmI : Measurable (fun ω => ENNReal.ofReal |IV π ω (T + j)|) :=
        ENNReal.measurable_ofReal.comp (measurable_IV π _).abs
      have hmG : Measurable (fun ω : Sample => ∑ i ∈ Finset.range ω.2.2, ENNReal.ofReal |ω.2.1 i|) := by
        have hq : Measurable (fun q : Path × ℕ => ∑ i ∈ Finset.range q.2, ENNReal.ofReal |q.1 i|) := by
          refine measurable_from_prod_countable_left fun k => ?_
          simp only
          exact Finset.measurable_sum _ fun i _ =>
            ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp (measurable_pi_apply i))
        exact hq.comp measurable_snd
      have hmD : ∀ n ∈ Finset.range (T + j), Measurable (fun ω : Sample => ENNReal.ofReal |ω.1 n|) :=
        fun n _ => ENNReal.measurable_ofReal.comp
          (continuous_abs.measurable.comp ((measurable_pi_apply _).comp measurable_fst))
      calc ∫⁻ ω, ∑ n ∈ Finset.range (T + j), ENNReal.ofReal (chiF π ω n 0) ∂sampleLaw μ
          ≤ ∫⁻ ω, (ENNReal.ofReal |IV π ω (T + j)| +
              ∑ i ∈ Finset.range ω.2.2, ENNReal.ofReal |ω.2.1 i| +
              ∑ n ∈ Finset.range (T + j), ENNReal.ofReal |ω.1 n|) ∂sampleLaw μ :=
            lintegral_mono hpt
        _ = ∫⁻ ω, ENNReal.ofReal |IV π ω (T + j)| ∂sampleLaw μ + I0 μ +
              ∑ n ∈ Finset.range (T + j), ∫⁻ ω, ENNReal.ofReal |ω.1 n| ∂sampleLaw μ := by
            have hmIG : Measurable (fun ω : Sample => ENNReal.ofReal |IV π ω (T + j)| +
                ∑ i ∈ Finset.range ω.2.2, ENNReal.ofReal |ω.2.1 i|) := hmI.add hmG
            rw [lintegral_add_left hmIG, lintegral_add_left hmI,
              lintegral_finset_sum _ hmD, I0]
        _ ≤ (K1 κ * Ssum μ κ π (T + j + 1) + ((L₀ + 1 : ℕ) : ℝ≥0∞) * EDa μ) + I0 μ +
              ((T + j : ℕ) : ℝ≥0∞) * EDa μ := by
            gcongr
            · refine (lint_IV hL μ κ π (T + j)).trans ?_
              gcongr
              rw [Ssum, Finset.sum_range_succ]
              exact le_add_self
            · rw [Finset.sum_congr rfl fun n _ => lintegral_coord μ n (fun d => ENNReal.ofReal |d|)
                (ENNReal.measurable_ofReal.comp continuous_abs.measurable)]
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              rfl
    have hS : Ssum μ κ π (T + j + 1) ≤ ((T : ℝ≥0∞) + L) * B := hSL _ (by omega) (by omega) (by omega)
    have hTj : ((T + j : ℕ) : ℝ≥0∞) ≤ (T : ℝ≥0∞) + L := by
      push_cast; gcongr; exact_mod_cast (show (j : ℕ) ≤ L by omega)
    simp only [hterm]
    calc (T : ℝ≥0∞)⁻¹ * ∑ n ∈ Finset.range T, ∫⁻ ω, ENNReal.ofReal (chiF π ω (n + j) 0) ∂sampleLaw μ
        ≤ (T : ℝ≥0∞)⁻¹ * ∑ n ∈ Finset.range (T + j), ∫⁻ ω, ENNReal.ofReal (chiF π ω n 0) ∂sampleLaw μ := by
          gcongr
          exact sum_shift_le (fun n => ∫⁻ ω, ENNReal.ofReal (chiF π ω n 0) ∂sampleLaw μ) T j
      _ ≤ (T : ℝ≥0∞)⁻¹ * ((K1 κ * (((T : ℝ≥0∞) + L) * B) + ((L₀ + 1 : ℕ) : ℝ≥0∞) * EDa μ) + I0 μ +
              ((T : ℝ≥0∞) + L) * EDa μ) := by
          gcongr
          exact hint.trans (by gcongr)
      _ ≤ K1 κ * ((1 + L) * B) + ((L₀ + 1 : ℕ) : ℝ≥0∞) * EDa μ + I0 μ + (1 + L) * EDa μ := by
          rw [mul_add, mul_add, mul_add]
          exact add_le_add (add_le_add (add_le_add (aux2 T hT _ _ _) (aux1 T hT _))
            (aux1 T hT _)) (hfin _)


/-! ## P8: choosing near-optimal policies and assembling the witness -/

lemma choose_policy (μ : DemandLaw) (κ : Costs) (hfin : OPT μ κ L₀ L ≠ ⊤) (δ : ℝ≥0∞)
    (hδ : δ ≠ 0) :
    ∃ π : AdmissiblePolicy L₀ L, ∃ T0 : ℕ, ∀ T ≥ T0, Aavg μ κ π T ≤ OPT μ κ L₀ L + δ := by
  have h1 : OPT μ κ L₀ L < OPT μ κ L₀ L + δ := ENNReal.lt_add_right hfin hδ
  have h1' : (⨅ π : AdmissiblePolicy L₀ L, policyCost μ κ π) < OPT μ κ L₀ L + δ := h1
  obtain ⟨π, hπ⟩ := iInf_lt_iff.1 h1'
  unfold policyCost at hπ
  have h2 := Filter.eventually_lt_of_limsup_lt hπ
  obtain ⟨T0, hT0⟩ := eventually_atTop.1 h2
  exact ⟨π, T0, fun T hT => (hT0 T hT).le⟩

lemma nuT_nonneg (μ : DemandLaw) (π : AdmissiblePolicy L₀ L) (T : ℕ) :
    ∀ᵐ x ∂nuT μ π T, (∀ j, 0 ≤ x.1 j) ∧ ∀ j, 0 ≤ x.2.1 j := by
  have hK : MeasurableSet {x : E L₀ L | (∀ j, 0 ≤ x.1 j) ∧ ∀ j, 0 ≤ x.2.1 j} := by
    simp only [Set.setOf_and, Set.setOf_forall]
    exact (MeasurableSet.iInter fun j => measurableSet_le measurable_const (by fun_prop)).inter
      (MeasurableSet.iInter fun j => measurableSet_le measurable_const (by fun_prop))
  rw [ae_iff]
  have : {x : E L₀ L | ¬((∀ j, 0 ≤ x.1 j) ∧ ∀ j, 0 ≤ x.2.1 j)} =
      {x : E L₀ L | (∀ j, 0 ≤ x.1 j) ∧ ∀ j, 0 ≤ x.2.1 j}ᶜ := rfl
  rw [this, nuT_apply μ π T _ hK.compl]
  have hz : ∀ n, sampleLaw μ (V π n ⁻¹' {x : E L₀ L | (∀ j, 0 ≤ x.1 j) ∧ ∀ j, 0 ≤ x.2.1 j}ᶜ) = 0 := by
    intro n
    have : V π n ⁻¹' {x : E L₀ L | (∀ j, 0 ≤ x.1 j) ∧ ∀ j, 0 ≤ x.2.1 j}ᶜ = ∅ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
        iff_false, not_not]
      refine ⟨fun j => ?_, fun j => (act π ω (n + j)).2.2⟩
      have h := chiF_nonneg π ω n j
      simp only [chiF, dif_pos j.isLt] at h
      exact h
    rw [this, measure_empty]
  rw [Finset.sum_eq_zero fun n _ => hz n, mul_zero]

lemma rel_chi (hL : L₀ + 1 < L) (π : AdmissiblePolicy L₀ L) (i : Fin (L - L₀ - 1)) (n : ℕ)
    (ω : Sample) : (V π n ω).1 i = (V π (n + i) ω).1 ⟨0, by omega⟩ := by
  have h := chi_shift π ω n i i.isLt
  have h0 : 0 < L - L₀ - 1 := by omega
  simp only [chiF, dif_pos h0, dif_pos i.isLt] at h
  exact h.symm

lemma rel_stat (hL : L₀ + 1 < L) (π : AdmissiblePolicy L₀ L) (k : Fin (L - L₀)) (n : ℕ)
    (ω : Sample) : statF k (V π n ω) = stat0 (V π (n + k) ω) := by
  have h0 : 0 < L - L₀ := by omega
  have e1 : ∀ i ∈ Finset.range k.val,
      qN L₀ L (fun y : E L₀ L => y.2.1) (V π n ω) i + chiN L₀ L (fun y : E L₀ L => y.1) (V π n ω) i -
        (V π n ω).2.2.2 i = ((act π ω (n + i)).2 : ℝ) + chiF π ω n i - ω.1 (n + i) := by
    intro i hi
    have := Finset.mem_range.1 hi
    simp only [qN, dif_pos (show i < L - L₀ by omega)]
    rfl
  have e2 : qN L₀ L (fun y : E L₀ L => y.2.1) (V π (n + k) ω) 0 = ((act π ω (n + k)).2 : ℝ) := by
    simp only [qN, dif_pos h0]
    rfl
  unfold statF stat0
  rw [Finset.sum_congr rfl e1, e2]
  exact stat_path hL π ω n k k.isLt

lemma Jh_V (hL : L₀ + 1 < L) (κ : Costs) (π : AdmissiblePolicy L₀ L) (n : ℕ) (ω : Sample) :
    ENNReal.ofReal (Jh κ (V π n ω)) = periodCost κ π ω (n + (L₀ + 1)) := by
  have h0 : 0 < L - L₀ := by omega
  have e : qN L₀ L (fun y : E L₀ L => y.2.1) (V π n ω) 0 = ((act π ω n).2 : ℝ) := by
    simp only [qN, dif_pos h0]
    rfl
  rw [ofReal_Jh, periodCost_eq hL]
  unfold qE0 stat0
  rw [e]
  rfl

lemma U7_alg (O δ : ℝ≥0∞) (hδ : δ ≤ 1) : (1 + δ) * (O + δ) ≤ O + δ * (O + 2) := by
  calc (1 + δ) * (O + δ) = O + δ * (1 + O + δ) := by ring
    _ ≤ O + δ * (1 + O + 1) := by gcongr
    _ = O + δ * (O + 2) := by ring

set_option maxHeartbeats 2000000 in
theorem main_of_fin (μ : DemandLaw) (κ : Costs) (hL : L₀ + 1 < L) (hfin : OPT μ κ L₀ L ≠ ⊤) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (χ : Ω → Fin (L - L₀ - 1) → ℝ) (q : Ω → Fin (L - L₀) → ℝ) (I : Ω → ℝ) (D : ℕ → Ω → ℝ),
      IsStationaryWitness P μ κ L₀ L χ q I D := by
  set δ : ℕ → ℝ≥0∞ := fun N => ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ with hδdef
  have hδ0 : ∀ N, δ N ≠ 0 := fun N => ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)
  have hδ1 : ∀ N, δ N ≤ 1 := fun N =>
    ENNReal.inv_le_one.2 (by exact_mod_cast Nat.succ_pos N)
  choose π T0 hπ using fun N => choose_policy μ κ hfin (δ N) (hδ0 N)
  set T : ℕ → ℕ := fun N => T0 N + (L₀ + 1) * (N + 1) with hTdef
  have hT1 : ∀ N, 1 ≤ T N := fun N => by simp only [hTdef]; nlinarith
  have hTpos : ∀ N, 0 < T N := fun N => hT1 N
  have hTN : ∀ N, N + 1 ≤ T N := fun N => by simp only [hTdef]; nlinarith
  have hTL : ∀ N, L₀ * (N + 1) ≤ T N := fun N => by simp only [hTdef]; nlinarith
  have hT0le : ∀ N, T0 N ≤ T N := fun N => by simp only [hTdef]; omega
  let u : ℕ → ProbabilityMeasure (E L₀ L) := fun N =>
    ⟨nuT μ (π N) (T N), nuT_isProb μ (π N) (T N) (hTpos N)⟩
  set B : ℝ≥0∞ := OPT μ κ L₀ L + 1 with hBdef
  have hB : ∀ N, ∀ T' ≥ T0 N, Aavg μ κ (π N) T' ≤ B := fun N T' hT' =>
    (hπ N T' hT').trans (by rw [hBdef]; exact add_le_add (le_refl _) (hδ1 N))
  have hBt : B ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hfin, ENNReal.one_ne_top⟩
  set Mbig : ℝ≥0∞ := ENNReal.ofReal (1 / κ.c) * ((1 + L) * B) +
    (K1 κ * ((1 + L) * B) + ((L₀ + 1 : ℕ) : ℝ≥0∞) * EDa μ + I0 μ + (1 + L) * EDa μ) with hMdef
  have hLt : (1 + (L : ℝ≥0∞)) ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.natCast_ne_top _⟩
  have hK1 : K1 κ ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  have hMbig : Mbig ≠ ⊤ := by
    have h1 : (1 + (L : ℝ≥0∞)) * B ≠ ⊤ := ENNReal.mul_ne_top hLt hBt
    refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top h1, ?_⟩
    refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top hK1 h1, ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (EDa_ne_top μ)⟩,
      I0_ne_top μ⟩, ENNReal.mul_ne_top hLt (EDa_ne_top μ)⟩
  set Oval : ℝ := (OPT μ κ L₀ L).toReal with hOval
  have hOPT : OPT μ κ L₀ L = ENNReal.ofReal Oval := (ENNReal.ofReal_toReal hfin).symm
  have hO0 : 0 ≤ Oval := ENNReal.toReal_nonneg
  have hMeq : ENNReal.ofReal Mbig.toReal = Mbig := ENNReal.ofReal_toReal hMbig
  -- the defect bound becomes small
  have hsmall : ∀ (k : ℕ) (φ : ℝ →ᵇ ℝ) (ε : ℝ), 0 < ε →
      ∀ᶠ N in atTop, 2 * (k : ℝ) * ‖φ‖ / (T N : ℝ) ≤ ε := by
    intro k φ ε hε
    obtain ⟨N0, hN0⟩ := exists_nat_gt (2 * (k : ℝ) * ‖φ‖ / ε)
    filter_upwards [eventually_ge_atTop N0] with N hN
    have hTr : (0 : ℝ) < T N := by exact_mod_cast hTpos N
    rw [div_le_iff₀ hTr]
    have h1 : 2 * (k : ℝ) * ‖φ‖ / ε < T N := by
      calc 2 * (k : ℝ) * ‖φ‖ / ε < N0 := hN0
        _ ≤ N := by exact_mod_cast hN
        _ ≤ T N := by exact_mod_cast (show N ≤ T N by have := hTN N; omega)
    rw [div_lt_iff₀ hε] at h1
    linarith
  obtain ⟨ν, -, hw⟩ := witness_of_seq μ κ hL u Oval hO0 hOPT Mbig.toReal ENNReal.toReal_nonneg
    (fun N => nuT_path μ (π N) (T N) (hTpos N))
    (fun N => nuT_indep_chiI μ (π N) (T N) (hTpos N))
    (fun N k => nuT_indep_q μ (π N) (T N) (hTpos N) k)
    (fun N => nuT_nonneg μ (π N) (T N))
    (fun i φ ε hε => (hsmall i φ ε hε).mono fun N hN =>
      (defect μ (π N) (T N) (hTpos N) (fun x => x.1 i) (fun x => x.1 ⟨0, by omega⟩)
        (by fun_prop) (by fun_prop) i (fun n ω => rel_chi hL (π N) i n ω) φ).trans hN)
    (fun i φ ε hε => (hsmall i φ ε hε).mono fun N hN =>
      (defect μ (π N) (T N) (hTpos N) (fun x => x.2.1 i) (fun x => x.2.1 ⟨0, by omega⟩)
        (by fun_prop) (by fun_prop) i (fun n ω => rfl) φ).trans hN)
    (fun k φ ε hε => (hsmall k φ ε hε).mono fun N hN =>
      (defect μ (π N) (T N) (hTpos N) (statF k) stat0
        (continuous_statF k).measurable continuous_stat0.measurable k
        (fun n ω => rel_stat hL (π N) k n ω) φ).trans hN)
    (fun N => by
      obtain ⟨m1, m2, m3⟩ := nuT_moments hL μ κ (π N) B (T0 N) (hB N) (T N) (hT0le N) (hT1 N)
      rw [hMeq]
      refine ⟨fun j => (m3 j).trans le_add_self, fun j => (m1 j).trans le_self_add,
        m2.trans ?_⟩
      exact le_self_add.trans (le_self_add.trans le_add_self))
    (fun ε hε => by
      have ht : Tendsto (fun N => δ N * (OPT μ κ L₀ L + 2)) atTop (𝓝 0) := by
        have h1 : Tendsto δ atTop (𝓝 0) :=
          ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
        have h2 : OPT μ κ L₀ L + 2 ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hfin, ENNReal.ofNat_ne_top⟩
        have := ENNReal.Tendsto.mul_const h1 (Or.inr h2)
        simpa using this
      filter_upwards [(tendsto_order.1 ht).2 (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)]
        with N hN
      have hTr : ((T N : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (hTpos N).ne'
      have hJ : ∫⁻ x, ENNReal.ofReal (Jh κ x) ∂(u N : Measure (E L₀ L)) =
          ((T N : ℕ) : ℝ≥0∞)⁻¹ * Ssum μ κ (π N) (T N) := by
        show ∫⁻ x, ENNReal.ofReal (Jh κ x) ∂nuT μ (π N) (T N) = _
        have hmJ : Measurable (fun x : E L₀ L => ENNReal.ofReal (Jh κ x)) :=
          ENNReal.measurable_ofReal.comp (continuous_Jh κ).measurable
        rw [lintegral_nuT μ (π N) (T N) (fun x => ENNReal.ofReal (Jh κ x)) hmJ, Ssum]
        congr 1
        refine Finset.sum_congr rfl fun n _ => lintegral_congr fun ω => Jh_V hL κ (π N) n ω
      have hfrac : ((T N : ℕ) : ℝ≥0∞)⁻¹ * (((T N + L₀ : ℕ) : ℝ≥0∞)) ≤ 1 + δ N := by
        push_cast
        rw [mul_add, ENNReal.inv_mul_cancel hTr (ENNReal.natCast_ne_top _)]
        gcongr
        rw [hδdef]
        simp only
        rw [ENNReal.le_inv_iff_mul_le]
        calc ((T N : ℕ) : ℝ≥0∞)⁻¹ * (L₀ : ℝ≥0∞) * ((N + 1 : ℕ) : ℝ≥0∞)
            = ((T N : ℕ) : ℝ≥0∞)⁻¹ * ((L₀ * (N + 1) : ℕ) : ℝ≥0∞) := by push_cast; ring
          _ ≤ ((T N : ℕ) : ℝ≥0∞)⁻¹ * ((T N : ℕ) : ℝ≥0∞) := by gcongr; exact_mod_cast hTL N
          _ = 1 := ENNReal.inv_mul_cancel hTr (ENNReal.natCast_ne_top _)
      rw [hJ]
      calc ((T N : ℕ) : ℝ≥0∞)⁻¹ * Ssum μ κ (π N) (T N)
          ≤ ((T N : ℕ) : ℝ≥0∞)⁻¹ * (((T N + L₀ : ℕ) : ℝ≥0∞) * (OPT μ κ L₀ L + δ N)) := by
            gcongr
            exact Ssum_le μ κ (π N) _ (T0 N) (hπ N) (T N) (by have := hT0le N; omega)
              (by have := hT1 N; omega)
        _ ≤ (1 + δ N) * (OPT μ κ L₀ L + δ N) := by rw [← mul_assoc]; gcongr
        _ ≤ OPT μ κ L₀ L + δ N * (OPT μ κ L₀ L + 2) := U7_alg _ _ (hδ1 N)
        _ ≤ OPT μ κ L₀ L + ENNReal.ofReal ε := add_le_add (le_refl _) hN.le
        _ = ENNReal.ofReal (Oval + ε) := by rw [hOPT, ENNReal.ofReal_add hO0 hε.le])
  exact ⟨E L₀ L, inferInstance, ν, _, _, _, _, hw⟩

end XGSW


open MeasureTheory ProbabilityTheory Filter XinGoldbergTBS.Asymptotic in
theorem solution (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) (hL : L₀ + 1 < L) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (χ : Ω → Fin (L - L₀ - 1) → ℝ) (q : Ω → Fin (L - L₀) → ℝ) (I : Ω → ℝ) (D : ℕ → Ω → ℝ),
      IsStationaryWitness P μ κ L₀ L χ q I D := by
  have h1 := XGOB.tbs00 μ κ L₀ L
  have hfin : OPT μ κ L₀ L ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := tbsCost μ κ L₀ L 0 0) ?_ (iInf_le _ (tbsPolicy L₀ L 0 0))
    rw [h1]; exact ENNReal.ofReal_ne_top
  exact XGSW.main_of_fin μ κ hL hfin
