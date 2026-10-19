-- Prove2me | solution 1 for XinGoldbergTBS.Asymptotic.opt_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-17T08:33:43.73334+00:00
-- url     : https://prove2.me/submissions/8b194a6b-5d0c-48c7-8aa9-e52095d6f691

import Mathlib
import Definitions.Def_XinGoldbergTBS_Asymptotic_Model
import Definitions.Def_XinGoldbergTBS_Asymptotic_Constants

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

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

open XinGoldbergTBS.Asymptotic in
theorem solution (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) (hL : L₀ + 1 < L) :
    tbsCost μ κ L₀ L 0 0 = ENNReal.ofReal (UConst μ κ L₀) ∧
    ENNReal.ofReal (gConst μ κ L₀) ≤ OPT μ κ L₀ L ∧
    OPT μ κ L₀ L ≤ ENNReal.ofReal (UConst μ κ L₀) := by
  have h1 := XGOB.tbs00 μ κ L₀ L
  refine ⟨h1, le_iInf fun π => XGOB.policy_lower μ κ π (by omega) (by omega), ?_⟩
  rw [← h1]
  exact iInf_le _ (tbsPolicy L₀ L 0 0)
