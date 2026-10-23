-- Prove2me | solution 1 for RiskControl.WSR.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-23T02:25:50.973901+00:00
-- url     : https://prove2.me/submissions/af8a1015-5237-48ce-a677-1a22b76f46c0

import Mathlib
import Definitions.Def_RiskControl_WSR_Process

open MeasureTheory

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace WSRProof

abbrev Sample (n : ℕ) := Fin n → ℝ
abbrev sampleLaw (Q : Measure ℝ) (n : ℕ) := Measure.pi (fun _ : Fin n => Q)
def resize {i : ℕ} (m : ℕ) (u : Sample i) : Sample m :=
  fun j => if h : j.val < i then u ⟨j.val, h⟩ else 0
noncomputable def nativeFraction (n : ℕ) (δ : ℝ) (i : ℕ) (u : Sample i) : ℝ :=
  RiskControl.WSR.nu n δ (resize n u) (i + 1)
noncomputable def wealth (b : (i : ℕ) → Sample i → ℝ) (R : ℝ) :
    (i : ℕ) → Sample i → ℝ
  | 0, _ => 1
  | i + 1, u => wealth b R i (Fin.init u) *
      (1 - b i (Fin.init u) * (u (Fin.last i) - R))
noncomputable def stopped (b : (i : ℕ) → Sample i → ℝ) (R c : ℝ) :
    (i : ℕ) → Sample i → ℝ
  | 0, _ => 1
  | i + 1, u =>
      if c < stopped b R c i (Fin.init u) then stopped b R c i (Fin.init u)
      else stopped b R c i (Fin.init u) *
        (1 - b i (Fin.init u) * (u (Fin.last i) - R))
def crossing (b : (i : ℕ) → Sample i → ℝ) (R c : ℝ) (n : ℕ) : Set (Sample n) :=
  {u | ∃ i ∈ Finset.Icc 1 n, c < wealth b R i (resize i u)}

end WSRProof

open MeasureTheory
open scoped BigOperators
namespace WSRProof
open RiskControl.WSR

theorem measurable_resize {i : ℕ} (m : ℕ) : Measurable (resize (i := i) m) := by
  apply measurable_pi_lambda
  intro j
  simp only [resize]
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const

theorem measurable_muHat (n i : ℕ) : Measurable (fun u : Sample n => muHat u i) := by
  unfold muHat
  exact (measurable_const.add (Finset.measurable_sum _ fun j _ =>
    (stronglyMeasurable_obs n j).measurable)).div_const _

theorem measurable_sigmaSqHat (n i : ℕ) :
    Measurable (fun u : Sample n => sigmaSqHat u i) := by
  unfold sigmaSqHat
  apply Measurable.div_const
  apply Measurable.add measurable_const
  apply Finset.measurable_sum
  intro j _
  exact ((stronglyMeasurable_obs n j).measurable.sub (measurable_muHat n j)).pow_const 2

theorem measurable_nu (n : ℕ) (δ : ℝ) (i : ℕ) : Measurable (fun u => nu n δ u i) := by
  unfold nu
  exact measurable_const.min ((measurable_const.div
    (measurable_const.mul (measurable_sigmaSqHat n (i-1)))).sqrt)

theorem nativeFraction_measurable (n : ℕ) (δ : ℝ) (i : ℕ) :
    Measurable (nativeFraction n δ i) :=
  (measurable_nu n δ (i+1)).comp (measurable_resize n)

theorem nu_bounds (n : ℕ) (δ : ℝ) (u : Sample n) (i : ℕ) :
    0 ≤ nu n δ u i ∧ nu n δ u i ≤ 1 := by
  exact ⟨le_min (by norm_num) (Real.sqrt_nonneg _), min_le_left _ _⟩

theorem nativeFraction_bounds (n : ℕ) (δ : ℝ) (i : ℕ) (u : Sample i) :
    0 ≤ nativeFraction n δ i u ∧ nativeFraction n δ i u ≤ 1 :=
  nu_bounds n δ (resize n u) (i+1)

theorem obs_congr {n : ℕ} {u v : Sample n} {i : ℕ}
    (h : ∀ j : Fin n, j.val < i → u j = v j) {j : ℕ} (hj : j ≤ i) :
    obs u j = obs v j := by
  unfold obs
  split_ifs with hq
  · apply h
    change j - 1 < i
    omega
  · rfl

theorem muHat_congr {n : ℕ} {u v : Sample n} {i : ℕ}
    (h : ∀ j : Fin n, j.val < i → u j = v j) {j : ℕ} (hj : j ≤ i) :
    muHat u j = muHat v j := by
  unfold muHat
  congr 2
  apply Finset.sum_congr rfl
  intro k hk
  exact obs_congr h (le_trans (Finset.mem_Icc.mp hk).2 hj)

theorem sigmaSqHat_congr {n : ℕ} {u v : Sample n} {i : ℕ}
    (h : ∀ j : Fin n, j.val < i → u j = v j) :
    sigmaSqHat u i = sigmaSqHat v i := by
  unfold sigmaSqHat
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  rw [obs_congr h (Finset.mem_Icc.mp hj).2,
    muHat_congr h (Finset.mem_Icc.mp hj).2]

theorem fraction_prefix (n : ℕ) (δ : ℝ) (u : Sample n) (i : ℕ) (hi : i ≤ n) :
    nativeFraction n δ i (resize i u) = nu n δ u (i+1) := by
  unfold nativeFraction nu
  simp only [Nat.add_sub_cancel]
  rw [sigmaSqHat_congr (u := resize n (resize i u)) (v := u) (i := i)]
  intro j hj
  simp only [resize, hj, dite_true]
  have hn : j.val < n := lt_of_lt_of_le hj hi
  simp only [hn, dite_true]

theorem init_resize {n : ℕ} (u : Sample n) (i : ℕ) :
    Fin.init (resize (i+1) u) = resize i u := by
  ext j
  simp [Fin.init, resize]

theorem resize_self {n : ℕ} (u : Sample n) : resize n u = u := by
  ext j
  simp [resize]

theorem native_wealth_eq (n : ℕ) (δ R : ℝ) (u : Sample n) (i : ℕ) (hi : i ≤ n) :
    wealth (nativeFraction n δ) R i (resize i u) = K n δ u i R := by
  induction i with
  | zero => simp [wealth, K]
  | succ i ih =>
    have hin : i < n := by omega
    rw [wealth, init_resize, ih (by omega), fraction_prefix n δ u i (by omega)]
    have ho : obs u (i+1) = resize (i+1) u (Fin.last i) := by
      simp [obs, resize, hin]
    rw [← ho]
    unfold K
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ i+1)]

end WSRProof

open MeasureTheory
open scoped BigOperators
namespace WSRProof
open RiskControl.WSR

theorem obs_bounds {n : ℕ} (u : Sample n) (hu : ∀ j, u j ∈ Set.Icc (0 : ℝ) 1)
    (j : ℕ) : 0 ≤ obs u j ∧ obs u j ≤ 1 := by
  unfold obs
  split_ifs
  · exact hu _
  · norm_num

theorem factor_nonneg (n : ℕ) (δ : ℝ) (u : Sample n)
    (hu : ∀ j, u j ∈ Set.Icc (0 : ℝ) 1) (j : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    0 ≤ 1 - nu n δ u j * (obs u j - R) := by
  have hb := nu_bounds n δ u j
  have hx := obs_bounds u hu j
  nlinarith [mul_nonneg hb.1 hR, mul_le_one₀ hb.2 hx.1 hx.2]

theorem capital_monotone (n : ℕ) (δ : ℝ) (u : Sample n)
    (hu : ∀ j, u j ∈ Set.Icc (0 : ℝ) 1) (i : ℕ) :
    MonotoneOn (fun R => K n δ u i R) (Set.Ici 0) := by
  intro R hR S _ hRS
  apply Finset.prod_le_prod
  · intro j _
    exact factor_nonneg n δ u hu j R hR
  · intro j _
    have hb := (nu_bounds n δ u j).1
    nlinarith [mul_nonneg hb (sub_nonneg.mpr hRS)]

theorem ucb_lt_implies_crossing (n : ℕ) (δ : ℝ) (u : Sample n)
    (hu : ∀ j, u j ∈ Set.Icc (0 : ℝ) 1) (R : ℝ) (hR : 0 ≤ R) :
    wsrUCB n δ u < (R : EReal) →
      u ∈ crossing (nativeFraction n δ) R (1 / δ) n := by
  intro h
  obtain ⟨z, hz, hzr⟩ := sInf_lt_iff.mp h
  obtain ⟨r, ⟨hr, i, hi, hk⟩, rfl⟩ := hz
  have hrR : r < R := EReal.coe_lt_coe_iff.mp hzr
  refine ⟨i, hi, ?_⟩
  rw [native_wealth_eq n δ R u i (Finset.mem_Icc.mp hi).2]
  exact lt_of_lt_of_le hk (capital_monotone n δ u hu i hr hR hrR.le)

end WSRProof

open MeasureTheory
open scoped BigOperators
namespace WSRProof

theorem loss_integrable (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ x ∂Q, x ∈ Set.Icc (0 : ℝ) 1) : Integrable (fun x : ℝ => x) Q := by
  apply (integrable_const (1 : ℝ)).mono' measurable_id.aestronglyMeasurable
  filter_upwards [hQ] with x hx
  change ‖x‖ ≤ 1
  simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2

theorem mean_mem_Icc (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ x ∂Q, x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x, x ∂Q) ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨integral_nonneg_of_ae (hQ.mono fun _ hx => hx.1), ?_⟩
  have h := integral_mono_ae (loss_integrable Q hQ) (integrable_const (1 : ℝ))
    (hQ.mono fun _ hx => hx.2)
  simpa using h

theorem sample_supported (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ x ∂Q, x ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
    ∀ᵐ u ∂sampleLaw Q n, ∀ j, u j ∈ Set.Icc (0 : ℝ) 1 := by
  apply Filter.eventually_all.2
  intro j
  exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => Q) (i := j)).eventually hQ

theorem integral_snoc (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (n : ℕ) (f : Sample (n + 1) → ℝ)
    (hf : Integrable f (sampleLaw Q (n + 1))) :
    (∫ u, f u ∂sampleLaw Q (n + 1)) =
      ∫ v, (∫ x, f (Fin.snoc v x) ∂Q) ∂sampleLaw Q n := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
  have he : MeasurePreserving e (sampleLaw Q (n + 1)) (Q.prod (sampleLaw Q n)) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => Q) (Fin.last n)
  have hi : Integrable (fun p : ℝ × Sample n => f (e.symm p))
      (Q.prod (sampleLaw Q n)) := he.symm.integrable_comp_of_integrable hf
  have heq (x : ℝ) (v : Sample n) : e.symm (x, v) = Fin.snoc v x := by
    simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_last']
    rfl
  calc
    _ = ∫ p : ℝ × Sample n, f (e.symm p) ∂Q.prod (sampleLaw Q n) :=
      (he.symm.integral_comp' f).symm
    _ = ∫ v, (∫ x, f (e.symm (x, v)) ∂Q) ∂sampleLaw Q n :=
      integral_prod_symm _ hi
    _ = _ := by simp_rw [heq]

end WSRProof

open MeasureTheory
open scoped BigOperators
namespace WSRProof

private theorem init_measurable (n : ℕ) :
    Measurable (Fin.init : Sample (n + 1) → Sample n) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

theorem stopped_measurable (b : (i : ℕ) → Sample i → ℝ)
    (hb : ∀ i, Measurable (b i)) (R c : ℝ) (n : ℕ) :
    Measurable (stopped b R c n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hs := ih.comp (init_measurable n)
    have hf : Measurable (fun u : Sample (n + 1) =>
        1 - b n (Fin.init u) * (u (Fin.last n) - R)) :=
      measurable_const.sub ((hb n |>.comp (init_measurable n)).mul
        ((measurable_pi_apply (Fin.last n) :
          Measurable (fun u : Sample (n + 1) => u (Fin.last n))).sub_const R))
    exact Measurable.ite (measurableSet_lt measurable_const hs) hs (hs.mul hf)

theorem stopped_bounds (b : (i : ℕ) → Sample i → ℝ)
    (hb : ∀ i u, 0 ≤ b i u ∧ b i u ≤ 1) (R c : ℝ)
    (hR : R ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) (u : Sample n)
    (hu : ∀ j, u j ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ stopped b R c n u ∧ stopped b R c n u ≤ (2 : ℝ)^n := by
  induction n with
  | zero => simp [stopped]
  | succ n ih =>
    have hs := ih (Fin.init u) (fun j => hu j.castSucc)
    have hbet := hb n (Fin.init u)
    have hx := hu (Fin.last n)
    have hf0 : 0 ≤ 1 - b n (Fin.init u) * (u (Fin.last n) - R) := by
      nlinarith [mul_nonneg hbet.1 hR.1, mul_nonneg hbet.1 (sub_nonneg.mpr hx.2)]
    have hf2 : 1 - b n (Fin.init u) * (u (Fin.last n) - R) ≤ 2 := by
      nlinarith [mul_nonneg hbet.1 hx.1, mul_nonneg hbet.1 (sub_nonneg.mpr hR.2)]
    simp only [stopped]
    split_ifs
    · exact ⟨hs.1, hs.2.trans (by rw [pow_succ]; nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n])⟩
    · refine ⟨mul_nonneg hs.1 hf0, ?_⟩
      calc
        _ ≤ (2 : ℝ)^n * 2 := mul_le_mul hs.2 hf2 hf0 (pow_nonneg (by norm_num) n)
        _ = _ := (pow_succ _ _).symm

theorem stopped_integrable (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ x ∂Q, x ∈ Set.Icc (0 : ℝ) 1)
    (b : (i : ℕ) → Sample i → ℝ) (hb_meas : ∀ i, Measurable (b i))
    (hb_bounds : ∀ i u, 0 ≤ b i u ∧ b i u ≤ 1) (c : ℝ) (n : ℕ) :
    Integrable (stopped b (∫ x, x ∂Q) c n) (sampleLaw Q n) := by
  apply (integrable_const ((2 : ℝ)^n)).mono'
    (stopped_measurable b hb_meas _ c n).aestronglyMeasurable
  filter_upwards [sample_supported Q hQ n] with u hu
  have h := stopped_bounds b hb_bounds _ c (mean_mem_Icc Q hQ) n u hu
  simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

theorem stopped_expectation (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ x ∂Q, x ∈ Set.Icc (0 : ℝ) 1)
    (b : (i : ℕ) → Sample i → ℝ)
    (hb_meas : ∀ i, Measurable (b i))
    (hb_bounds : ∀ i u, 0 ≤ b i u ∧ b i u ≤ 1)
    (c : ℝ) (n : ℕ) :
    Integrable (stopped b (∫ x, x ∂Q) c n) (sampleLaw Q n) ∧
      (∀ᵐ u ∂sampleLaw Q n, 0 ≤ stopped b (∫ x, x ∂Q) c n u) ∧
      (∫ u, stopped b (∫ x, x ∂Q) c n u ∂sampleLaw Q n) = 1 := by
  refine ⟨stopped_integrable Q hQ b hb_meas hb_bounds c n, ?_, ?_⟩
  · filter_upwards [sample_supported Q hQ n] with u hu
    exact (stopped_bounds b hb_bounds _ c (mean_mem_Icc Q hQ) n u hu).1
  · induction n with
    | zero => simp [stopped]
    | succ n ih =>
      rw [integral_snoc Q n _ (stopped_integrable Q hQ b hb_meas hb_bounds c (n + 1))]
      have inner (v : Sample n) :
          (∫ x, stopped b (∫ x, x ∂Q) c (n + 1) (Fin.snoc v x) ∂Q) =
            stopped b (∫ x, x ∂Q) c n v := by
        simp only [stopped, Fin.init_snoc, Fin.snoc_last]
        split_ifs
        · simp
        · have hx : Integrable (fun x : ℝ => x - ∫ y, y ∂Q) Q :=
            (loss_integrable Q hQ).sub (integrable_const _)
          have hbI : Integrable (fun x : ℝ => b n v * (x - ∫ y, y ∂Q)) Q :=
            hx.const_mul _
          rw [integral_const_mul, integral_sub (integrable_const (1 : ℝ)) hbI,
            integral_const_mul, integral_sub (loss_integrable Q hQ) (integrable_const _)]
          simp
      simp_rw [inner]
      exact ih

private theorem stop_resize_self {n : ℕ} (u : Sample n) : resize n u = u := by
  funext j
  simp [resize, j.isLt]

private theorem stop_resize_init {n i : ℕ} (hi : i ≤ n) (u : Sample (n + 1)) :
    resize i (Fin.init u) = resize i u := by
  funext j
  have hj : j.val < n := lt_of_lt_of_le j.isLt hi
  simp [resize, hj, lt_trans hj (Nat.lt_succ_self n), Fin.init]

private theorem stopped_eq_of_le (b : (i : ℕ) → Sample i → ℝ)
    (R c : ℝ) (n : ℕ) (u : Sample n) (h : stopped b R c n u ≤ c) :
    stopped b R c n u = wealth b R n u := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases hp : c < stopped b R c n (Fin.init u)
    · simp only [stopped, if_pos hp] at h
      exact (not_lt_of_ge h hp).elim
    · have he := ih (Fin.init u) (le_of_not_gt hp)
      rw [stopped, if_neg hp, he, wealth]

theorem crossing_imp_stopped (b : (i : ℕ) → Sample i → ℝ)
    (R c : ℝ) (n : ℕ) (u : Sample n)
    (hu : u ∈ crossing b R c n) :
    c < stopped b R c n u := by
  induction n with
  | zero =>
    rcases hu with ⟨i, hi, _⟩
    simp only [Finset.mem_Icc] at hi
    omega
  | succ n ih =>
    by_cases hp : c < stopped b R c n (Fin.init u)
    · simpa only [stopped, if_pos hp] using hp
    · rcases hu with ⟨i, hi, hcross⟩
      have hilo := (Finset.mem_Icc.mp hi).1
      have hihi := (Finset.mem_Icc.mp hi).2
      by_cases hin : i ≤ n
      · have hprev : Fin.init u ∈ crossing b R c n := by
          refine ⟨i, Finset.mem_Icc.mpr ⟨hilo, hin⟩, ?_⟩
          simpa only [stop_resize_init hin] using hcross
        exact (hp (ih (Fin.init u) hprev)).elim
      · have hieq : i = n + 1 := by omega
        subst i
        rw [stop_resize_self] at hcross
        have he := stopped_eq_of_le b R c n (Fin.init u) (le_of_not_gt hp)
        rw [stopped, if_neg hp, he]
        exact hcross

end WSRProof

open MeasureTheory
namespace WSRProof

theorem betting_crossing_bound (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ x ∂Q, x ∈ Set.Icc (0 : ℝ) 1)
    (b : (i : ℕ) → Sample i → ℝ)
    (hb_meas : ∀ i, Measurable (b i))
    (hb_bounds : ∀ i u, 0 ≤ b i u ∧ b i u ≤ 1)
    (n : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    sampleLaw Q n (crossing b (∫ x, x ∂Q) (1 / δ) n) ≤ ENNReal.ofReal δ := by
  have _ := hδ1
  obtain ⟨hI, h0, hmean⟩ := stopped_expectation Q hQ b hb_meas hb_bounds (1 / δ) n
  have hm := mul_meas_ge_le_integral_of_nonneg h0 hI (1 / δ)
  rw [hmean] at hm
  have hc : 0 < 1 / δ := one_div_pos.mpr hδ0
  have hr : (sampleLaw Q n).real {u | 1 / δ ≤ stopped b (∫ x, x ∂Q) (1 / δ) n u} ≤ δ := by
    have h : (sampleLaw Q n).real {u | 1 / δ ≤ stopped b (∫ x, x ∂Q) (1 / δ) n u} ≤ 1 / (1 / δ) :=
      (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hm)
    simpa using h
  calc
    _ ≤ sampleLaw Q n {u | 1 / δ ≤ stopped b (∫ x, x ∂Q) (1 / δ) n u} :=
      measure_mono fun u hu => (crossing_imp_stopped b _ _ n u hu).le
    _ = ENNReal.ofReal ((sampleLaw Q n).real
        {u | 1 / δ ≤ stopped b (∫ x, x ∂Q) (1 / δ) n u}) :=
      (ofReal_measureReal (by finiteness)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hr

end WSRProof

open MeasureTheory

namespace RiskControl.WSR

/-- Proposition 5 (Waudby-Smith–Ramdas bound), p. 7 (arXiv:2101.02703v3): for `n ≥ 1` i.i.d.
losses with law `Q` on `[0, 1]` and `δ ∈ (0, 1)`, `R̂⁺_WSR` is a `(1 − δ)` upper confidence
bound for the mean `R = ∫ x dQ`: `Qⁿ(R̂⁺_WSR < R) ≤ δ`. -/
theorem proposition_5 (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ x ∂Q, x ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) (hn : 1 ≤ n)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (Measure.pi fun _ : Fin n => Q)
        {ω | wsrUCB n δ ω < ((∫ x, x ∂Q : ℝ) : EReal)} ≤ ENNReal.ofReal δ := by
  have _ := hn
  have hm := WSRProof.mean_mem_Icc Q hQ
  calc
    _ ≤ WSRProof.sampleLaw Q n
        (WSRProof.crossing (WSRProof.nativeFraction n δ) (∫ x, x ∂Q) (1 / δ) n) := by
      apply MeasureTheory.measure_mono_ae
      filter_upwards [WSRProof.sample_supported Q hQ n] with u hu
      exact WSRProof.ucb_lt_implies_crossing n δ u hu (∫ x, x ∂Q) hm.1
    _ ≤ ENNReal.ofReal δ := WSRProof.betting_crossing_bound Q hQ
      (WSRProof.nativeFraction n δ) (WSRProof.nativeFraction_measurable n δ)
      (WSRProof.nativeFraction_bounds n δ) n δ hδ0 hδ1

end RiskControl.WSR

open RiskControl.WSR

theorem solution (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ x ∂Q, x ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) (hn : 1 ≤ n)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (Measure.pi fun _ : Fin n => Q)
        {ω | wsrUCB n δ ω < ((∫ x, x ∂Q : ℝ) : EReal)} ≤ ENNReal.ofReal δ := by
  exact RiskControl.WSR.proposition_5 Q hQ n hn δ hδ0 hδ1
