-- Prove2me | solution 1 for SupplyChainTheory.chain_optimal_fractile
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T02:05:42.909274+00:00
-- url     : https://prove2.me/submissions/a1d10529-062f-4314-8d32-f53497722b54

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts

open MeasureTheory ProbabilityTheory

namespace SupplyChainTheory

lemma sc_int_min (D : Measure ℝ) [IsProbabilityMeasure D]
    (hD : Integrable (fun x => x) D) (Q : ℝ) : Integrable (fun d => min Q d) D := by
  refine Integrable.mono' ((integrable_const |Q|).add hD.abs)
    (measurable_const.min measurable_id).aestronglyMeasurable
    (Filter.Eventually.of_forall fun d => ?_)
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rcases le_total Q d with h | h
  · rw [min_eq_left h]; linarith [abs_nonneg d]
  · rw [min_eq_right h]; linarith [abs_nonneg Q]

lemma sc_rv (P : ContractData) : 0 < P.r - P.v := by
  have := P.profitable; have := P.cs_nonneg; have := P.v_lt_cr; linarith

lemma sc_K (P : ContractData) : 0 < P.r - P.v + P.p := by
  have := sc_rv P; have := P.ps_nonneg; have := P.pr_nonneg
  simp only [ContractData.p]; linarith

lemma sc_cv (P : ContractData) : 0 < P.c - P.v := by
  have := P.cs_nonneg; have := P.v_lt_cr; simp only [ContractData.c]; linarith

lemma sc_kappa (P : ContractData) :
    0 < (P.c - P.v) / (P.r - P.v + P.p) ∧ (P.c - P.v) / (P.r - P.v + P.p) < 1 := by
  have hK := sc_K P
  refine ⟨div_pos (sc_cv P) hK, (div_lt_one hK).mpr ?_⟩
  have := P.profitable; have := P.ps_nonneg; have := P.pr_nonneg
  simp only [ContractData.c, ContractData.p]; linarith

lemma sc_cdf_cont (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D] :
    Continuous (cdf D) := by
  rw [continuous_iff_continuousAt]
  intro a
  have hmono := monotone_cdf D
  have hleft : Function.leftLim (cdf D) a = cdf D a := by
    have h1 := (cdf D).measure_singleton a
    rw [measure_cdf, measure_singleton] at h1
    have h2 := ENNReal.ofReal_eq_zero.mp h1.symm
    have h3 := hmono.leftLim_le (le_refl a)
    linarith
  have hl : ContinuousWithinAt (cdf D) (Set.Iio a) a :=
    hmono.continuousWithinAt_Iio_iff_leftLim_eq.mpr hleft
  have hr : ContinuousWithinAt (cdf D) (Set.Ioi a) a :=
    ((cdf D).right_continuous a).mono Set.Ioi_subset_Ici_self
  exact continuousAt_iff_continuous_left'_right'.mpr ⟨hl, hr⟩

lemma sc_exists_fractile (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D]
    (κ : ℝ) (h0 : 0 < κ) (h1 : κ < 1) : ∃ Q, 1 - cdf D Q = κ := by
  have hc := sc_cdf_cont D
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot D).eventually
    (gt_mem_nhds (by linarith : (0:ℝ) < 1 - κ))).exists
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop D).eventually
    (lt_mem_nhds (by linarith : 1 - κ < 1))).exists
  obtain ⟨Q, hQ⟩ := intermediate_value_univ a b hc ⟨ha.le, hb.le⟩
  exact ⟨Q, by linarith⟩

lemma sc_sales_deriv (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D]
    (hD : Integrable (fun x => x) D) (Q0 : ℝ) :
    HasDerivAt (expSales D) (1 - cdf D Q0) Q0 := by
  have hlip : ∀ d : ℝ, LipschitzOnWith (Real.nnabs 1) (fun Q : ℝ => min Q d) Set.univ := by
    intro d
    have : Real.nnabs 1 = 1 := by simp
    rw [this]
    exact (LipschitzWith.id.min_const d).lipschitzOnWith
  have hdiff : ∀ d : ℝ, d ≠ Q0 →
      HasDerivAt (fun Q : ℝ => min Q d) (if Q0 < d then (1:ℝ) else 0) Q0 := by
    intro d hd
    rcases lt_or_gt_of_ne hd with h | h
    · rw [if_neg (not_lt.mpr h.le)]
      apply (hasDerivAt_const Q0 d).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds h] with Q hQ
      exact min_eq_right (le_of_lt hQ)
    · rw [if_pos h]
      apply (hasDerivAt_id Q0).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds h] with Q hQ
      exact min_eq_left (le_of_lt hQ)
  have key := hasDerivAt_integral_of_dominated_loc_of_lip (μ := D)
    (F := fun Q d => min Q d) (F' := fun d => if Q0 < d then (1:ℝ) else 0)
    (bound := fun _ => (1:ℝ)) (s := Set.univ) (x₀ := Q0) Filter.univ_mem
    (Filter.Eventually.of_forall fun Q =>
      (measurable_const.min measurable_id).aestronglyMeasurable)
    (sc_int_min D hD Q0)
    ((Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
      measurable_const).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun d => hlip d)
    (integrable_const 1)
    ((Measure.ae_ne D Q0).mono fun d hd => hdiff d hd)
  have hval : ∫ d, (if Q0 < d then (1:ℝ) else 0) ∂D = 1 - cdf D Q0 := by
    have e : (fun d : ℝ => if Q0 < d then (1:ℝ) else 0) = (Set.Ioi Q0).indicator 1 := by
      funext d; simp [Set.indicator_apply]
    rw [e, integral_indicator_one measurableSet_Ioi, cdf_eq_real, ← Set.compl_Iic,
      measureReal_compl measurableSet_Iic, probReal_univ]
  rw [← hval]
  exact key.2

lemma sc_max_iff {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x) (hanti : Antitone g')
    (Q : ℝ) : IsMaxOn g Set.univ Q ↔ g' Q = 0 := by
  constructor
  · intro h
    exact (h.isLocalMax Filter.univ_mem).hasDerivAt_eq_zero (hg Q)
  · intro h0 y _
    have hcont : Continuous g := continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt
    rcases le_total y Q with hyQ | hQy
    · have hmono : MonotoneOn g (Set.Iic Q) := by
        apply monotoneOn_of_deriv_nonneg (convex_Iic Q) hcont.continuousOn
          (fun x _ => (hg x).differentiableAt.differentiableWithinAt)
        intro x hx
        rw [interior_Iic] at hx
        rw [(hg x).deriv]
        have := hanti (le_of_lt hx)
        linarith
      exact hmono hyQ (Set.mem_Iic.mpr le_rfl) hyQ
    · have hanti' : AntitoneOn g (Set.Ici Q) := by
        apply antitoneOn_of_deriv_nonpos (convex_Ici Q) hcont.continuousOn
          (fun x _ => (hg x).differentiableAt.differentiableWithinAt)
        intro x hx
        rw [interior_Ici] at hx
        rw [(hg x).deriv]
        have := hanti (le_of_lt hx)
        linarith
      exact hanti' (Set.mem_Ici.mpr le_rfl) hQy hQy

lemma sc_lin_deriv (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D]
    (hD : Integrable (fun x => x) D) (α β γ : ℝ) (Q : ℝ) :
    HasDerivAt (fun Q => α * expSales D Q - β * Q - γ) (α * (1 - cdf D Q) - β) Q := by
  have h := ((sc_sales_deriv D hD Q).const_mul α).sub ((hasDerivAt_id Q).const_mul β)
  simpa using h.sub_const γ

lemma sc_lin_anti (D : Measure ℝ) (α β : ℝ) (hα : 0 ≤ α) :
    Antitone fun Q => α * (1 - cdf D Q) - β := by
  intro x y hxy
  have := monotone_cdf D hxy
  have := mul_le_mul_of_nonneg_left this hα
  simp only
  linarith

lemma sc_chain_eq (P : ContractData) (D : Measure ℝ) :
    chainProfit P D = fun Q => (P.r - P.v + P.p) * expSales D Q - (P.c - P.v) * Q
      - P.p * meanDemand D := rfl

lemma sc_chain_max_iff (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D]
    [NullSingletonClass D] (hD : Integrable (fun x => x) D) (Q : ℝ) :
    IsMaxOn (chainProfit P D) Set.univ Q ↔
      (P.r - P.v + P.p) * (1 - cdf D Q) - (P.c - P.v) = 0 := by
  rw [sc_chain_eq]
  exact sc_max_iff (fun Q => sc_lin_deriv D hD _ _ _ Q)
    (sc_lin_anti D _ _ (sc_K P).le) Q

theorem sc_fractile (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D]
    [NullSingletonClass D] (hD : Integrable (fun x => x) D) :
    (∀ Q, IsMaxOn (chainProfit P D) Set.univ Q ↔
        1 - cdf D Q = (P.c - P.v) / (P.r - P.v + P.p))
      ∧ ∃ Q0, IsMaxOn (chainProfit P D) Set.univ Q0 := by
  have hK := sc_K P
  have hiff : ∀ Q, IsMaxOn (chainProfit P D) Set.univ Q ↔
      1 - cdf D Q = (P.c - P.v) / (P.r - P.v + P.p) := by
    intro Q
    rw [sc_chain_max_iff P D hD Q, eq_div_iff hK.ne']
    constructor <;> intro h <;> linarith
  refine ⟨hiff, ?_⟩
  obtain ⟨h0, h1⟩ := sc_kappa P
  obtain ⟨Q0, hQ0⟩ := sc_exists_fractile D _ h0 h1
  exact ⟨Q0, (hiff Q0).mpr hQ0⟩

end SupplyChainTheory

open SupplyChainTheory

theorem solution (P : ContractData) (D : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure D]
    [MeasureTheory.NullSingletonClass D] (hD : MeasureTheory.Integrable (fun x => x) D) :
    (∀ Q, IsMaxOn (chainProfit P D) Set.univ Q ↔ 1 - ProbabilityTheory.cdf D Q = (P.c - P.v) / (P.r - P.v + P.p))
      ∧ ∃ Q0, IsMaxOn (chainProfit P D) Set.univ Q0 := by
  exact sc_fractile P D hD
