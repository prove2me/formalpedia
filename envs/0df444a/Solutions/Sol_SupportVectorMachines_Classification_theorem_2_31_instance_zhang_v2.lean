-- Prove2me | solution 1 for SupportVectorMachines.Classification.theorem_2_31_instance_zhang_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T09:31:50.907469+00:00
-- url     : https://prove2.me/submissions/2c2f26ee-a8fd-4cbf-b7d4-2beb44a2334d

import Mathlib
import Definitions.Def_SupportVectorMachines_Classification_RiskBasics_v2
import Definitions.Def_SupportVectorMachines_Classification_ClassificationLosses_v2

open MeasureTheory

namespace ZG88
open SupportVectorMachines.Classification

/-- pointwise Zhang -/
lemma pointwise (η t : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1) :
    η * (if (1:ℝ) * sgn t ≤ 0 then 1 else 0) + (1 - η) * (if (-1:ℝ) * sgn t ≤ 0 then 1 else 0)
      + min η (1 - η) ≤ η * max 0 (1 - 1 * t) + (1 - η) * max 0 (1 - (-1) * t) := by
  have ha := le_max_left (0:ℝ) (1 - t)
  have hb := le_max_right (0:ℝ) (1 - t)
  have hc := le_max_left (0:ℝ) (1 + t)
  have hd := le_max_right (0:ℝ) (1 + t)
  have e1 := mul_le_mul_of_nonneg_left ha h0
  have e2 := mul_le_mul_of_nonneg_left hb h0
  have e3 := mul_le_mul_of_nonneg_left hc (by linarith : (0:ℝ) ≤ 1 - η)
  have e4 := mul_le_mul_of_nonneg_left hd (by linarith : (0:ℝ) ≤ 1 - η)
  simp only [one_mul, neg_one_mul, sub_neg_eq_add]
  unfold sgn
  rcases le_total η (1/2) with hη | hη
  · rw [min_eq_left (by linarith)]
    by_cases ht : t < 0
    · simp only [ht, if_true]; norm_num
      nlinarith [mul_nonneg h0 (by linarith : (0:ℝ) ≤ -t)]
    · simp only [ht, if_false]; norm_num
      have ht' : 0 ≤ t := le_of_not_gt ht
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - 2 * η) ht']
  · rw [min_eq_right (by linarith)]
    by_cases ht : t < 0
    · simp only [ht, if_true]; norm_num
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 * η - 1) (by linarith : (0:ℝ) ≤ -t)]
    · simp only [ht, if_false]; norm_num
      have ht' : 0 ≤ t := le_of_not_gt ht
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - η) ht']

lemma class_lower (η t : ℝ) (_h0 : 0 ≤ η) (_h1 : η ≤ 1) :
    min η (1 - η) ≤
    η * (if (1:ℝ) * sgn t ≤ 0 then 1 else 0) + (1 - η) * (if (-1:ℝ) * sgn t ≤ 0 then 1 else 0) := by
  unfold sgn
  by_cases ht : t < 0
  · simp only [ht, if_true]; norm_num
  · simp only [ht, if_false]; norm_num

lemma hinge_upper (η : ℝ) :
    η * max 0 (1 - 1 * sgn (2 * η - 1)) + (1 - η) * max 0 (1 - (-1) * sgn (2 * η - 1))
      ≤ 2 * min η (1 - η) := by
  unfold sgn
  by_cases ht : 2 * η - 1 < 0
  · simp only [ht, if_true]; norm_num
    rw [min_eq_left (by linarith)]; linarith
  · simp only [ht, if_false]; norm_num
    rw [min_eq_right (by linarith)]; linarith

variable {X : Type*} [MeasurableSpace X]

noncomputable def nu (P : Measure (X × ℝ)) (y : ℝ) : Measure X :=
  (P.restrict (Set.univ ×ˢ {y})).map Prod.fst

lemma measurable_L (L : Loss X) (y : ℝ) {g : X → ℝ} (hg : Measurable g) :
    Measurable (fun x => ENNReal.ofReal (L x y (g x))) :=
  ENNReal.measurable_ofReal.comp
    (L.measurable.comp (measurable_id.prodMk (measurable_const.prodMk hg)))

lemma risk_split (L : Loss X) (P : Measure (X × ℝ)) [IsProbabilityMeasure P]
    (hY : P (Set.univ ×ˢ ({-1, 1} : Set ℝ)) = 1) {g : X → ℝ} (hg : Measurable g) :
    risk L P g = ∫⁻ x, ENNReal.ofReal (L x 1 (g x)) ∂(nu P 1)
      + ∫⁻ x, ENNReal.ofReal (L x (-1) (g x)) ∂(nu P (-1)) := by
  have hSm : MeasurableSet ((Set.univ : Set X) ×ˢ ({-1, 1} : Set ℝ)) :=
    MeasurableSet.univ.prod (by measurability)
  have hc : P ((Set.univ : Set X) ×ˢ ({-1, 1} : Set ℝ))ᶜ = 0 := by
    rw [measure_compl hSm (measure_ne_top _ _), hY]; simp
  have hres : P.restrict (Set.univ ×ˢ ({-1, 1} : Set ℝ)) = P :=
    Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.2 hc)
  have hsplit : (Set.univ : Set X) ×ˢ ({-1, 1} : Set ℝ) =
      (Set.univ ×ˢ ({-1} : Set ℝ)) ∪ (Set.univ ×ˢ ({1} : Set ℝ)) := by
    rw [← Set.prod_union]; rfl
  have hdisj : Disjoint ((Set.univ : Set X) ×ˢ ({-1} : Set ℝ)) (Set.univ ×ˢ ({1} : Set ℝ)) := by
    rw [Set.disjoint_prod]; right; norm_num
  unfold risk
  rw [← hres, hsplit, lintegral_union (MeasurableSet.univ.prod (measurableSet_singleton _)) hdisj,
    add_comm]
  unfold nu
  rw [lintegral_map (measurable_L L 1 hg) measurable_fst,
    lintegral_map (measurable_L L (-1) hg) measurable_fst]
  rw [Measure.restrict_restrict (MeasurableSet.univ.prod (measurableSet_singleton _)),
    Measure.restrict_restrict (MeasurableSet.univ.prod (measurableSet_singleton _))]
  rw [Set.inter_eq_left.2 Set.subset_union_right,
    Set.inter_eq_left.2 Set.subset_union_left]
  congr 1
  · refine setLIntegral_congr_fun (MeasurableSet.univ.prod (measurableSet_singleton _)) ?_
    rintro ⟨x, y⟩ ⟨-, hy⟩
    simp only [Set.mem_singleton_iff] at hy
    subst hy; rfl
  · refine setLIntegral_congr_fun (MeasurableSet.univ.prod (measurableSet_singleton _)) ?_
    rintro ⟨x, y⟩ ⟨-, hy⟩
    simp only [Set.mem_singleton_iff] at hy
    subst hy; rfl

noncomputable def mu (P : Measure (X × ℝ)) : Measure X := nu P 1 + nu P (-1)

noncomputable def eta (P : Measure (X × ℝ)) (x : X) : ℝ := ((nu P 1).rnDeriv (mu P) x).toReal

instance (P : Measure (X × ℝ)) [IsFiniteMeasure P] (y : ℝ) : IsFiniteMeasure (nu P y) := by
  unfold nu; infer_instance

instance (P : Measure (X × ℝ)) [IsFiniteMeasure P] : IsFiniteMeasure (mu P) := by
  unfold mu; infer_instance

lemma measurable_eta (P : Measure (X × ℝ)) : Measurable (eta P) :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal

lemma eta_nonneg (P : Measure (X × ℝ)) (x : X) : 0 ≤ eta P x := ENNReal.toReal_nonneg

lemma ae_sum (P : Measure (X × ℝ)) [IsFiniteMeasure P] :
    ∀ᵐ x ∂(mu P), (nu P 1).rnDeriv (mu P) x + (nu P (-1)).rnDeriv (mu P) x = 1 := by
  have h1 := Measure.rnDeriv_add (nu P 1) (nu P (-1)) (mu P)
  have h2 := Measure.rnDeriv_self (mu P)
  unfold mu at h1 h2 ⊢
  filter_upwards [h1, h2] with x hx1 hx2
  rw [← hx2, hx1]; rfl

lemma ae_eta_le (P : Measure (X × ℝ)) [IsFiniteMeasure P] :
    ∀ᵐ x ∂(mu P), eta P x ≤ 1 := by
  filter_upwards [ae_sum P] with x hx
  have : (nu P 1).rnDeriv (mu P) x ≤ 1 := by rw [← hx]; exact le_self_add
  unfold eta
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)

lemma risk_eq (L : Loss X) (P : Measure (X × ℝ)) [IsProbabilityMeasure P]
    (hY : P (Set.univ ×ˢ ({-1, 1} : Set ℝ)) = 1) {g : X → ℝ} (hg : Measurable g) :
    risk L P g = ∫⁻ x, ENNReal.ofReal
      (eta P x * L x 1 (g x) + (1 - eta P x) * L x (-1) (g x)) ∂(mu P) := by
  rw [risk_split L P hY hg]
  have hac1 : nu P 1 ≪ mu P := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hac2 : nu P (-1) ≪ mu P := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  rw [← lintegral_rnDeriv_mul hac1 (measurable_L L 1 hg).aemeasurable,
    ← lintegral_rnDeriv_mul hac2 (measurable_L L (-1) hg).aemeasurable,
    ← lintegral_add_left (f := fun x => (nu P 1).rnDeriv (mu P) x * ENNReal.ofReal (L x 1 (g x)))
      ((Measure.measurable_rnDeriv _ _).mul (measurable_L L 1 hg))]
  apply lintegral_congr_ae
  filter_upwards [ae_sum P] with x hx
  set a := (nu P 1).rnDeriv (mu P) x
  set b := (nu P (-1)).rnDeriv (mu P) x
  have ha1 : a ≤ 1 := by rw [← hx]; exact le_self_add
  have hatop : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ha1
  have hb : b = 1 - a := ENNReal.eq_sub_of_add_eq hatop (by rw [add_comm]; exact hx)
  have hη : eta P x = a.toReal := rfl
  have hηle : a.toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using ha1)
  have hL1 := L.nonneg x 1 (g x)
  have hL2 := L.nonneg x (-1) (g x)
  rw [hη, ENNReal.ofReal_add (mul_nonneg ENNReal.toReal_nonneg hL1)
    (mul_nonneg (by linarith) hL2), ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_toReal hatop, hb,
    ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hatop, ENNReal.ofReal_one]

end ZG88

open MeasureTheory SupportVectorMachines.Classification in
theorem solution {X : Type*} [MeasurableSpace X] (P : Measure (X × ℝ))
    [IsProbabilityMeasure P] (hY : P (Set.univ ×ˢ ({-1, 1} : Set ℝ)) = 1)
    (f : X → ℝ) (hf : Measurable f) :
    risk classLoss P f - bayesRisk classLoss P ≤
      risk hingeLoss P f - bayesRisk hingeLoss P := by
  set η := ZG88.eta P
  set μ := ZG88.mu P
  set M : ENNReal := ∫⁻ x, ENNReal.ofReal (min (η x) (1 - η x)) ∂μ with hM
  have hηm : Measurable η := ZG88.measurable_eta P
  have hmm : Measurable (fun x => ENNReal.ofReal (min (η x) (1 - η x))) :=
    ENNReal.measurable_ofReal.comp (hηm.min (measurable_const.sub hηm))
  have hMtop : M ≠ ⊤ := by
    refine ne_top_of_le_ne_top (measure_ne_top μ Set.univ) ?_
    rw [← lintegral_one]
    apply lintegral_mono_ae
    filter_upwards [ZG88.ae_eta_le P] with x hx
    have := ZG88.eta_nonneg P x
    exact ENNReal.ofReal_le_one.2 (le_trans (min_le_left _ _) hx)
  -- A + M ≤ Cc
  have h1 : risk classLoss P f + M ≤ risk hingeLoss P f := by
    rw [ZG88.risk_eq _ P hY hf, ZG88.risk_eq _ P hY hf, hM, ← lintegral_add_right _ hmm]
    apply lintegral_mono_ae
    filter_upwards [ZG88.ae_eta_le P] with x hx
    have h0 := ZG88.eta_nonneg P x
    rw [← ENNReal.ofReal_add]
    · apply ENNReal.ofReal_le_ofReal
      exact ZG88.pointwise (η x) (f x) h0 hx
    · apply add_nonneg
      · exact mul_nonneg h0 (classLoss.nonneg _ _ _)
      · exact mul_nonneg (by linarith) (classLoss.nonneg _ _ _)
    · exact le_min h0 (by linarith)
  -- M ≤ B
  have h2 : M ≤ bayesRisk classLoss P := by
    refine le_iInf₂ fun g hg => ?_
    rw [ZG88.risk_eq _ P hY hg]
    apply lintegral_mono_ae
    filter_upwards [ZG88.ae_eta_le P] with x hx
    exact ENNReal.ofReal_le_ofReal (ZG88.class_lower (η x) (g x) (ZG88.eta_nonneg P x) hx)
  -- D ≤ M + M
  have h3 : bayesRisk hingeLoss P ≤ M + M := by
    have hg : Measurable (fun x => sgn (2 * η x - 1)) :=
      measurable_sgn.comp ((measurable_const.mul hηm).sub measurable_const)
    refine le_trans (iInf₂_le _ hg) ?_
    rw [ZG88.risk_eq _ P hY hg, hM, ← lintegral_add_left hmm]
    apply lintegral_mono_ae
    filter_upwards [ZG88.ae_eta_le P] with x hx
    have h0 := ZG88.eta_nonneg P x
    rw [← ENNReal.ofReal_add (le_min h0 (by linarith)) (le_min h0 (by linarith))]
    apply ENNReal.ofReal_le_ofReal
    have := ZG88.hinge_upper (η x)
    simp only [hingeLoss]
    linarith
  calc risk classLoss P f - bayesRisk classLoss P ≤ risk classLoss P f - M :=
        tsub_le_tsub_left h2 _
    _ ≤ (risk hingeLoss P f - M) - M :=
        tsub_le_tsub_right (ENNReal.le_sub_of_add_le_right hMtop h1) _
    _ = risk hingeLoss P f - (M + M) := tsub_tsub _ _ _
    _ ≤ risk hingeLoss P f - bayesRisk hingeLoss P := tsub_le_tsub_left h3 _
