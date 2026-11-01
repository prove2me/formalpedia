-- Prove2me | solution 1 for StoneRegression.Quantile.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-31T18:45:35.285395+00:00
-- url     : https://prove2.me/submissions/b30a6179-4ce1-4c3f-aa7b-ce1016e1399b

import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting
import Definitions.Def_StoneRegression_Quantile_Quantiles

set_option autoImplicit false
set_option linter.all false

namespace SRQ3

open MeasureTheory ProbabilityTheory Filter Topology StoneRegression.Criterion StoneRegression.Quantile
open scoped ENNReal NNReal

variable {d : ℕ}

/-- Weighted sum `∑ᵢ W_{ni}(X) φ(Yᵢ)` on a path of pairs. -/
noncomputable def wsum (W : WeightSeq d) (n : ℕ) (φ : ℝ → ℝ)
    (ω : ℕ → EuclideanSpace ℝ (Fin d) × ℝ) : ℝ :=
  ∑ i : Fin n, W n (ω 0).1 (fun j => (ω (j.val + 1)).1) i * φ (ω (i.val + 1)).2

lemma measurable_wsum (W : WeightSeq d) (hW : MeasurableWeights W) (n : ℕ) {φ : ℝ → ℝ}
    (hφ : Measurable φ) : Measurable (wsum W n φ) := by
  unfold wsum
  refine Finset.measurable_sum _ (fun i _ => ?_)
  refine Measurable.mul ?_ (hφ.comp ((measurable_snd).comp (measurable_pi_apply _)))
  have h1 : Measurable (fun ω : ℕ → EuclideanSpace ℝ (Fin d) × ℝ =>
      ((ω 0).1, fun j : Fin n => (ω (j.val + 1)).1)) := by
    refine Measurable.prodMk (measurable_fst.comp (measurable_pi_apply 0)) ?_
    exact measurable_pi_lambda _ (fun j => measurable_fst.comp (measurable_pi_apply _))
  exact (measurable_pi_apply i).comp ((hW n).comp h1)

lemma measurable_condMean (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) {φ : ℝ → ℝ}
    (hφ : Measurable φ) : Measurable (fun x => ∫ y, φ y ∂(κ x)) :=
  (StronglyMeasurable.integral_kernel (κ := κ) hφ.stronglyMeasurable).measurable

lemma measurable_x0 : Measurable (fun ω : ℕ → EuclideanSpace ℝ (Fin d) × ℝ => (ω 0).1) :=
  measurable_fst.comp (measurable_pi_apply 0)

lemma lintegral_x0 (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ]
    {f : EuclideanSpace ℝ (Fin d) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, f (ω 0).1 ∂(pairLaw μ κ) = ∫⁻ x, f x ∂μ := by
  have h0 : (pairLaw μ κ).map (fun ω => ω 0) = μ ⊗ₘ κ := by
    unfold pairLaw; exact Measure.infinitePi_map_eval _ 0
  calc ∫⁻ ω, f (ω 0).1 ∂(pairLaw μ κ)
      = ∫⁻ q, f q.1 ∂((pairLaw μ κ).map (fun ω => ω 0)) :=
        (lintegral_map (hf.comp measurable_fst) (measurable_pi_apply 0)).symm
    _ = ∫⁻ q, f q.1 ∂(μ ⊗ₘ κ) := by rw [h0]
    _ = ∫⁻ x, f x ∂((μ ⊗ₘ κ).map Prod.fst) := (lintegral_map hf measurable_fst).symm
    _ = ∫⁻ x, f x ∂μ := by
        have := Measure.fst_compProd μ κ
        unfold Measure.fst at this
        rw [this]

lemma pairLaw_prob (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ] :
    IsProbabilityMeasure (pairLaw μ κ) := by
  unfold pairLaw; infer_instance

/-- Consistency applied to the transformed response `φ(Y)`. -/
lemma consist_phi (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (hW : MeasurableWeights W) (hcons : IsConsistent μ W)
    (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ] {φ : ℝ → ℝ}
    (hφ : Measurable φ) {s : ℝ} (hs : 1 < s)
    (hmom : ∫⁻ q, ‖φ q.2‖ₑ ^ s ∂(μ ⊗ₘ κ) < ∞) :
    Tendsto (fun n => ∫⁻ ω, ‖wsum W n φ ω - ∫ y, φ y ∂(κ (ω 0).1)‖ₑ ^ s ∂(pairLaw μ κ))
      atTop (𝓝 0) := by
  haveI : IsMarkovKernel (κ.map φ) := Kernel.IsMarkovKernel.map κ hφ
  have hmap : μ ⊗ₘ κ.map φ = (μ ⊗ₘ κ).map (Prod.map id φ) := Measure.compProd_map hφ
  have hT : Measurable (Prod.map (id : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) φ) :=
    measurable_id.prodMap hφ
  have hmom' : ∫⁻ q, ‖q.2‖ₑ ^ s ∂(μ ⊗ₘ κ.map φ) < ∞ := by
    rw [hmap, lintegral_map (by fun_prop) hT]
    simpa using hmom
  have h := hcons (κ.map φ) s hs hmom'
  have hP : pairLaw μ (κ.map φ) =
      (pairLaw μ κ).map (fun ω i => Prod.map id φ (ω i)) := by
    unfold pairLaw
    rw [Measure.infinitePi_map_pi _ (fun _ => hT), hmap]
  have hTT : Measurable (fun (ω : ℕ → EuclideanSpace ℝ (Fin d) × ℝ) (i : ℕ) =>
      Prod.map id φ (ω i)) := measurable_pi_lambda _ (fun i => hT.comp (measurable_pi_apply i))
  have hF : ∀ n, Measurable (fun ω : ℕ → EuclideanSpace ℝ (Fin d) × ℝ =>
      ‖estimate W n ω - regFn (κ.map φ) (ω 0).1‖ₑ ^ s) := by
    intro n
    have h1 : Measurable (estimate W n) := measurable_wsum W hW n measurable_id
    have h2 : Measurable (fun ω : ℕ → EuclideanSpace ℝ (Fin d) × ℝ => regFn (κ.map φ) (ω 0).1) :=
      (measurable_condMean (κ.map φ) measurable_id).comp measurable_x0
    exact ((h1.sub h2).enorm).pow_const s
  simp_rw [hP] at h
  have h' : ∀ n, ∫⁻ ω, ‖estimate W n ω - regFn (κ.map φ) (ω 0).1‖ₑ ^ s
      ∂((pairLaw μ κ).map (fun ω i => Prod.map id φ (ω i))) =
      ∫⁻ ω, ‖wsum W n φ ω - ∫ y, φ y ∂(κ (ω 0).1)‖ₑ ^ s ∂(pairLaw μ κ) := by
    intro n
    rw [lintegral_map (hF n) hTT]
    congr 1
    funext ω
    simp only [estimate, wsum, regFn, Prod.map_fst, Prod.map_snd, id]
    rw [Kernel.map_apply _ hφ, integral_map (f := fun y : ℝ => y) hφ.aemeasurable
      (measurable_id'.aestronglyMeasurable)]
  simpa only [h'] using h

lemma tim_of_lintegral {P : Measure (ℕ → EuclideanSpace ℝ (Fin d) × ℝ)}
    {f : ℕ → (ℕ → EuclideanSpace ℝ (Fin d) × ℝ) → ℝ} (hf : ∀ n, Measurable (f n)) {s : ℝ}
    (hs : 0 < s) (h : Tendsto (fun n => ∫⁻ ω, ‖f n ω‖ₑ ^ s ∂P) atTop (𝓝 0)) :
    TendstoInMeasure P f atTop (fun _ => 0) := by
  refine tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top (p := ENNReal.ofReal s)
    (by simpa using hs) ENNReal.ofReal_ne_top (fun n => (hf n).aestronglyMeasurable)
    aestronglyMeasurable_const ?_
  have hE : ∀ n, eLpNorm (f n - fun _ => (0:ℝ)) (ENNReal.ofReal s) P =
      (∫⁻ ω, ‖f n ω‖ₑ ^ s ∂P) ^ (1 / s) := by
    intro n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hs) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hs.le]
    simp
  simp_rw [hE]
  have h2 := ((ENNReal.continuous_rpow_const (y := 1 / s)).tendsto 0).comp h
  rwa [ENNReal.zero_rpow_of_pos (by positivity : (0:ℝ) < 1 / s)] at h2

lemma indic_integral (ν : Measure ℝ) [IsProbabilityMeasure ν] (q : ℝ) :
    ∫ y, (if y ≤ q then (1:ℝ) else 0) ∂ν = (ν (Set.Iic q)).toReal := by
  have : (fun y : ℝ => if y ≤ q then (1:ℝ) else 0) = (Set.Iic q).indicator 1 := by
    ext y; simp [Set.indicator_apply]
  rw [this, integral_indicator_one measurableSet_Iic]
  rfl

lemma measurable_indic (q : ℝ) : Measurable (fun y : ℝ => if y ≤ q then (1:ℝ) else 0) :=
  Measurable.ite measurableSet_Iic measurable_const measurable_const

/-- Pointwise consistency of the weighted empirical CDF, in probability. -/
lemma estCdf_tim (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (hW : MeasurableWeights W) (hcons : IsConsistent μ W)
    (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ] (q : ℝ) :
    TendstoInMeasure (pairLaw μ κ)
      (fun n ω => estCdf W n ω q - condCdf κ (ω 0).1 q) atTop (fun _ => 0) := by
  have hmom : ∫⁻ z, ‖(fun y : ℝ => if y ≤ q then (1:ℝ) else 0) z.2‖ₑ ^ (2:ℝ) ∂(μ ⊗ₘ κ) < ∞ := by
    calc ∫⁻ z, ‖(fun y : ℝ => if y ≤ q then (1:ℝ) else 0) z.2‖ₑ ^ (2:ℝ) ∂(μ ⊗ₘ κ)
        ≤ ∫⁻ z, 1 ∂(μ ⊗ₘ κ) := by
          refine lintegral_mono (fun z => ?_)
          by_cases h : z.2 ≤ q <;> simp [h]
      _ < ∞ := by simp
  have h := consist_phi μ W hW hcons κ (measurable_indic q) (by norm_num : (1:ℝ) < 2) hmom
  have heq : ∀ n (ω : ℕ → EuclideanSpace ℝ (Fin d) × ℝ),
      wsum W n (fun y : ℝ => if y ≤ q then (1:ℝ) else 0) ω -
        ∫ y, (fun y : ℝ => if y ≤ q then (1:ℝ) else 0) y ∂(κ (ω 0).1) =
      estCdf W n ω q - condCdf κ (ω 0).1 q := by
    intro n ω
    rw [indic_integral]
    rfl
  simp_rw [heq] at h
  refine tim_of_lintegral (fun n => ?_) (by norm_num : (0:ℝ) < 2) h
  have h1 := measurable_wsum W hW n (measurable_indic q)
  have h2 : Measurable (fun x => ∫ y, (fun y : ℝ => if y ≤ q then (1:ℝ) else 0) y ∂(κ x)) :=
    measurable_condMean κ (measurable_indic q)
  have h3 := h1.sub (h2.comp measurable_x0)
  show Measurable (fun ω => estCdf W n ω q - condCdf κ (ω 0).1 q)
  rw [← funext (heq n)]
  exact h3

section Quant

lemma condCdf_eq_cdf (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ]
    (x : EuclideanSpace ℝ (Fin d)) (y : ℝ) : condCdf κ x y = cdf (κ x) y := by
  rw [cdf_eq_real]; rfl

lemma condCdf_mono (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ]
    (x : EuclideanSpace ℝ (Fin d)) : Monotone (condCdf κ x) := by
  intro a b h; rw [condCdf_eq_cdf, condCdf_eq_cdf]; exact monotone_cdf _ h

lemma measurable_condCdf (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) (q : ℝ) :
    Measurable (fun x => condCdf κ x q) :=
  (κ.measurable_coe measurableSet_Iic).ennreal_toReal

lemma condCdf_ev_lt (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ]
    (x : EuclideanSpace ℝ (Fin d)) {p : ℝ} (hp0 : 0 < p) :
    ∃ b, ∀ y ≤ b, condCdf κ x y < p := by
  have := (tendsto_order.1 (tendsto_cdf_atBot (μ := κ x))).2 p hp0
  rcases Filter.eventually_atBot.1 this with ⟨b, hb⟩
  exact ⟨b, fun y hy => by rw [condCdf_eq_cdf]; exact hb y hy⟩

lemma condCdf_ev_gt (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ]
    (x : EuclideanSpace ℝ (Fin d)) {p : ℝ} (hp1 : p < 1) :
    ∃ b, ∀ y ≥ b, p < condCdf κ x y := by
  have := (tendsto_order.1 (tendsto_cdf_atTop (μ := κ x))).1 p hp1
  rcases Filter.eventually_atTop.1 this with ⟨b, hb⟩
  exact ⟨b, fun y hy => by rw [condCdf_eq_cdf]; exact hb y hy⟩

lemma lowerSet_bdd (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ]
    (x : EuclideanSpace ℝ (Fin d)) {p : ℝ} (hp0 : 0 < p) :
    BddBelow {y | p ≤ condCdf κ x y} := by
  obtain ⟨b, hb⟩ := condCdf_ev_lt κ x hp0
  refine ⟨b, fun y hy => ?_⟩
  by_contra h; rw [not_le] at h
  exact absurd (show p ≤ condCdf κ x y from hy) (not_le.2 (hb y h.le))

lemma lowerSet_ne (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ]
    (x : EuclideanSpace ℝ (Fin d)) {p : ℝ} (hp1 : p < 1) :
    {y | p ≤ condCdf κ x y}.Nonempty := by
  obtain ⟨b, hb⟩ := condCdf_ev_gt κ x hp1
  exact ⟨b, (hb b le_rfl).le⟩

lemma lt_lowerQ (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ]
    (x : EuclideanSpace ℝ (Fin d)) {p q : ℝ} (hp0 : 0 < p) (h : q < lowerQ κ p x) :
    condCdf κ x q < p := by
  by_contra h'; rw [not_lt] at h'
  exact absurd (csInf_le (lowerSet_bdd κ x hp0) h') (not_le.2 h)

lemma lowerQ_lt (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ]
    (x : EuclideanSpace ℝ (Fin d)) {p q : ℝ} (hp1 : p < 1) (h : lowerQ κ p x < q) :
    p ≤ condCdf κ x q := by
  obtain ⟨y, hy, hyq⟩ := exists_lt_of_csInf_lt (lowerSet_ne κ x hp1) h
  exact le_trans hy (condCdf_mono κ x hyq.le)

lemma upperSet_bdd (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ]
    (x : EuclideanSpace ℝ (Fin d)) {p : ℝ} (hp1 : p < 1) :
    BddAbove {y | condCdf κ x y ≤ p} := by
  obtain ⟨b, hb⟩ := condCdf_ev_gt κ x hp1
  refine ⟨b, fun y hy => ?_⟩
  by_contra h; rw [not_le] at h
  exact absurd (show condCdf κ x y ≤ p from hy) (not_le.2 (hb y h.le))

lemma upperSet_ne (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ]
    (x : EuclideanSpace ℝ (Fin d)) {p : ℝ} (hp0 : 0 < p) :
    {y | condCdf κ x y ≤ p}.Nonempty := by
  obtain ⟨b, hb⟩ := condCdf_ev_lt κ x hp0
  exact ⟨b, (hb b le_rfl).le⟩

lemma upperQ_lt (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ]
    (x : EuclideanSpace ℝ (Fin d)) {p q : ℝ} (hp1 : p < 1) (h : upperQ κ p x < q) :
    p < condCdf κ x q := by
  by_contra h'; rw [not_lt] at h'
  exact absurd (le_csSup (upperSet_bdd κ x hp1) h') (not_le.2 h)

lemma lt_upperQ (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ]
    (x : EuclideanSpace ℝ (Fin d)) {p q : ℝ} (hp0 : 0 < p) (h : q < upperQ κ p x) :
    condCdf κ x q ≤ p := by
  obtain ⟨y, hy, hyq⟩ := exists_lt_of_lt_csSup (upperSet_ne κ x hp0) h
  exact le_trans (condCdf_mono κ x hyq.le) hy

end Quant

section Est

lemma estCdf_mono (W : WeightSeq d) (hP : ProbWeights W) {n : ℕ} (hn : 1 ≤ n)
    (ω : ℕ → EuclideanSpace ℝ (Fin d) × ℝ) : Monotone (estCdf W n ω) := by
  intro a b hab
  unfold estCdf
  refine Finset.sum_le_sum (fun i _ => ?_)
  refine mul_le_mul_of_nonneg_left ?_ ((hP n hn _ _).1 i)
  by_cases h : (ω (i.val + 1)).2 ≤ a
  · simp [h, h.trans hab]
  · simp only [h, if_false]; split_ifs <;> norm_num

lemma estCdf_big (W : WeightSeq d) (hP : ProbWeights W) {n : ℕ} (hn : 1 ≤ n)
    (ω : ℕ → EuclideanSpace ℝ (Fin d) × ℝ) (y : ℝ)
    (hy : ∀ i : Fin n, (ω (i.val + 1)).2 ≤ y) : estCdf W n ω y = 1 := by
  unfold estCdf
  simp only [hy, if_true, mul_one]
  exact (hP n hn _ _).2

lemma estCdf_small (W : WeightSeq d) {n : ℕ}
    (ω : ℕ → EuclideanSpace ℝ (Fin d) × ℝ) (y : ℝ)
    (hy : ∀ i : Fin n, y < (ω (i.val + 1)).2) : estCdf W n ω y = 0 := by
  unfold estCdf
  exact Finset.sum_eq_zero (fun i _ => by simp [not_le.2 (hy i)])

lemma abs_le_B {n : ℕ} (ω : ℕ → EuclideanSpace ℝ (Fin d) × ℝ) (i : Fin n) :
    |(ω (i.val + 1)).2| ≤ ∑ j : Fin n, |(ω (j.val + 1)).2| :=
  Finset.single_le_sum (f := fun j : Fin n => |(ω (j.val + 1)).2|)
    (fun j _ => abs_nonneg _) (Finset.mem_univ i)

lemma estLowerQ_lt (W : WeightSeq d) (hP : ProbWeights W) {n : ℕ} (hn : 1 ≤ n)
    (ω : ℕ → EuclideanSpace ℝ (Fin d) × ℝ) {p q : ℝ} (hp1 : p < 1)
    (h : estLowerQ W n p ω < q) : p ≤ estCdf W n ω q := by
  have hne : {y | p ≤ estCdf W n ω y}.Nonempty := by
    refine ⟨∑ j : Fin n, |(ω (j.val + 1)).2|, ?_⟩
    show p ≤ estCdf W n ω _
    rw [estCdf_big W hP hn ω _ (fun i => (le_abs_self _).trans (abs_le_B ω i))]
    exact hp1.le
  obtain ⟨y, hy, hyq⟩ := exists_lt_of_csInf_lt hne h
  exact le_trans hy (estCdf_mono W hP hn ω hyq.le)

lemma lt_estUpperQ (W : WeightSeq d) (hP : ProbWeights W) {n : ℕ} (hn : 1 ≤ n)
    (ω : ℕ → EuclideanSpace ℝ (Fin d) × ℝ) {p q : ℝ} (hp0 : 0 < p)
    (h : q < estUpperQ W n p ω) : estCdf W n ω q ≤ p := by
  have hne : {y | estCdf W n ω y ≤ p}.Nonempty := by
    refine ⟨-(∑ j : Fin n, |(ω (j.val + 1)).2|) - 1, ?_⟩
    show estCdf W n ω _ ≤ p
    rw [estCdf_small W ω _ (fun i => by
      have h1 := abs_le_B ω i
      have h2 := neg_abs_le (ω (i.val + 1)).2
      linarith)]
    exact hp0.le
  obtain ⟨y, hy, hyq⟩ := exists_lt_of_lt_csSup hne h
  exact le_trans (estCdf_mono W hP hn ω hyq.le) hy

end Est

section Limits

variable {Ω : Type*} [MeasurableSpace Ω]

lemma tendsto_meas_antitone {P : Measure Ω} [IsFiniteMeasure P] {s : ℕ → Set Ω}
    (hs : ∀ m, MeasurableSet (s m)) (ha : Antitone s) (he : ∀ ω, ∃ m, ω ∉ s m) :
    Tendsto (fun m => P (s m)) atTop (𝓝 0) := by
  have h := tendsto_measure_iInter_atTop (μ := P) (fun m => (hs m).nullMeasurableSet) ha
    ⟨0, measure_ne_top _ _⟩
  have he' : (⋂ m, s m) = ∅ := by
    ext ω; simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
    exact he ω
  rw [he', measure_empty] at h
  exact h

lemma gap_lemma {P : Measure Ω} [IsFiniteMeasure P] {D : ℕ → Ω → ℝ}
    (hD : TendstoInMeasure P D atTop (fun _ => 0)) {g : Ω → ℝ} (hg : Measurable g) :
    Tendsto (fun n => P {ω | 0 < g ω ∧ g ω ≤ |D n ω|}) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro γ hγ
  have hA : Tendsto (fun m : ℕ => P {ω | 0 < g ω ∧ g ω < 1 / ((m:ℝ) + 1)}) atTop (𝓝 0) := by
    refine tendsto_meas_antitone (fun m => ?_) ?_ ?_
    · exact (measurableSet_lt measurable_const hg).inter (measurableSet_lt hg measurable_const)
    · intro a b hab ω hω
      refine ⟨hω.1, lt_of_lt_of_le hω.2 ?_⟩
      gcongr
    · intro ω
      by_cases h0 : 0 < g ω
      · obtain ⟨m, hm⟩ := exists_nat_one_div_lt h0
        exact ⟨m, fun h => absurd h.2 (not_lt.2 hm.le)⟩
      · exact ⟨0, fun h => h0 h.1⟩
  have hγ2 : (0:ℝ≥0∞) < γ / 2 := ENNReal.half_pos hγ.ne'
  obtain ⟨m, hm⟩ := ((ENNReal.tendsto_nhds_zero.1 hA) (γ / 2) hγ2).exists
  have hpos : (0:ℝ) < 1 / ((m:ℝ) + 1) := by positivity
  have hB := (tendstoInMeasure_iff_norm.1 hD) (1 / ((m:ℝ) + 1)) hpos
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 hB) (γ / 2) hγ2] with n hn
  calc P {ω | 0 < g ω ∧ g ω ≤ |D n ω|}
      ≤ P ({ω | 0 < g ω ∧ g ω < 1 / ((m:ℝ) + 1)} ∪ {ω | 1 / ((m:ℝ) + 1) ≤ ‖D n ω - 0‖}) := by
        refine measure_mono (fun ω hω => ?_)
        by_cases h : g ω < 1 / ((m:ℝ) + 1)
        · exact Or.inl ⟨hω.1, h⟩
        · right
          show 1 / ((m:ℝ) + 1) ≤ ‖D n ω - 0‖
          rw [sub_zero, Real.norm_eq_abs]
          exact (not_lt.1 h).trans hω.2
    _ ≤ P {ω | 0 < g ω ∧ g ω < 1 / ((m:ℝ) + 1)} + P {ω | 1 / ((m:ℝ) + 1) ≤ ‖D n ω - 0‖} :=
        measure_union_le _ _
    _ ≤ γ / 2 + γ / 2 := add_le_add hm hn
    _ = γ := ENNReal.add_halves γ

lemma tendsto_of_cover {P : Measure Ω} [IsFiniteMeasure P] {E : ℕ → Set Ω}
    (h : ∀ γ : ℝ≥0∞, 0 < γ → ∃ (C : Set Ω) (K : Finset ℤ) (B : ℤ → ℕ → Set Ω), P C ≤ γ ∧
      (∀ k ∈ K, Tendsto (fun n => P (B k n)) atTop (𝓝 0)) ∧
      ∀ᶠ n in atTop, E n ⊆ C ∪ ⋃ k ∈ K, B k n) :
    Tendsto (fun n => P (E n)) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro γ hγ
  have hγ2 : (0:ℝ≥0∞) < γ / 2 := ENNReal.half_pos hγ.ne'
  obtain ⟨C, K, B, hC, hB, hcov⟩ := h (γ / 2) hγ2
  have hsum : Tendsto (fun n => ∑ k ∈ K, P (B k n)) atTop (𝓝 0) := by
    simpa using tendsto_finset_sum K hB
  filter_upwards [hcov, (ENNReal.tendsto_nhds_zero.1 hsum) (γ / 2) hγ2] with n h1 h2
  calc P (E n) ≤ P (C ∪ ⋃ k ∈ K, B k n) := measure_mono h1
    _ ≤ P C + P (⋃ k ∈ K, B k n) := measure_union_le _ _
    _ ≤ P C + ∑ k ∈ K, P (B k n) := add_le_add le_rfl (measure_biUnion_finset_le K _)
    _ ≤ γ / 2 + γ / 2 := add_le_add hC h2
    _ = γ := ENNReal.add_halves γ

end Limits

section InProb

/-- (9): `(L̂ₙ − L)⁻ → 0` in probability. -/
lemma part9 (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (hW : MeasurableWeights W) (hP : ProbWeights W) (hcons : IsConsistent μ W)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ] :
    TendstoInMeasure (pairLaw μ κ)
      (fun n ω => max (-(estLowerQ W n p ω - lowerQ κ p (ω 0).1)) 0) atTop (fun _ => 0) := by
  haveI := pairLaw_prob μ κ
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  apply tendsto_of_cover
  intro γ hγ
  set δ : ℝ := ε / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  let C : ℕ → Set (ℕ → EuclideanSpace ℝ (Fin d) × ℝ) := fun M =>
    {ω | condCdf κ (ω 0).1 M < p} ∪ {ω | p ≤ condCdf κ (ω 0).1 (-(M:ℝ))}
  have hC : Tendsto (fun M => pairLaw μ κ (C M)) atTop (𝓝 0) := by
    refine tendsto_meas_antitone (fun M => ?_) ?_ ?_
    · exact (measurableSet_lt ((measurable_condCdf κ _).comp measurable_x0) measurable_const).union
        (measurableSet_le measurable_const ((measurable_condCdf κ _).comp measurable_x0))
    · intro a b hab ω hω
      rcases hω with h | h
      · left
        exact lt_of_le_of_lt (condCdf_mono κ _ (by exact_mod_cast hab)) h
      · right
        refine le_trans h (condCdf_mono κ _ ?_)
        have : (a:ℝ) ≤ b := by exact_mod_cast hab
        linarith
    · intro ω
      obtain ⟨b1, hb1⟩ := condCdf_ev_gt κ (ω 0).1 hp1
      obtain ⟨b2, hb2⟩ := condCdf_ev_lt κ (ω 0).1 hp0
      obtain ⟨m, hm⟩ := exists_nat_ge (max b1 (-b2))
      refine ⟨m, fun h => ?_⟩
      rcases h with h | h
      · exact absurd h (not_lt.2 (hb1 m (le_trans (le_max_left _ _) hm)).le)
      · have : -(m:ℝ) ≤ b2 := by have := le_trans (le_max_right b1 (-b2)) hm; linarith
        exact absurd h (not_le.2 (hb2 _ this))
  obtain ⟨M, hM⟩ := ((ENNReal.tendsto_nhds_zero.1 hC) γ hγ).exists
  let B : ℤ → ℕ → Set (ℕ → EuclideanSpace ℝ (Fin d) × ℝ) := fun k n =>
    {ω | 0 < p - condCdf κ (ω 0).1 (k * δ) ∧
      p - condCdf κ (ω 0).1 (k * δ) ≤ |estCdf W n ω (k * δ) - condCdf κ (ω 0).1 (k * δ)|}
  refine ⟨C M, Finset.Icc (⌊(-(M:ℝ) - ε) / δ⌋) (⌊(M:ℝ) / δ⌋ + 1), B, hM, fun k _ => ?_, ?_⟩
  · exact gap_lemma (estCdf_tim μ W hW hcons κ (k * δ))
      (measurable_const.sub ((measurable_condCdf κ _).comp measurable_x0))
  filter_upwards [eventually_ge_atTop 1] with n hn ω hω
  simp only [Set.mem_setOf_eq, sub_zero, Real.norm_eq_abs] at hω
  by_cases hCω : ω ∈ C M
  · exact Or.inl hCω
  right
  simp only [C, Set.mem_union, Set.mem_setOf_eq, not_or, not_lt, not_le] at hCω
  set L := lowerQ κ p (ω 0).1 with hL
  have hLM : L ≤ M := by
    by_contra h; rw [not_le] at h
    exact absurd (lt_lowerQ κ _ hp0 h) (not_lt.2 hCω.1)
  have hLm : -(M:ℝ) ≤ L := by
    by_contra h; rw [not_le] at h
    exact absurd (lowerQ_lt κ _ hp1 h) (not_le.2 hCω.2)
  have hgap : estLowerQ W n p ω ≤ L - ε := by
    have h0 : ε ≤ max (-(estLowerQ W n p ω - L)) 0 := by
      rw [abs_of_nonneg (le_max_right _ _)] at hω; exact hω
    rcases le_total (-(estLowerQ W n p ω - L)) 0 with h | h
    · rw [max_eq_right h] at h0; linarith
    · rw [max_eq_left h] at h0; linarith
  set k : ℤ := ⌊(L - ε) / δ⌋ + 1 with hk
  have hk1 : L - ε < k * δ := by
    have := Int.lt_floor_add_one ((L - ε) / δ)
    rw [hk]; push_cast
    have := (div_lt_iff₀ hδ0).1 this
    linarith
  have hk2 : (k:ℝ) * δ < L := by
    have := Int.floor_le ((L - ε) / δ)
    rw [hk]; push_cast
    have := (le_div_iff₀ hδ0).1 this
    nlinarith
  have hkmem : k ∈ Finset.Icc (⌊(-(M:ℝ) - ε) / δ⌋) (⌊(M:ℝ) / δ⌋ + 1) := by
    rw [Finset.mem_Icc]
    constructor
    · have : ⌊(-(M:ℝ) - ε) / δ⌋ ≤ ⌊(L - ε) / δ⌋ :=
        Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hδ0.le)
      omega
    · have : ⌊(L - ε) / δ⌋ ≤ ⌊(M:ℝ) / δ⌋ :=
        Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hδ0.le)
      omega
  simp only [Set.mem_iUnion]
  refine ⟨k, hkmem, ?_⟩
  have hF := lt_lowerQ κ (ω 0).1 hp0 hk2
  have hFh := estLowerQ_lt W hP hn ω hp1 (lt_of_le_of_lt hgap hk1)
  refine ⟨by linarith, ?_⟩
  exact le_trans (by linarith) (le_abs_self _)

/-- (10): `(Ûₙ − U)⁺ → 0` in probability. -/
lemma part10 (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (hW : MeasurableWeights W) (hP : ProbWeights W) (hcons : IsConsistent μ W)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ] :
    TendstoInMeasure (pairLaw μ κ)
      (fun n ω => max (estUpperQ W n p ω - upperQ κ p (ω 0).1) 0) atTop (fun _ => 0) := by
  haveI := pairLaw_prob μ κ
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  apply tendsto_of_cover
  intro γ hγ
  set δ : ℝ := ε / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  let C : ℕ → Set (ℕ → EuclideanSpace ℝ (Fin d) × ℝ) := fun M =>
    {ω | condCdf κ (ω 0).1 M ≤ p} ∪ {ω | p < condCdf κ (ω 0).1 (-(M:ℝ))}
  have hC : Tendsto (fun M => pairLaw μ κ (C M)) atTop (𝓝 0) := by
    refine tendsto_meas_antitone (fun M => ?_) ?_ ?_
    · exact (measurableSet_le ((measurable_condCdf κ _).comp measurable_x0) measurable_const).union
        (measurableSet_lt measurable_const ((measurable_condCdf κ _).comp measurable_x0))
    · intro a b hab ω hω
      rcases hω with h | h
      · left
        exact le_trans (condCdf_mono κ _ (by exact_mod_cast hab)) h
      · right
        refine lt_of_lt_of_le h (condCdf_mono κ _ ?_)
        have : (a:ℝ) ≤ b := by exact_mod_cast hab
        linarith
    · intro ω
      obtain ⟨b1, hb1⟩ := condCdf_ev_gt κ (ω 0).1 hp1
      obtain ⟨b2, hb2⟩ := condCdf_ev_lt κ (ω 0).1 hp0
      obtain ⟨m, hm⟩ := exists_nat_ge (max b1 (-b2))
      refine ⟨m, fun h => ?_⟩
      rcases h with h | h
      · exact absurd h (not_le.2 (hb1 m (le_trans (le_max_left _ _) hm)))
      · have : -(m:ℝ) ≤ b2 := by have := le_trans (le_max_right b1 (-b2)) hm; linarith
        exact absurd h (not_lt.2 (hb2 _ this).le)
  obtain ⟨M, hM⟩ := ((ENNReal.tendsto_nhds_zero.1 hC) γ hγ).exists
  let B : ℤ → ℕ → Set (ℕ → EuclideanSpace ℝ (Fin d) × ℝ) := fun k n =>
    {ω | 0 < condCdf κ (ω 0).1 (k * δ) - p ∧
      condCdf κ (ω 0).1 (k * δ) - p ≤ |estCdf W n ω (k * δ) - condCdf κ (ω 0).1 (k * δ)|}
  refine ⟨C M, Finset.Icc (⌊(-(M:ℝ) - ε) / δ⌋) (⌊(M:ℝ) / δ⌋ + 1), B, hM, fun k _ => ?_, ?_⟩
  · exact gap_lemma (estCdf_tim μ W hW hcons κ (k * δ))
      (((measurable_condCdf κ _).comp measurable_x0).sub measurable_const)
  filter_upwards [eventually_ge_atTop 1] with n hn ω hω
  simp only [Set.mem_setOf_eq, sub_zero, Real.norm_eq_abs] at hω
  by_cases hCω : ω ∈ C M
  · exact Or.inl hCω
  right
  simp only [C, Set.mem_union, Set.mem_setOf_eq, not_or, not_lt, not_le] at hCω
  set U := upperQ κ p (ω 0).1 with hU
  have hUM : U ≤ M := by
    by_contra h; rw [not_le] at h
    exact absurd (lt_upperQ κ _ hp0 h) (not_le.2 hCω.1)
  have hUm : -(M:ℝ) ≤ U := by
    by_contra h; rw [not_le] at h
    exact absurd (upperQ_lt κ _ hp1 h) (not_lt.2 hCω.2)
  have hgap : U + ε ≤ estUpperQ W n p ω := by
    have h0 : ε ≤ max (estUpperQ W n p ω - U) 0 := by
      rw [abs_of_nonneg (le_max_right _ _)] at hω; exact hω
    rcases le_total (estUpperQ W n p ω - U) 0 with h | h
    · rw [max_eq_right h] at h0; linarith
    · rw [max_eq_left h] at h0; linarith
  set k : ℤ := ⌊U / δ⌋ + 1 with hk
  have hk1 : U < k * δ := by
    have := Int.lt_floor_add_one (U / δ)
    rw [hk]; push_cast
    have := (div_lt_iff₀ hδ0).1 this
    linarith
  have hk2 : (k:ℝ) * δ < U + ε := by
    have := Int.floor_le (U / δ)
    rw [hk]; push_cast
    have := (le_div_iff₀ hδ0).1 this
    nlinarith
  have hkmem : k ∈ Finset.Icc (⌊(-(M:ℝ) - ε) / δ⌋) (⌊(M:ℝ) / δ⌋ + 1) := by
    rw [Finset.mem_Icc]
    constructor
    · have : ⌊(-(M:ℝ) - ε) / δ⌋ ≤ ⌊U / δ⌋ :=
        Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hδ0.le)
      omega
    · have : ⌊U / δ⌋ ≤ ⌊(M:ℝ) / δ⌋ :=
        Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hδ0.le)
      omega
  simp only [Set.mem_iUnion]
  refine ⟨k, hkmem, ?_⟩
  have hF := upperQ_lt κ (ω 0).1 hp1 hk1
  have hFh := lt_estUpperQ W hP hn ω hp0 (lt_of_lt_of_le hk2 hgap)
  refine ⟨by linarith, ?_⟩
  have hab := neg_le_abs (estCdf W n ω (k * δ) - condCdf κ (ω 0).1 (k * δ))
  linarith

end InProb

section LrTools

lemma le_of_forall_lt_rpow {a : ℝ} {c B : ℝ≥0∞} {s : ℝ} (hs : 0 < s) (hc : c ≠ ∞)
    (h : ∀ t : ℝ, 0 < t → t < a → c * ENNReal.ofReal t ^ s ≤ B) :
    c * ENNReal.ofReal a ^ s ≤ B := by
  rcases le_or_gt a 0 with ha | ha
  · rw [ENNReal.ofReal_of_nonpos ha, ENNReal.zero_rpow_of_pos hs, mul_zero]; exact bot_le
  · have ht : Tendsto (fun t : ℝ => c * ENNReal.ofReal t ^ s) (𝓝[<] a)
        (𝓝 (c * ENNReal.ofReal a ^ s)) := by
      have h1 : Tendsto (fun t : ℝ => ENNReal.ofReal t ^ s) (𝓝 a) (𝓝 (ENNReal.ofReal a ^ s)) :=
        ((ENNReal.continuous_rpow_const).comp ENNReal.continuous_ofReal).tendsto a
      exact (ENNReal.Tendsto.const_mul h1 (Or.inr hc)).mono_left nhdsWithin_le_nhds
    refine le_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsLT ha] with t ht
    exact h t ht.1 ht.2

lemma combine {a b Z m r : ℝ} (hr : 1 ≤ r) {c1 c2 K : ℝ≥0∞} (hc1 : c1 ≠ 0) (hc1' : c1 ≠ ∞)
    (hc2 : c2 ≠ 0) (hc2' : c2 ≠ ∞)
    (hA : c1 * ENNReal.ofReal a ^ r ≤ K) (hB : c2 * ENNReal.ofReal b ^ (r / 2) ≤ ENNReal.ofReal Z) :
    ENNReal.ofReal (a + b) ^ r ≤ (2 ^ (r - 1) / c1) * K +
      (2 ^ (r - 1) * 2 / c2 ^ (2:ℝ)) * ‖m‖ₑ ^ (2:ℝ) +
      (2 ^ (r - 1) * 2 / c2 ^ (2:ℝ)) * ‖Z - m‖ₑ ^ (2:ℝ) := by
  have hr0 : 0 ≤ r := by linarith
  have h1 : ENNReal.ofReal (a + b) ^ r ≤ 2 ^ (r - 1) * (ENNReal.ofReal a ^ r + ENNReal.ofReal b ^ r) :=
    (ENNReal.rpow_le_rpow ENNReal.ofReal_add_le hr0).trans
      (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hr)
  have hA' : ENNReal.ofReal a ^ r ≤ K / c1 := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hc1) (Or.inl hc1'), mul_comm]; exact hA
  have hB1 : ENNReal.ofReal b ^ (r / 2) ≤ ENNReal.ofReal Z / c2 := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hc2) (Or.inl hc2'), mul_comm]; exact hB
  have hZ : ENNReal.ofReal Z ≤ ‖Z - m‖ₑ + ‖m‖ₑ := by
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
    refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
    linarith [le_abs_self (Z - m), le_abs_self m]
  have hB2 : ENNReal.ofReal b ^ r ≤ (ENNReal.ofReal Z / c2) ^ (2:ℝ) := by
    have : ENNReal.ofReal b ^ r = (ENNReal.ofReal b ^ (r / 2)) ^ (2:ℝ) := by
      rw [← ENNReal.rpow_mul]; congr 1; ring
    rw [this]; exact ENNReal.rpow_le_rpow hB1 (by norm_num)
  have hZ2 : ENNReal.ofReal Z ^ (2:ℝ) ≤ 2 * (‖Z - m‖ₑ ^ (2:ℝ) + ‖m‖ₑ ^ (2:ℝ)) := by
    have := (ENNReal.rpow_le_rpow hZ (by norm_num : (0:ℝ) ≤ 2)).trans
      (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ (by norm_num : (1:ℝ) ≤ 2))
    rwa [show (2:ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one] at this
  have hB3 : (ENNReal.ofReal Z / c2) ^ (2:ℝ) ≤
      (2 * (‖Z - m‖ₑ ^ (2:ℝ) + ‖m‖ₑ ^ (2:ℝ))) / c2 ^ (2:ℝ) := by
    rw [ENNReal.div_rpow_of_nonneg _ _ (by norm_num)]
    exact ENNReal.div_le_div_right hZ2 _
  calc ENNReal.ofReal (a + b) ^ r
      ≤ 2 ^ (r - 1) * (ENNReal.ofReal a ^ r + ENNReal.ofReal b ^ r) := h1
    _ ≤ 2 ^ (r - 1) * (K / c1 + (2 * (‖Z - m‖ₑ ^ (2:ℝ) + ‖m‖ₑ ^ (2:ℝ))) / c2 ^ (2:ℝ)) := by
        gcongr
        exact hB2.trans hB3
    _ = (2 ^ (r - 1) / c1) * K + (2 ^ (r - 1) * 2 / c2 ^ (2:ℝ)) * ‖m‖ₑ ^ (2:ℝ) +
          (2 ^ (r - 1) * 2 / c2 ^ (2:ℝ)) * ‖Z - m‖ₑ ^ (2:ℝ) := by
        simp only [div_eq_mul_inv]; ring

lemma enorm_integral_sq_le (ν : Measure ℝ) [IsProbabilityMeasure ν] {φ : ℝ → ℝ}
    (hφ : Measurable φ) :
    ‖∫ y, φ y ∂ν‖ₑ ^ (2:ℝ) ≤ ∫⁻ y, ‖φ y‖ₑ ^ (2:ℝ) ∂ν := by
  have h1 := enorm_integral_le_lintegral_enorm (μ := ν) φ
  have h2 : eLpNorm φ 1 ν ≤ eLpNorm φ 2 ν :=
    eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) hφ.aestronglyMeasurable
  rw [eLpNorm_one_eq_lintegral_enorm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)] at h2
  have h3 : ((2:ℝ≥0∞).toReal) = 2 := by norm_num
  rw [h3] at h2
  calc ‖∫ y, φ y ∂ν‖ₑ ^ (2:ℝ) ≤ (∫⁻ y, ‖φ y‖ₑ ∂ν) ^ (2:ℝ) :=
        ENNReal.rpow_le_rpow h1 (by norm_num)
    _ ≤ ((∫⁻ y, ‖φ y‖ₑ ^ (2:ℝ) ∂ν) ^ (1 / (2:ℝ))) ^ (2:ℝ) :=
        ENNReal.rpow_le_rpow h2 (by norm_num)
    _ = ∫⁻ y, ‖φ y‖ₑ ^ (2:ℝ) ∂ν := by
        rw [← ENNReal.rpow_mul]; norm_num

lemma dct_tim {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {f : ℕ → Ω → ℝ} {r : ℝ} (hr : 0 < r)
    (hf : TendstoInMeasure P f atTop (fun _ => 0)) {G : Ω → ℝ≥0∞} (hG : Measurable G)
    (hGi : ∫⁻ ω, G ω ∂P ≠ ∞)
    {δ : ℕ → Ω → ℝ≥0∞} (hδm : ∀ n, Measurable (δ n))
    (hδ : Tendsto (fun n => ∫⁻ ω, δ n ω ∂P) atTop (𝓝 0))
    (hdom : ∀ᶠ n in atTop, ∀ ω, ‖f n ω‖ₑ ^ r ≤ G ω + δ n ω) :
    Tendsto (fun n => ∫⁻ ω, ‖f n ω‖ₑ ^ r ∂P) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro γ hγ
  have hγ2 : (0:ℝ≥0∞) < γ / 2 := ENNReal.half_pos hγ.ne'
  have hγ4 : (0:ℝ≥0∞) < γ / 2 / 2 := ENNReal.half_pos hγ2.ne'
  have ht : Tendsto (fun e : ℝ => ENNReal.ofReal e ^ r) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun e : ℝ => ENNReal.ofReal e ^ r) (𝓝 0) (𝓝 (ENNReal.ofReal 0 ^ r)) :=
      ((ENNReal.continuous_rpow_const).comp ENNReal.continuous_ofReal).tendsto 0
    rw [ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hr] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  obtain ⟨e, he1, he0⟩ :=
    (((ENNReal.tendsto_nhds_zero.1 ht) (γ / 2) hγ2).and self_mem_nhdsWithin).exists
  have he0' : (0:ℝ) < e := he0
  let A : ℕ → Set Ω := fun n => {ω | e ≤ ‖f n ω - 0‖}
  have hA : Tendsto (fun n => P (A n)) atTop (𝓝 0) := (tendstoInMeasure_iff_norm.1 hf) e he0'
  let S : ℕ → Set Ω := fun n => toMeasurable P (A n)
  have hS : Tendsto (P ∘ S) atTop (𝓝 0) := by
    simpa [S, Function.comp_def, measure_toMeasurable] using hA
  have hSG := tendsto_setLIntegral_zero hGi hS
  filter_upwards [hdom, (ENNReal.tendsto_nhds_zero.1 hSG) (γ / 2 / 2) hγ4,
    (ENNReal.tendsto_nhds_zero.1 hδ) (γ / 2 / 2) hγ4] with n hn h1 h2
  have hpt : ∀ ω, ‖f n ω‖ₑ ^ r ≤ ENNReal.ofReal e ^ r + ((S n).indicator G ω + δ n ω) := by
    intro ω
    by_cases hω : ω ∈ A n
    · have : ω ∈ S n := subset_toMeasurable P (A n) hω
      rw [Set.indicator_of_mem this]
      exact (hn ω).trans le_add_self
    · have hlt : ‖f n ω‖ < e := by
        simp only [A, Set.mem_setOf_eq, sub_zero, not_le] at hω; exact hω
      have : ‖f n ω‖ₑ ≤ ENNReal.ofReal e := by
        rw [← ofReal_norm_eq_enorm]; exact ENNReal.ofReal_le_ofReal hlt.le
      exact (ENNReal.rpow_le_rpow this hr.le).trans le_self_add
  have hSm : MeasurableSet (S n) := measurableSet_toMeasurable _ _
  calc ∫⁻ ω, ‖f n ω‖ₑ ^ r ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal e ^ r + ((S n).indicator G ω + δ n ω)) ∂P := lintegral_mono hpt
    _ = ENNReal.ofReal e ^ r + ((∫⁻ ω in S n, G ω ∂P) + ∫⁻ ω, δ n ω ∂P) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_add_left (hG.indicator hSm), lintegral_indicator hSm]
    _ ≤ γ / 2 + (γ / 2 / 2 + γ / 2 / 2) := by gcongr
    _ = γ := by rw [ENNReal.add_halves, ENNReal.add_halves]

end LrTools

section Bounds

lemma enorm_max0 (x : ℝ) : ‖max x 0‖ₑ = ENNReal.ofReal x := by
  rw [Real.enorm_eq_ofReal (le_max_right _ _)]
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
  · rw [max_eq_left h]

lemma measurable_ofReal_rpow {ψ : ℝ → ℝ} (hψ : Measurable ψ) (r : ℝ) :
    Measurable (fun y => ENNReal.ofReal (ψ y) ^ r) :=
  (ENNReal.measurable_ofReal.comp hψ).pow_const r

lemma bound_L (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ]
    (x : EuclideanSpace ℝ (Fin d)) {p r : ℝ} (hp0 : 0 < p) (hr : 0 < r) :
    ENNReal.ofReal (1 - p) * ENNReal.ofReal (lowerQ κ p x) ^ r ≤
      ∫⁻ y, ENNReal.ofReal y ^ r ∂(κ x) := by
  refine le_of_forall_lt_rpow hr ENNReal.ofReal_ne_top (fun t ht0 htL => ?_)
  have hF := lt_lowerQ κ x hp0 htL
  have hI : ENNReal.ofReal (1 - p) ≤ κ x (Set.Ioi t) := by
    rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic]
    have h1 : κ x (Set.Iic t) = ENNReal.ofReal (condCdf κ x t) := by
      unfold condCdf; rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
    have h2 : 0 ≤ condCdf κ x t := ENNReal.toReal_nonneg
    rw [h1, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ h2]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  calc ENNReal.ofReal (1 - p) * ENNReal.ofReal t ^ r
      ≤ κ x (Set.Ioi t) * ENNReal.ofReal t ^ r := by gcongr
    _ = ∫⁻ y in Set.Ioi t, ENNReal.ofReal t ^ r ∂(κ x) := by rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ y in Set.Ioi t, ENNReal.ofReal y ^ r ∂(κ x) :=
        setLIntegral_mono (measurable_ofReal_rpow measurable_id r)
          (fun y hy => ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (le_of_lt hy)) hr.le)
    _ ≤ ∫⁻ y, ENNReal.ofReal y ^ r ∂(κ x) := setLIntegral_le_lintegral _ _

lemma bound_U (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ]
    (x : EuclideanSpace ℝ (Fin d)) {p r : ℝ} (hp1 : p < 1) (hr : 0 < r) :
    ENNReal.ofReal p * ENNReal.ofReal (-upperQ κ p x) ^ r ≤
      ∫⁻ y, ENNReal.ofReal (-y) ^ r ∂(κ x) := by
  refine le_of_forall_lt_rpow hr ENNReal.ofReal_ne_top (fun t ht0 htU => ?_)
  have hF := upperQ_lt κ x hp1 (show upperQ κ p x < -t by linarith)
  have hI : ENNReal.ofReal p ≤ κ x (Set.Iic (-t)) := by
    have h1 : κ x (Set.Iic (-t)) = ENNReal.ofReal (condCdf κ x (-t)) := by
      unfold condCdf; rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [h1]
    exact ENNReal.ofReal_le_ofReal hF.le
  calc ENNReal.ofReal p * ENNReal.ofReal t ^ r
      ≤ κ x (Set.Iic (-t)) * ENNReal.ofReal t ^ r := by gcongr
    _ = ∫⁻ y in Set.Iic (-t), ENNReal.ofReal t ^ r ∂(κ x) := by rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ y in Set.Iic (-t), ENNReal.ofReal (-y) ^ r ∂(κ x) :=
        setLIntegral_mono (measurable_ofReal_rpow measurable_neg r)
          (fun y hy => ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal
            (by have : y ≤ -t := hy; linarith)) hr.le)
    _ ≤ ∫⁻ y, ENNReal.ofReal (-y) ^ r ∂(κ x) := setLIntegral_le_lintegral _ _

lemma bound_Lhat (W : WeightSeq d) (hP : ProbWeights W) {n : ℕ} (hn : 1 ≤ n)
    (ω : ℕ → EuclideanSpace ℝ (Fin d) × ℝ) {p r : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hr : 0 < r) :
    ENNReal.ofReal p * ENNReal.ofReal (-estLowerQ W n p ω) ^ (r / 2) ≤
      ENNReal.ofReal (wsum W n (fun y => (max (-y) 0) ^ (r / 2)) ω) := by
  have hr2 : 0 < r / 2 := by positivity
  refine le_of_forall_lt_rpow hr2 ENNReal.ofReal_ne_top (fun t ht0 htL => ?_)
  have hF := estLowerQ_lt W hP hn ω hp1 (show estLowerQ W n p ω < -t by linarith)
  have hsum : estCdf W n ω (-t) * t ^ (r / 2) ≤ wsum W n (fun y => (max (-y) 0) ^ (r / 2)) ω := by
    unfold estCdf wsum
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ ((hP n hn _ _).1 i)
    split_ifs with h
    · rw [one_mul]
      exact Real.rpow_le_rpow ht0.le (le_max_of_le_left (by linarith)) hr2.le
    · rw [zero_mul]
      exact Real.rpow_nonneg (le_max_right _ _) _
  have hreal : p * t ^ (r / 2) ≤ wsum W n (fun y => (max (-y) 0) ^ (r / 2)) ω :=
    le_trans (mul_le_mul_of_nonneg_right hF (Real.rpow_nonneg ht0.le _)) hsum
  rw [ENNReal.ofReal_rpow_of_nonneg ht0.le hr2.le, ← ENNReal.ofReal_mul hp0.le]
  exact ENNReal.ofReal_le_ofReal hreal

lemma bound_Uhat (W : WeightSeq d) (hP : ProbWeights W) {n : ℕ} (hn : 1 ≤ n)
    (ω : ℕ → EuclideanSpace ℝ (Fin d) × ℝ) {p r : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hr : 0 < r) :
    ENNReal.ofReal (1 - p) * ENNReal.ofReal (estUpperQ W n p ω) ^ (r / 2) ≤
      ENNReal.ofReal (wsum W n (fun y => (max y 0) ^ (r / 2)) ω) := by
  have hr2 : 0 < r / 2 := by positivity
  refine le_of_forall_lt_rpow hr2 ENNReal.ofReal_ne_top (fun t ht0 htU => ?_)
  have hF := lt_estUpperQ W hP hn ω hp0 htU
  have hsumW := (hP n hn (ω 0).1 (fun j => (ω (j.val + 1)).1)).2
  have hone : 1 - estCdf W n ω t = ∑ i : Fin n, W n (ω 0).1 (fun j => (ω (j.val + 1)).1) i *
      (1 - if (ω (i.val + 1)).2 ≤ t then 1 else 0) := by
    have : ∑ i : Fin n, W n (ω 0).1 (fun j => (ω (j.val + 1)).1) i *
        (1 - if (ω (i.val + 1)).2 ≤ t then 1 else 0) =
        ∑ i : Fin n, W n (ω 0).1 (fun j => (ω (j.val + 1)).1) i - estCdf W n ω t := by
      unfold estCdf
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => by ring)
    rw [this, hsumW]
  have hsum : (1 - estCdf W n ω t) * t ^ (r / 2) ≤ wsum W n (fun y => (max y 0) ^ (r / 2)) ω := by
    rw [hone]
    unfold wsum
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ ((hP n hn _ _).1 i)
    split_ifs with h
    · rw [sub_self, zero_mul]
      exact Real.rpow_nonneg (le_max_right _ _) _
    · rw [sub_zero, one_mul]
      exact Real.rpow_le_rpow ht0.le (le_max_of_le_left (by linarith [not_le.1 h])) hr2.le
  have hreal : (1 - p) * t ^ (r / 2) ≤ wsum W n (fun y => (max y 0) ^ (r / 2)) ω :=
    le_trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg ht0.le _)) hsum
  rw [ENNReal.ofReal_rpow_of_nonneg ht0.le hr2.le, ← ENNReal.ofReal_mul (by linarith)]
  exact ENNReal.ofReal_le_ofReal hreal

end Bounds

section Assembly

lemma lr_generic (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (hW : MeasurableWeights W) (hcons : IsConsistent μ W)
    (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ] {r : ℝ} (hr : 1 ≤ r)
    (hm : ∫⁻ q, ‖q.2‖ₑ ^ r ∂(μ ⊗ₘ κ) < ∞)
    {f : ℕ → (ℕ → EuclideanSpace ℝ (Fin d) × ℝ) → ℝ}
    (hf : TendstoInMeasure (pairLaw μ κ) f atTop (fun _ => 0))
    {c1 c2 : ℝ≥0∞} (hc1 : c1 ≠ 0) (hc1' : c1 ≠ ∞) (hc2 : c2 ≠ 0) (hc2' : c2 ≠ ∞)
    {ψ : ℝ → ℝ} (hψ : Measurable ψ) (hψle : ∀ y, ENNReal.ofReal (ψ y) ≤ ‖y‖ₑ)
    {φ : ℝ → ℝ} (hφ : Measurable φ) (hφle : ∀ y, ‖φ y‖ₑ ^ (2:ℝ) ≤ ‖y‖ₑ ^ r)
    {a : EuclideanSpace ℝ (Fin d) → ℝ} {b : ℕ → (ℕ → EuclideanSpace ℝ (Fin d) × ℝ) → ℝ}
    (hfab : ∀ n, 1 ≤ n → ∀ ω, ‖f n ω‖ₑ = ENNReal.ofReal (a (ω 0).1 + b n ω))
    (hA : ∀ x, c1 * ENNReal.ofReal (a x) ^ r ≤ ∫⁻ y, ENNReal.ofReal (ψ y) ^ r ∂(κ x))
    (hB : ∀ n, 1 ≤ n → ∀ ω, c2 * ENNReal.ofReal (b n ω) ^ (r / 2) ≤ ENNReal.ofReal (wsum W n φ ω)) :
    Tendsto (fun n => ∫⁻ ω, ‖f n ω‖ₑ ^ r ∂(pairLaw μ κ)) atTop (𝓝 0) := by
  haveI := pairLaw_prob μ κ
  have hr0 : 0 < r := by linarith
  set A1 : ℝ≥0∞ := 2 ^ (r - 1) / c1 with hA1
  set A2 : ℝ≥0∞ := 2 ^ (r - 1) * 2 / c2 ^ (2:ℝ) with hA2
  have h2top : (2:ℝ≥0∞) ^ (r - 1) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)
  have hA1t : A1 ≠ ∞ := ENNReal.div_ne_top h2top hc1
  have hA2t : A2 ≠ ∞ := ENNReal.div_ne_top (ENNReal.mul_ne_top h2top (by norm_num))
    (ENNReal.rpow_pos (pos_iff_ne_zero.2 hc2) hc2').ne'
  let K : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun x => ∫⁻ y, ENNReal.ofReal (ψ y) ^ r ∂(κ x)
  let m : EuclideanSpace ℝ (Fin d) → ℝ := fun x => ∫ y, φ y ∂(κ x)
  have hKm : Measurable K := Measurable.lintegral_kernel (measurable_ofReal_rpow hψ r)
  have hmm : Measurable m := measurable_condMean κ hφ
  have hmomφ : ∫⁻ q, ‖φ q.2‖ₑ ^ (2:ℝ) ∂(μ ⊗ₘ κ) < ∞ :=
    lt_of_le_of_lt (lintegral_mono (fun q => hφle q.2)) hm
  have hδ0 := consist_phi μ W hW hcons κ hφ (by norm_num : (1:ℝ) < 2) hmomφ
  let G : (ℕ → EuclideanSpace ℝ (Fin d) × ℝ) → ℝ≥0∞ := fun ω =>
    A1 * K (ω 0).1 + A2 * ‖m (ω 0).1‖ₑ ^ (2:ℝ)
  let δ : ℕ → (ℕ → EuclideanSpace ℝ (Fin d) × ℝ) → ℝ≥0∞ := fun n ω =>
    A2 * ‖wsum W n φ ω - m (ω 0).1‖ₑ ^ (2:ℝ)
  have hGx : Measurable (fun x => A1 * K x + A2 * ‖m x‖ₑ ^ (2:ℝ)) :=
    (hKm.const_mul A1).add ((hmm.enorm.pow_const _).const_mul A2)
  have hG : Measurable G := hGx.comp measurable_x0
  have hGi : ∫⁻ ω, G ω ∂(pairLaw μ κ) ≠ ∞ := by
    have e1 : ∫⁻ ω, G ω ∂(pairLaw μ κ) = ∫⁻ x, (A1 * K x + A2 * ‖m x‖ₑ ^ (2:ℝ)) ∂μ :=
      lintegral_x0 μ κ hGx
    rw [e1, lintegral_add_left (hKm.const_mul A1), lintegral_const_mul _ hKm,
      lintegral_const_mul _ (hmm.enorm.pow_const _)]
    have hK : ∫⁻ x, K x ∂μ < ∞ := by
      have : ∫⁻ x, K x ∂μ = ∫⁻ q, ENNReal.ofReal (ψ q.2) ^ r ∂(μ ⊗ₘ κ) :=
        (Measure.lintegral_compProd ((measurable_ofReal_rpow hψ r).comp measurable_snd)).symm
      rw [this]
      exact lt_of_le_of_lt (lintegral_mono (fun q => ENNReal.rpow_le_rpow (hψle q.2) hr0.le)) hm
    have hM : ∫⁻ x, ‖m x‖ₑ ^ (2:ℝ) ∂μ < ∞ := by
      have h1 : ∫⁻ x, ‖m x‖ₑ ^ (2:ℝ) ∂μ ≤ ∫⁻ x, ∫⁻ y, ‖φ y‖ₑ ^ (2:ℝ) ∂(κ x) ∂μ :=
        lintegral_mono (fun x => enorm_integral_sq_le (κ x) hφ)
      have h2 : ∫⁻ x, ∫⁻ y, ‖φ y‖ₑ ^ (2:ℝ) ∂(κ x) ∂μ = ∫⁻ q, ‖φ q.2‖ₑ ^ (2:ℝ) ∂(μ ⊗ₘ κ) :=
        (Measure.lintegral_compProd ((hφ.comp measurable_snd).enorm.pow_const _)).symm
      exact lt_of_le_of_lt (h1.trans h2.le) hmomφ
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hA1t hK.ne, ENNReal.mul_ne_top hA2t hM.ne⟩
  have hδm : ∀ n, Measurable (δ n) := fun n =>
    (((measurable_wsum W hW n hφ).sub (hmm.comp measurable_x0)).enorm.pow_const _).const_mul A2
  have hδ : Tendsto (fun n => ∫⁻ ω, δ n ω ∂(pairLaw μ κ)) atTop (𝓝 0) := by
    have e : ∀ n, ∫⁻ ω, δ n ω ∂(pairLaw μ κ) =
        A2 * ∫⁻ ω, ‖wsum W n φ ω - ∫ y, φ y ∂(κ (ω 0).1)‖ₑ ^ (2:ℝ) ∂(pairLaw μ κ) := fun n =>
      lintegral_const_mul _
        (((measurable_wsum W hW n hφ).sub (hmm.comp measurable_x0)).enorm.pow_const _)
    simp_rw [e]
    have := ENNReal.Tendsto.const_mul hδ0 (Or.inr hA2t)
    rwa [mul_zero] at this
  refine dct_tim hr0 hf hG hGi hδm hδ ?_
  filter_upwards [eventually_ge_atTop 1] with n hn ω
  rw [hfab n hn ω]
  have := combine (m := m (ω 0).1) hr hc1 hc1' hc2 hc2' (hA (ω 0).1) (hB n hn ω)
  exact this

lemma lr_lower (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (hW : MeasurableWeights W) (hP : ProbWeights W) (hcons : IsConsistent μ W)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ] (r : ℝ) (hr : 1 ≤ r)
    (hm : ∫⁻ q, ‖q.2‖ₑ ^ r ∂(μ ⊗ₘ κ) < ∞) :
    Tendsto (fun n => ∫⁻ ω, ‖max (-(estLowerQ W n p ω - lowerQ κ p (ω 0).1)) 0‖ₑ ^ r
      ∂(pairLaw μ κ)) atTop (𝓝 0) := by
  have hr0 : 0 < r := by linarith
  refine lr_generic μ W hW hcons κ hr hm (part9 μ W hW hP hcons p hp0 hp1 κ)
    (c1 := ENNReal.ofReal (1 - p)) (c2 := ENNReal.ofReal p)
    (ENNReal.ofReal_pos.2 (by linarith)).ne' ENNReal.ofReal_ne_top
    (ENNReal.ofReal_pos.2 hp0).ne' ENNReal.ofReal_ne_top
    (ψ := fun y => y) measurable_id
    (fun y => by rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self y))
    (φ := fun y => (max (-y) 0) ^ (r / 2))
    ((measurable_neg.max measurable_const).pow_const _) ?_
    (a := fun x => lowerQ κ p x) (b := fun n ω => -estLowerQ W n p ω)
    (fun n _ ω => by rw [enorm_max0]; congr 1; ring)
    (fun x => bound_L κ x hp0 hr0)
    (fun n hn ω => bound_Lhat W hP hn ω hp0 hp1 hr0)
  intro y
  rw [Real.enorm_eq_ofReal (Real.rpow_nonneg (le_max_right _ _) _),
    ← ENNReal.ofReal_rpow_of_nonneg (le_max_right _ _) (by positivity), ← ENNReal.rpow_mul,
    show r / 2 * 2 = r by ring, Real.enorm_eq_ofReal_abs]
  exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (max_le (neg_le_abs y) (abs_nonneg y))) hr0.le

lemma lr_upper (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (hW : MeasurableWeights W) (hP : ProbWeights W) (hcons : IsConsistent μ W)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ] (r : ℝ) (hr : 1 ≤ r)
    (hm : ∫⁻ q, ‖q.2‖ₑ ^ r ∂(μ ⊗ₘ κ) < ∞) :
    Tendsto (fun n => ∫⁻ ω, ‖max (estUpperQ W n p ω - upperQ κ p (ω 0).1) 0‖ₑ ^ r
      ∂(pairLaw μ κ)) atTop (𝓝 0) := by
  have hr0 : 0 < r := by linarith
  refine lr_generic μ W hW hcons κ hr hm (part10 μ W hW hP hcons p hp0 hp1 κ)
    (c1 := ENNReal.ofReal p) (c2 := ENNReal.ofReal (1 - p))
    (ENNReal.ofReal_pos.2 hp0).ne' ENNReal.ofReal_ne_top
    (ENNReal.ofReal_pos.2 (by linarith)).ne' ENNReal.ofReal_ne_top
    (ψ := fun y => -y) measurable_neg
    (fun y => by rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (neg_le_abs y))
    (φ := fun y => (max y 0) ^ (r / 2))
    ((measurable_id.max measurable_const).pow_const _) ?_
    (a := fun x => -upperQ κ p x) (b := fun n ω => estUpperQ W n p ω)
    (fun n _ ω => by rw [enorm_max0]; congr 1; ring)
    (fun x => bound_U κ x hp1 hr0)
    (fun n hn ω => bound_Uhat W hP hn ω hp0 hp1 hr0)
  intro y
  rw [Real.enorm_eq_ofReal (Real.rpow_nonneg (le_max_right _ _) _),
    ← ENNReal.ofReal_rpow_of_nonneg (le_max_right _ _) (by positivity), ← ENNReal.rpow_mul,
    show r / 2 * 2 = r by ring, Real.enorm_eq_ofReal_abs]
  exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (max_le (le_abs_self y) (abs_nonneg y))) hr0.le

end Assembly

end SRQ3

open MeasureTheory ProbabilityTheory Filter Topology StoneRegression.Quantile ENNReal NNReal in
theorem solution {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : StoneRegression.Criterion.WeightSeq d) (hW : StoneRegression.Criterion.MeasurableWeights W) (hP : StoneRegression.Criterion.ProbWeights W) (hcons : StoneRegression.Criterion.IsConsistent μ W)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (κ : Kernel (EuclideanSpace ℝ (Fin d)) ℝ) [IsMarkovKernel κ] :
    TendstoInMeasure (StoneRegression.Criterion.pairLaw μ κ)
        (fun n ω => max (-(estLowerQ W n p ω - lowerQ κ p (ω 0).1)) 0) atTop (fun _ => 0) ∧
    TendstoInMeasure (StoneRegression.Criterion.pairLaw μ κ)
        (fun n ω => max (estUpperQ W n p ω - upperQ κ p (ω 0).1) 0) atTop (fun _ => 0) ∧
    ∀ r : ℝ, 1 ≤ r → ∫⁻ q, ‖q.2‖ₑ ^ r ∂(μ ⊗ₘ κ) < ∞ →
      Tendsto (fun n => ∫⁻ ω, ‖max (-(estLowerQ W n p ω - lowerQ κ p (ω 0).1)) 0‖ₑ ^ r ∂(StoneRegression.Criterion.pairLaw μ κ))
          atTop (𝓝 0) ∧
      Tendsto (fun n => ∫⁻ ω, ‖max (estUpperQ W n p ω - upperQ κ p (ω 0).1) 0‖ₑ ^ r ∂(StoneRegression.Criterion.pairLaw μ κ))
          atTop (𝓝 0) := by
  exact ⟨SRQ3.part9 μ W hW hP hcons p hp0 hp1 κ, SRQ3.part10 μ W hW hP hcons p hp0 hp1 κ,
    fun r hr hm => ⟨SRQ3.lr_lower μ W hW hP hcons p hp0 hp1 κ r hr hm,
      SRQ3.lr_upper μ W hW hP hcons p hp0 hp1 κ r hr hm⟩⟩
