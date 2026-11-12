-- Prove2me | solution 1 for PersuasionByParts.Known.cutoff_reduction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T16:55:06.026928+00:00
-- url     : https://prove2.me/submissions/d6f03d13-b451-4c02-876a-929252dc7a45

import Mathlib
import Definitions.Def_PersuasionByParts_Known_Model
import Theorems.Thm_PersuasionByParts_Known_experiment_wellposed

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
noncomputable section

namespace PersuasionByParts.Known.Dev.CR
open PersuasionByParts.Known

/-- an up-set whose closed rays `Ici t` (`t` in the set) all have measure `≤ m` has measure `≤ m`. -/
theorem upset_measure_le (μ : Measure ℝ) (T : Set ℝ) (hup : ∀ a ∈ T, ∀ b, a ≤ b → b ∈ T)
    (m : ℝ≥0∞) (hm : ∀ t ∈ T, μ (Ici t) ≤ m) : μ T ≤ m := by
  rcases T.eq_empty_or_nonempty with rfl | hne
  · simp
  by_cases hb : BddBelow T
  · obtain ⟨u, hanti, hlim, hu⟩ := exists_seq_tendsto_sInf hne hb
    by_cases h0 : sInf T ∈ T
    · exact le_trans (measure_mono fun b hb' => csInf_le hb hb') (hm _ h0)
    · have hsub : T ⊆ ⋃ n, Ici (u n) := by
        intro b hbT
        have hlt : sInf T < b := lt_of_le_of_ne (csInf_le hb hbT) (fun h => h0 (h ▸ hbT))
        obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hlt)).exists
        exact mem_iUnion.2 ⟨n, le_of_lt hn⟩
      refine le_trans (measure_mono hsub) ?_
      have hmono : Monotone fun n => Ici (u n) := fun i j hij => Ici_subset_Ici.2 (hanti hij)
      rw [hmono.measure_iUnion]
      exact iSup_le fun n => hm _ (hu n)
  · have hall : ∀ k : ℕ, ((-(k:ℝ)) ∈ T) := fun k => by
      obtain ⟨a, haT, hak⟩ := not_bddBelow_iff.1 hb (-(k:ℝ))
      exact hup a haT _ hak.le
    have hsub : T ⊆ ⋃ k : ℕ, Ici (-(k:ℝ)) := by
      intro b _
      obtain ⟨k, hk⟩ := exists_nat_ge (-b)
      exact mem_iUnion.2 ⟨k, by simp only [mem_Ici]; linarith⟩
    refine le_trans (measure_mono hsub) ?_
    have hmono : Monotone fun k : ℕ => Ici (-(k:ℝ)) := fun i j hij =>
      Ici_subset_Ici.2 (by simpa using hij)
    rw [hmono.measure_iUnion]
    exact iSup_le fun k => hm _ (hall k)


variable {n : ℕ} (P : Prior n) (hn : 0 < n)

theorem total_meas' : Measurable (total : (Fin n → ℝ) → ℝ) := by
  unfold total; fun_prop

instance instJ (E : JointExperiment n) : IsProbabilityMeasure (jointSignalLaw P E) := by
  unfold jointSignalLaw; infer_instance

theorem jpost_meas (E : JointExperiment n) : Measurable (jointPosterior P E) :=
  ((total_meas' (n := n)).stronglyMeasurable.integral_kernel).measurable

/-- the cutoff as a `Decision` -/
def cutD (t : ℝ) : Decision where
  toFun := cutoff t
  measurable := by
    unfold cutoff
    exact Measurable.ite measurableSet_Ici measurable_const measurable_const
  monotone := fun a b hab => by
    unfold cutoff
    split_ifs with h1 h2 <;> first | exact le_refl _ | exact absurd (le_trans h1 hab) h2 | norm_num
  range := fun y => by
    unfold cutoff; split_ifs <;> simp


include hn in
theorem prodVal_ge (g : Decision) (t : ℝ) : g t * productCutoff P t ≤ productValue P g := by
  obtain ⟨-, -, -, hbg, -, hV, -, hPg, -⟩ := experiment_wellposed P hn g
  obtain ⟨-, -, -, -, -, -, -, hPc, -⟩ := experiment_wellposed P hn (cutD t)
  obtain ⟨-, -, hne, -, -, -⟩ := (experiment_wellposed P hn g).2.2.2.2.2.2.2.2 t
  by_cases h0 : g t = 0
  · rw [h0, zero_mul]; exact hV.1
  have hpos : 0 < g t := lt_of_le_of_ne (g.range t).1 (Ne.symm h0)
  have hle : productCutoff P t ≤ productValue P g / g t := by
    refine csSup_le hne ?_
    rintro v ⟨E, rfl⟩
    rw [le_div_iff₀ hpos]
    have hint1 := (hPc E).2.1
    have hint2 := (hPg E).2.1
    have hmono : productPayoff P E (cutoff t) * g t ≤ productPayoff P E g := by
      unfold productPayoff
      rw [← integral_mul_const]
      refine integral_mono (hint1.mul_const _) hint2 fun s => ?_
      show cutoff t (productPosterior P E s) * g t ≤ g (productPosterior P E s)
      unfold cutoff
      split_ifs with h
      · simpa using g.monotone h
      · simpa using (g.range _).1
    exact le_trans hmono (le_csSup hbg ⟨E, rfl⟩)
  calc g t * productCutoff P t ≤ g t * (productValue P g / g t) :=
        mul_le_mul_of_nonneg_left hle hpos.le
    _ = productValue P g := by field_simp


theorem jpay_eq (E : JointExperiment n) (t : ℝ) :
    jointPayoff P E (cutoff t) = (jointSignalLaw P E).real {y | t ≤ jointPosterior P E y} := by
  have hB : MeasurableSet {y | t ≤ jointPosterior P E y} :=
    measurableSet_le measurable_const (jpost_meas P E)
  haveI := instJ P E
  unfold jointPayoff
  have : (fun y => cutoff t (jointPosterior P E y)) =
      ({y | t ≤ jointPosterior P E y} : Set E.Signal).indicator (fun _ => (1:ℝ)) := by
    funext y; simp [cutoff, Set.indicator_apply]
  rw [this, integral_indicator_const _ hB]; simp

include hn in
theorem jc_ge (E : JointExperiment n) (t : ℝ) :
    (jointSignalLaw P E).real {y | t ≤ jointPosterior P E y} ≤ jointCutoff P t := by
  obtain ⟨-, hb, -⟩ := (experiment_wellposed P hn (cutD t)).2.2.2.2.2.2.2.2 t
  rw [← jpay_eq]
  exact le_csSup hb ⟨E, rfl⟩

include hn in
theorem key (c : ℝ) (hc : 0 < c)
    (hcutoff : ∀ t : ℝ, productCutoff P t ≥ c * jointCutoff P t ^ 2) (g : Decision)
    (E : JointExperiment n) (t : ℝ) :
    c * g t * (jointSignalLaw P E).real {y | t ≤ jointPosterior P E y} ^ 2 ≤ productValue P g := by
  have h1 := prodVal_ge P hn g t
  have h2 := hcutoff t
  have h3 := jc_ge P hn E t
  have hq : 0 ≤ (jointSignalLaw P E).real {y | t ≤ jointPosterior P E y} := measureReal_nonneg
  have hg := (g.range t).1
  have : (jointSignalLaw P E).real {y | t ≤ jointPosterior P E y} ^ 2 ≤ jointCutoff P t ^ 2 :=
    pow_le_pow_left₀ hq h3 2
  calc c * g t * (jointSignalLaw P E).real {y | t ≤ jointPosterior P E y} ^ 2
      ≤ c * g t * jointCutoff P t ^ 2 := mul_le_mul_of_nonneg_left this (by positivity)
    _ = g t * (c * jointCutoff P t ^ 2) := by ring
    _ ≤ g t * productCutoff P t := mul_le_mul_of_nonneg_left h2 hg
    _ ≤ _ := h1


include hn in
theorem tail_bound (c : ℝ) (hc : 0 < c)
    (hcutoff : ∀ t : ℝ, productCutoff P t ≥ c * jointCutoff P t ^ 2) (g : Decision)
    (E : JointExperiment n) (u : ℝ) (hu : 0 < u) :
    jointSignalLaw P E {s | u < g (jointPosterior P E s)} ≤
      ENNReal.ofReal (Real.sqrt (productValue P g / c) * u ^ (-(1/2:ℝ))) := by
  set ν := jointSignalLaw P E
  haveI := instJ P E
  have hY := jpost_meas P E
  set Y := jointPosterior P E
  set V := productValue P g
  have hV : 0 ≤ V := (experiment_wellposed P hn g).2.2.2.2.2.1.1
  set M := Real.sqrt (V / c) * u ^ (-(1/2:ℝ)) with hM
  have hT : MeasurableSet {y | u < g y} := measurableSet_lt measurable_const g.measurable
  have hmap : ν {s | u < g (Y s)} = (ν.map Y) {y | u < g y} := by
    rw [Measure.map_apply hY hT]; rfl
  rw [hmap]
  refine upset_measure_le _ _ (fun a ha b hab => lt_of_lt_of_le ha (g.monotone hab)) _ ?_
  intro t ht
  have hB : MeasurableSet (Ici t) := measurableSet_Ici
  rw [Measure.map_apply hY hB]
  have hq : ν (Y ⁻¹' Ici t) = ENNReal.ofReal (ν.real {y | t ≤ Y y}) := by
    rw [ofReal_measureReal]; rfl
  rw [hq]
  refine ENNReal.ofReal_le_ofReal ?_
  have ht' : u < g t := ht
  have hk := key P hn c hc hcutoff g E t
  have hq0 : 0 ≤ ν.real {y | t ≤ Y y} := measureReal_nonneg
  have hM0 : 0 ≤ M := by positivity
  have hsq : ν.real {y | t ≤ Y y} ^ 2 ≤ M ^ 2 := by
    have : M ^ 2 = V / c * u⁻¹ := by
      rw [hM, mul_pow, Real.sq_sqrt (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hu.le]
      norm_num [Real.rpow_neg_one]
    rw [this, div_mul_eq_mul_div, le_div_iff₀ hc, ← div_eq_mul_inv, le_div_iff₀ hu]
    have : c * u * ν.real {y | t ≤ Y y} ^ 2 ≤ c * g t * ν.real {y | t ≤ Y y} ^ 2 := by
      have : u ≤ g t := le_of_lt ht'
      gcongr
    nlinarith [this, hk]
  exact le_of_sq_le_sq hsq hM0 |> fun h => by simpa using abs_le_of_sq_le_sq' hsq hM0 |>.2


include hn in
theorem payoff_le (c : ℝ) (hc : 0 < c)
    (hcutoff : ∀ t : ℝ, productCutoff P t ≥ c * jointCutoff P t ^ 2) (g : Decision)
    (E : JointExperiment n) :
    jointPayoff P E g ≤ 2 * Real.sqrt (productValue P g / c) := by
  haveI := instJ P E
  set ν := jointSignalLaw P E
  set Y := jointPosterior P E
  set K := Real.sqrt (productValue P g / c) with hK
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  have hint : Integrable (fun s => g (Y s)) ν := ((experiment_wellposed P hn g).2.2.2.2.2.2.1 E).2.1
  have hm : Measurable (fun s => g (Y s)) := g.measurable.comp (jpost_meas P E)
  have h1 : ENNReal.ofReal (jointPayoff P E g) = ∫⁻ s, ENNReal.ofReal (g (Y s)) ∂ν :=
    ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun s => (g.range _).1)
  have h2 : ∫⁻ s, ENNReal.ofReal (g (Y s)) ∂ν = ∫⁻ t in Ioi (0:ℝ), ν {a | t < g (Y a)} :=
    lintegral_eq_lintegral_meas_lt ν (Eventually.of_forall fun s => (g.range _).1) hm.aemeasurable
  have h3 : ∫⁻ t in Ioi (0:ℝ), ν {a | t < g (Y a)} ≤
      ∫⁻ t in Ioi (0:ℝ), (Ioc (0:ℝ) 1).indicator
        (fun t => ENNReal.ofReal (K * t ^ (-(1/2:ℝ)))) t := by
    refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
    by_cases h : t ≤ 1
    · rw [indicator_of_mem (show t ∈ Ioc (0:ℝ) 1 from ⟨ht, h⟩)]
      exact tail_bound P hn c hc hcutoff g E t ht
    · have : {a | t < g (Y a)} = ∅ := by
        ext a; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt]
        exact le_trans (g.range _).2 (not_le.1 h).le
      rw [this]; simp
  have h4 : ∫⁻ t in Ioi (0:ℝ), (Ioc (0:ℝ) 1).indicator
        (fun t => ENNReal.ofReal (K * t ^ (-(1/2:ℝ)))) t =
      ∫⁻ t in Ioc (0:ℝ) 1, ENNReal.ofReal (K * t ^ (-(1/2:ℝ))) := by
    rw [lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.2 Ioc_subset_Ioi_self]
  have hii : IntegrableOn (fun t : ℝ => K * t ^ (-(1/2:ℝ))) (Ioc (0:ℝ) 1) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := -(1/2:ℝ))
      (by norm_num))
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 this |>.const_mul K
  have h5 : ∫⁻ t in Ioc (0:ℝ) 1, ENNReal.ofReal (K * t ^ (-(1/2:ℝ))) = ENNReal.ofReal (2 * K) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hii (ae_restrict_of_forall_mem measurableSet_Ioc
      fun t ht => by have := ht.1; positivity)]
    congr 1
    rw [← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by norm_num))]
    norm_num [Real.zero_rpow]
    ring
  have := h1.trans_le (h2.trans_le (h3.trans (h4.trans_le h5.le)))
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 this

end PersuasionByParts.Known.Dev.CR

open PersuasionByParts.Known.Dev.CR
open MeasureTheory ProbabilityTheory Set
noncomputable section

namespace PersuasionByParts.Known

theorem chk_cutoff_reduction {n : ℕ} (P : Prior n) (hn : 0 < n)
    (c : ℝ) (hc : 0 < c)
    (hcutoff : ∀ t : ℝ, productCutoff P t ≥ c * jointCutoff P t ^ 2) :
    ∀ g : Decision, productValue P g ≥ (c / 4) * jointValue P g ^ 2 := by
  intro g
  obtain ⟨hne, -, -, -, ⟨hJ0, -⟩, ⟨hV0, -⟩, -⟩ := experiment_wellposed P hn g
  have hle : jointValue P g ≤ 2 * Real.sqrt (productValue P g / c) :=
    csSup_le hne (by rintro v ⟨E, rfl⟩; exact payoff_le P hn c hc hcutoff g E)
  have h2 : jointValue P g ^ 2 ≤ (2 * Real.sqrt (productValue P g / c)) ^ 2 :=
    pow_le_pow_left₀ hJ0 hle 2
  rw [mul_pow, Real.sq_sqrt (by positivity)] at h2
  have : c / 4 * jointValue P g ^ 2 ≤ c / 4 * (2 ^ 2 * (productValue P g / c)) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  calc c / 4 * jointValue P g ^ 2 ≤ c / 4 * (2 ^ 2 * (productValue P g / c)) := this
    _ = productValue P g := by field_simp; ring

end PersuasionByParts.Known
end
end
end

theorem solution : type_of% @PersuasionByParts.Known.chk_cutoff_reduction := @PersuasionByParts.Known.chk_cutoff_reduction
