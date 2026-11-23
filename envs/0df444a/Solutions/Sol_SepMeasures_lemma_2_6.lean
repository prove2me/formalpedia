-- Prove2me | solution 1 for SepMeasures.lemma_2_6
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:20:51.331931+00:00
-- url     : https://prove2.me/submissions/ebffee80-e8e2-408e-a424-ae178ceeb939

import Mathlib
import Definitions.Def_SepMeasures_CutValue
import Definitions.Def_SepMeasures_Families
import Definitions.Def_SepMeasures_W1

open MeasureTheory SepMeasures

namespace Aux26

lemma coe_nnnorm_eq_ofReal_abs (r : ℝ) : (‖r‖₊ : ENNReal) = ENNReal.ofReal |r| := by
  have h : |r| = (‖r‖₊ : ℝ) := by rw [coe_nnnorm, Real.norm_eq_abs]
  rw [h, ENNReal.ofReal_coe_nnreal]

lemma seminorm_abs_sub_le {d : ℕ} (N : Seminorm ℝ (E d)) (x y : E d) :
    |N x - N y| ≤ N (x - y) := by
  rw [abs_sub_le_iff]
  constructor
  · have h := map_add_le_add N (x - y) y
    rw [sub_add_cancel] at h
    linarith
  · have h := map_add_le_add N (y - x) x
    rw [sub_add_cancel] at h
    have hneg : N (y - x) = N (x - y) := by
      have : y - x = -(x - y) := by abel
      rw [this, map_neg_eq_map]
    linarith

lemma seminorm_finset_sum_le {d ι : ℕ} (N : Seminorm ℝ (E d)) (s : Finset (Fin ι))
    (f : Fin ι → E d) : N (∑ i ∈ s, f i) ≤ ∑ i ∈ s, N (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (map_add_le_add N _ _).trans (add_le_add_right ih _)

lemma continuous_seminorm_Ed {d : ℕ} (N : Seminorm ℝ (E d)) : Continuous N := by
  let C : ℝ := ∑ i : Fin d, N (EuclideanSpace.single i 1)
  have hbound : ∀ z : E d, N z ≤ C * ‖z‖ := by
    intro z
    have hz : z = ∑ i : Fin d, (z i) • EuclideanSpace.single i (1 : ℝ) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    calc N z = N (∑ i : Fin d, (z i) • EuclideanSpace.single i (1 : ℝ)) := by rw [← hz]
      _ ≤ ∑ i : Fin d, N ((z i) • EuclideanSpace.single i (1 : ℝ)) :=
          seminorm_finset_sum_le N Finset.univ _
      _ = ∑ i : Fin d, |z i| * N (EuclideanSpace.single i 1) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_smul_eq_mul, Real.norm_eq_abs]
      _ ≤ ∑ i : Fin d, ‖z‖ * N (EuclideanSpace.single i 1) := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le z i) (apply_nonneg N _)
      _ = C * ‖z‖ := by rw [← Finset.mul_sum, mul_comm]
  rw [Metric.continuous_iff]
  intro x ε hε
  refine ⟨ε / (|C| + 1), div_pos hε (by positivity), fun y hy => ?_⟩
  rw [Real.dist_eq]
  have h1 : |N y - N x| ≤ N (y - x) := seminorm_abs_sub_le N y x
  have h2 : N (y - x) ≤ C * ‖y - x‖ := hbound (y - x)
  have h3 : C * ‖y - x‖ ≤ (|C| + 1) * ‖y - x‖ :=
    mul_le_mul_of_nonneg_right ((le_abs_self C).trans (by linarith)) (norm_nonneg _)
  have h4 : ‖y - x‖ < ε / (|C| + 1) := by rwa [dist_eq_norm] at hy
  have h5 : (|C| + 1) * ‖y - x‖ < (|C| + 1) * (ε / (|C| + 1)) :=
    mul_lt_mul_of_pos_left h4 (by positivity)
  have h6 : (|C| + 1) * (ε / (|C| + 1)) = ε := mul_div_cancel₀ ε (by positivity)
  linarith

lemma prod_fst_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure ν] :
    (μ.prod ν).map Prod.fst = μ := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs]
  have : Prod.fst ⁻¹' s = s ×ˢ (Set.univ : Set β) := by ext p; simp
  rw [this, Measure.prod_prod, measure_univ, mul_one]

lemma prod_snd_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (μ.prod ν).map Prod.snd = ν := by
  ext s hs
  rw [Measure.map_apply measurable_snd hs]
  have : Prod.snd ⁻¹' s = (Set.univ : Set α) ×ˢ s := by ext p; simp
  rw [this, Measure.prod_prod, measure_univ, one_mul]

lemma integrable_dist_prod {d : ℕ} (N : Seminorm ℝ (E d))
    (μ ν : Measure (E d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : FiniteFirstMoment N μ) (hν : FiniteFirstMoment N ν) :
    Integrable (fun p : E d × E d => N (p.1 - p.2)) (μ.prod ν) := by
  have hcont : Continuous (fun p : E d × E d => N (p.1 - p.2)) :=
    (continuous_seminorm_Ed N).comp (continuous_fst.sub continuous_snd)
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have hle : ∀ p : E d × E d, (‖N (p.1 - p.2)‖₊ : ENNReal) ≤
      ENNReal.ofReal (N p.1) + ENNReal.ofReal (N p.2) := by
    intro p
    rw [coe_nnnorm_eq_ofReal_abs, abs_of_nonneg (apply_nonneg N _),
      ← ENNReal.ofReal_add (apply_nonneg N _) (apply_nonneg N _)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc N (p.1 - p.2) = N (p.1 + (-p.2)) := by rw [sub_eq_add_neg]
      _ ≤ N p.1 + N (-p.2) := map_add_le_add N _ _
      _ = N p.1 + N p.2 := by rw [map_neg_eq_map]
  have hmN : Measurable (fun x : E d => ENNReal.ofReal (N x)) :=
    ENNReal.measurable_ofReal.comp (continuous_seminorm_Ed N).measurable
  have e1 : (∫⁻ p : E d × E d, ENNReal.ofReal (N p.1) ∂(μ.prod ν)) =
      ∫⁻ x, ENNReal.ofReal (N x) ∂μ := by
    conv_rhs => rw [← prod_fst_map μ ν]
    exact (lintegral_map hmN measurable_fst).symm
  have e2 : (∫⁻ p : E d × E d, ENNReal.ofReal (N p.2) ∂(μ.prod ν)) =
      ∫⁻ y, ENNReal.ofReal (N y) ∂ν := by
    conv_rhs => rw [← prod_snd_map μ ν]
    exact (lintegral_map hmN measurable_snd).symm
  calc ∫⁻ p, (‖N (p.1 - p.2)‖₊ : ENNReal) ∂(μ.prod ν)
    _ ≤ ∫⁻ p : E d × E d, (ENNReal.ofReal (N p.1) + ENNReal.ofReal (N p.2)) ∂(μ.prod ν) :=
        lintegral_mono hle
    _ = (∫⁻ p : E d × E d, ENNReal.ofReal (N p.1) ∂(μ.prod ν)) +
          ∫⁻ p : E d × E d, ENNReal.ofReal (N p.2) ∂(μ.prod ν) :=
        lintegral_add_left (hmN.comp measurable_fst) _
    _ < ⊤ := by
        rw [e1, e2]
        exact ENNReal.add_lt_top.mpr ⟨hμ, hν⟩

lemma coupling_bound {d : ℕ} (N : Seminorm ℝ (E d))
    (μ ν μ' ν' : Measure (E d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν']
    (hμ : FiniteFirstMoment N μ) (hν : FiniteFirstMoment N ν)
    (hμ' : FiniteFirstMoment N μ') (hν' : FiniteFirstMoment N ν')
    {γ₁ γ₂ : Measure (E d × E d)}
    (hγ₁ : γ₁ ∈ WassersteinDRO.StrongDuality.couplings μ μ')
    (hγ₂ : γ₂ ∈ WassersteinDRO.StrongDuality.couplings ν ν') :
    ENNReal.ofReal |totalDist N μ ν - totalDist N μ' ν'| ≤
      (∫⁻ q, ENNReal.ofReal (N (q.1 - q.2)) ∂γ₁) +
        ∫⁻ q, ENNReal.ofReal (N (q.1 - q.2)) ∂γ₂ := by
  rcases hγ₁ with ⟨hprob₁, hfst₁, hsnd₁⟩
  rcases hγ₂ with ⟨hprob₂, hfst₂, hsnd₂⟩
  have : IsProbabilityMeasure γ₁ := hprob₁
  have : IsProbabilityMeasure γ₂ := hprob₂
  let π := γ₁.prod γ₂
  let f₁ : (E d × E d) × (E d × E d) → E d × E d := Prod.map Prod.fst Prod.fst
  let f₂ : (E d × E d) × (E d × E d) → E d × E d := Prod.map Prod.snd Prod.snd
  have hf₁_meas : Measurable f₁ := measurable_fst.prodMap measurable_fst
  have hf₂_meas : Measurable f₂ := measurable_snd.prodMap measurable_snd
  have hmap₁ : π.map f₁ = μ.prod ν := by
    change (γ₁.prod γ₂).map (Prod.map Prod.fst Prod.fst) = μ.prod ν
    rw [← hfst₁, ← hfst₂]
    exact (Measure.map_prod_map γ₁ γ₂ measurable_fst measurable_fst).symm
  have hmap₂ : π.map f₂ = μ'.prod ν' := by
    change (γ₁.prod γ₂).map (Prod.map Prod.snd Prod.snd) = μ'.prod ν'
    rw [← hsnd₁, ← hsnd₂]
    exact (Measure.map_prod_map γ₁ γ₂ measurable_snd measurable_snd).symm
  have hint_μν := integrable_dist_prod N μ ν hμ hν
  have hint_μ'ν' := integrable_dist_prod N μ' ν' hμ' hν'
  have hint₁ : Integrable (fun r : (E d × E d) × (E d × E d) => N (r.1.1 - r.2.1)) π := by
    have h1 : Integrable (fun p : E d × E d => N (p.1 - p.2)) (π.map f₁) := hmap₁.symm ▸ hint_μν
    exact (integrable_map_measure h1.aestronglyMeasurable hf₁_meas.aemeasurable).mp h1
  have hint₂ : Integrable (fun r : (E d × E d) × (E d × E d) => N (r.1.2 - r.2.2)) π := by
    have h2 : Integrable (fun p : E d × E d => N (p.1 - p.2)) (π.map f₂) := hmap₂.symm ▸ hint_μ'ν'
    exact (integrable_map_measure h2.aestronglyMeasurable hf₂_meas.aemeasurable).mp h2
  have hL₁ : totalDist N μ ν = ∫ r, N (r.1.1 - r.2.1) ∂π := by
    unfold totalDist
    have h1 : Integrable (fun p : E d × E d => N (p.1 - p.2)) (π.map f₁) := hmap₁.symm ▸ hint_μν
    rw [← hmap₁, integral_map hf₁_meas.aemeasurable h1.aestronglyMeasurable]
    rfl
  have hL₂ : totalDist N μ' ν' = ∫ r, N (r.1.2 - r.2.2) ∂π := by
    unfold totalDist
    have h2 : Integrable (fun p : E d × E d => N (p.1 - p.2)) (π.map f₂) := hmap₂.symm ▸ hint_μ'ν'
    rw [← hmap₂, integral_map hf₂_meas.aemeasurable h2.aestronglyMeasurable]
    rfl
  have habs_le : |totalDist N μ ν - totalDist N μ' ν'| ≤
      ∫ r, |N (r.1.1 - r.2.1) - N (r.1.2 - r.2.2)| ∂π := by
    rw [hL₁, hL₂, ← integral_sub hint₁ hint₂]
    exact abs_integral_le_integral_abs
  have hint_diff : Integrable (fun r : (E d × E d) × (E d × E d) =>
      |N (r.1.1 - r.2.1) - N (r.1.2 - r.2.2)|) π := (hint₁.sub hint₂).abs
  have hofReal : ENNReal.ofReal |totalDist N μ ν - totalDist N μ' ν'| ≤
      ∫⁻ r, ENNReal.ofReal |N (r.1.1 - r.2.1) - N (r.1.2 - r.2.2)| ∂π := by
    calc ENNReal.ofReal |totalDist N μ ν - totalDist N μ' ν'|
      _ ≤ ENNReal.ofReal (∫ r, |N (r.1.1 - r.2.1) - N (r.1.2 - r.2.2)| ∂π) :=
          ENNReal.ofReal_le_ofReal habs_le
      _ = ∫⁻ r, ENNReal.ofReal |N (r.1.1 - r.2.1) - N (r.1.2 - r.2.2)| ∂π :=
          ofReal_integral_eq_lintegral_ofReal hint_diff (ae_of_all π fun _ => abs_nonneg _)
  have hpt : ∀ r : (E d × E d) × (E d × E d),
      ENNReal.ofReal |N (r.1.1 - r.2.1) - N (r.1.2 - r.2.2)| ≤
        ENNReal.ofReal (N (r.1.1 - r.1.2)) + ENNReal.ofReal (N (r.2.1 - r.2.2)) := by
    intro r
    rw [← ENNReal.ofReal_add (apply_nonneg N _) (apply_nonneg N _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := seminorm_abs_sub_le N (r.1.1 - r.2.1) (r.1.2 - r.2.2)
    have h2 : (r.1.1 - r.2.1) - (r.1.2 - r.2.2) = (r.1.1 - r.1.2) + -(r.2.1 - r.2.2) := by abel
    have h3 : N ((r.1.1 - r.2.1) - (r.1.2 - r.2.2)) ≤ N (r.1.1 - r.1.2) + N (r.2.1 - r.2.2) := by
      rw [h2]
      exact (map_add_le_add N _ _).trans_eq (by rw [map_neg_eq_map])
    exact h1.trans h3
  have hm_cost : Measurable (fun q : E d × E d => ENNReal.ofReal (N (q.1 - q.2))) :=
    ENNReal.measurable_ofReal.comp ((continuous_seminorm_Ed N).comp
      (continuous_fst.sub continuous_snd)).measurable
  have ec1 : (∫⁻ r : (E d × E d) × (E d × E d), ENNReal.ofReal (N (r.1.1 - r.1.2)) ∂(γ₁.prod γ₂)) =
      ∫⁻ q, ENNReal.ofReal (N (q.1 - q.2)) ∂γ₁ := by
    conv_rhs => rw [← prod_fst_map γ₁ γ₂]
    exact (lintegral_map hm_cost measurable_fst).symm
  have ec2 : (∫⁻ r : (E d × E d) × (E d × E d), ENNReal.ofReal (N (r.2.1 - r.2.2)) ∂(γ₁.prod γ₂)) =
      ∫⁻ q, ENNReal.ofReal (N (q.1 - q.2)) ∂γ₂ := by
    conv_rhs => rw [← prod_snd_map γ₁ γ₂]
    exact (lintegral_map hm_cost measurable_snd).symm
  calc ENNReal.ofReal |totalDist N μ ν - totalDist N μ' ν'|
    _ ≤ ∫⁻ r, (ENNReal.ofReal (N (r.1.1 - r.1.2)) + ENNReal.ofReal (N (r.2.1 - r.2.2))) ∂π :=
        hofReal.trans (lintegral_mono hpt)
    _ = (∫⁻ r, ENNReal.ofReal (N (r.1.1 - r.1.2)) ∂(γ₁.prod γ₂)) +
          ∫⁻ r, ENNReal.ofReal (N (r.2.1 - r.2.2)) ∂(γ₁.prod γ₂) :=
        lintegral_add_left (hm_cost.comp measurable_fst) _
    _ = (∫⁻ q, ENNReal.ofReal (N (q.1 - q.2)) ∂γ₁) +
          ∫⁻ q, ENNReal.ofReal (N (q.1 - q.2)) ∂γ₂ := by
        rw [ec1, ec2]

end Aux26

theorem solution (d : ℕ) (hd : 1 ≤ d) (N : Seminorm ℝ (E d)) (hN : ∀ x, N x = 0 → x = 0)
    (μ ν μ' ν' : Measure (E d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν']
    (hμ : FiniteFirstMoment N μ) (hν : FiniteFirstMoment N ν)
    (hμ' : FiniteFirstMoment N μ') (hν' : FiniteFirstMoment N ν') :
    ENNReal.ofReal |totalDist N μ ν - totalDist N μ' ν'| ≤ W1 N μ μ' + W1 N ν ν' := by
  have _ := hd
  have _ := hN
  set lhs := ENNReal.ofReal |totalDist N μ ν - totalDist N μ' ν'|
  have hstep1 : ∀ γ₁ ∈ WassersteinDRO.StrongDuality.couplings μ μ',
      lhs ≤ (∫⁻ q, ENNReal.ofReal (N (q.1 - q.2)) ∂γ₁) + W1 N ν ν' := by
    intro γ₁ hγ₁
    set c₁ := ∫⁻ q, ENNReal.ofReal (N (q.1 - q.2)) ∂γ₁
    rw [← tsub_le_iff_left]
    refine le_iInf₂ fun γ₂ hγ₂ => ?_
    rw [tsub_le_iff_left]
    exact Aux26.coupling_bound N μ ν μ' ν' hμ hν hμ' hν' hγ₁ hγ₂
  rw [add_comm, ← tsub_le_iff_left]
  refine le_iInf₂ fun γ₁ hγ₁ => ?_
  rw [tsub_le_iff_left, add_comm]
  exact hstep1 γ₁ hγ₁
