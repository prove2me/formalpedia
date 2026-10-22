-- Prove2me | solution 1 for OnlineLearningOCO.OnlineToBatch.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:05:53.723675+00:00
-- url     : https://prove2.me/submissions/faeecbcb-b967-49c5-b457-d69f99b085d2

import Mathlib
import Definitions.Def_OnlineLearningOCO_OnlineToBatch_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory OnlineLearningOCO.OnlineToBatch

namespace OTBAux

/-- Independence turns the lintegral of a function of two independent variables into an iterated one. -/
lemma lint_indep {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (Y : Ω → β) (hX : Measurable X)
    (hY : Measurable Y) (hind : IndepFun X Y μ) (F : α × β → ENNReal) (hF : Measurable F) :
    ∫⁻ ω, F (X ω, Y ω) ∂μ = ∫⁻ ω, ∫⁻ y, F (X ω, y) ∂(μ.map Y) ∂μ := by
  have h1 : ∫⁻ ω, F (X ω, Y ω) ∂μ = ∫⁻ p, F p ∂(μ.map (fun ω => (X ω, Y ω))) := by
    rw [lintegral_map hF (hX.prodMk hY)]
  rw [h1, hind.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable,
    lintegral_prod _ hF.aemeasurable, lintegral_map _ hX]
  exact (hF.lintegral_prod_right')

lemma toReal_lint {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ)
    (hf : Measurable f) (h0 : ∀ ω, 0 ≤ f ω) :
    ∫ ω, f ω ∂μ = (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h0) hf.aestronglyMeasurable]

variable {d : ℕ} {Ψ : Type*} [MeasurableSpace Ψ]

lemma iterate_mem {S : Set (EuclideanSpace ℝ (Fin d))}
    {A : (t : ℕ) → (Fin t → Ψ) → EuclideanSpace ℝ (Fin d)} (hA : IsOnlineLearner S A)
    {T : ℕ} (ψ : Fin T → Ψ) (t : Fin T) : iterate A ψ t ∈ S := hA.mem _ _

lemma iterate_meas {S : Set (EuclideanSpace ℝ (Fin d))}
    {A : (t : ℕ) → (Fin t → Ψ) → EuclideanSpace ℝ (Fin d)} (hA : IsOnlineLearner S A)
    {T : ℕ} (t : Fin T) : Measurable (fun ψ : Fin T → Ψ => iterate A ψ t) := by
  unfold iterate
  refine (hA.measurable t).comp ?_
  exact measurable_pi_lambda _ (fun i => measurable_pi_apply _)

/-- the iterate as an `S`-valued map -/
lemma iterate_meas_S {S : Set (EuclideanSpace ℝ (Fin d))}
    {A : (t : ℕ) → (Fin t → Ψ) → EuclideanSpace ℝ (Fin d)} (hA : IsOnlineLearner S A)
    {T : ℕ} (t : Fin T) :
    Measurable (fun ψ : Fin T → Ψ => (⟨iterate A ψ t, iterate_mem hA ψ t⟩ : S)) :=
  (iterate_meas hA t).subtype_mk

lemma indep_iterate {S : Set (EuclideanSpace ℝ (Fin d))}
    {A : (t : ℕ) → (Fin t → Ψ) → EuclideanSpace ℝ (Fin d)} (hA : IsOnlineLearner S A)
    (Q : Measure Ψ) [IsProbabilityMeasure Q] {T : ℕ} (t : Fin T) :
    IndepFun (fun ψ : Fin T → Ψ => (⟨iterate A ψ t, iterate_mem hA ψ t⟩ : S))
      (fun ψ : Fin T → Ψ => ψ t) (sampleLaw Q T) := by
  have hind : iIndepFun (fun (i : Fin T) (ψ : Fin T → Ψ) => ψ i) (Measure.pi fun _ : Fin T => Q) :=
    iIndepFun_pi (μ := fun _ : Fin T => Q) (X := fun _ => id) (fun _ => aemeasurable_id)
  obtain ⟨Sf, hSf⟩ : ∃ Sf : Finset (Fin T), Sf = Finset.univ.filter (fun i => i.val < t.val) := ⟨_, rfl⟩
  have hdisj : Disjoint Sf ({t} : Finset (Fin T)) := by
    rw [Finset.disjoint_singleton_right, hSf]; simp
  have h := hind.indepFun_finset Sf {t} hdisj (fun i => measurable_pi_apply i)
  let g : (Sf → Ψ) → S := fun h =>
    ⟨A t (fun i : Fin t => h ⟨Fin.castLE t.isLt.le i, by rw [hSf]; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, i.isLt⟩⟩), hA.mem _ _⟩
  have hg : Measurable g := by
    refine Measurable.subtype_mk ((hA.measurable t).comp ?_)
    exact measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  let k : (({t} : Finset (Fin T)) → Ψ) → Ψ := fun h => h ⟨t, by simp⟩
  have hk : Measurable k := measurable_pi_apply _
  have := h.comp hg hk
  exact this

lemma round_lint {S : Set (EuclideanSpace ℝ (Fin d))}
    (Q : Measure Ψ) [IsProbabilityMeasure Q] (c : EuclideanSpace ℝ (Fin d) → Ψ → ℝ)
    (hc : IsCost S Q c) {A : (t : ℕ) → (Fin t → Ψ) → EuclideanSpace ℝ (Fin d)}
    (hA : IsOnlineLearner S A) {T : ℕ} (t : Fin T) :
    ∫⁻ ψ, ENNReal.ofReal (c (iterate A ψ t) (ψ t)) ∂(sampleLaw Q T) =
      ∫⁻ ψ, ENNReal.ofReal (risk Q c (iterate A ψ t)) ∂(sampleLaw Q T) := by
  have : IsProbabilityMeasure (sampleLaw Q T) := by unfold sampleLaw; infer_instance
  have hF : Measurable (fun p : S × Ψ => ENNReal.ofReal (c p.1 p.2)) :=
    ENNReal.measurable_ofReal.comp hc.measurable
  have key := lint_indep (sampleLaw Q T) _ _ (iterate_meas_S hA t) (measurable_pi_apply t)
    (indep_iterate hA Q t) _ hF
  have hmap : (sampleLaw Q T).map (fun ψ : Fin T → Ψ => ψ t) = Q := by
    unfold sampleLaw
    exact (measurePreserving_eval (fun _ : Fin T => Q) t).map_eq
  simp only [hmap] at key
  refine key.trans ?_
  refine lintegral_congr (fun ψ => ?_)
  have hs := iterate_mem hA ψ t
  unfold risk
  rw [ofReal_integral_eq_lintegral_ofReal (hc.integrable _ hs)
    (Filter.Eventually.of_forall (fun y => hc.nonneg _ hs y))]

lemma risk_nonneg {S : Set (EuclideanSpace ℝ (Fin d))}
    (Q : Measure Ψ) (c : EuclideanSpace ℝ (Fin d) → Ψ → ℝ)
    (hc : IsCost S Q c) {w : EuclideanSpace ℝ (Fin d)} (hw : w ∈ S) : 0 ≤ risk Q c w :=
  integral_nonneg (fun y => hc.nonneg _ hw y)

lemma risk_meas {S : Set (EuclideanSpace ℝ (Fin d))}
    (Q : Measure Ψ) [IsProbabilityMeasure Q] (c : EuclideanSpace ℝ (Fin d) → Ψ → ℝ)
    (hc : IsCost S Q c) : Measurable (fun s : S => risk Q c s) := by
  have : StronglyMeasurable (Function.uncurry (fun (s : S) (y : Ψ) => c s y)) :=
    hc.measurable.stronglyMeasurable
  exact (this.integral_prod_right (ν := Q)).measurable

lemma risk_iterate_meas {S : Set (EuclideanSpace ℝ (Fin d))}
    (Q : Measure Ψ) [IsProbabilityMeasure Q] (c : EuclideanSpace ℝ (Fin d) → Ψ → ℝ)
    (hc : IsCost S Q c) {A : (t : ℕ) → (Fin t → Ψ) → EuclideanSpace ℝ (Fin d)}
    (hA : IsOnlineLearner S A) {T : ℕ} (t : Fin T) :
    Measurable (fun ψ : Fin T → Ψ => risk Q c (iterate A ψ t)) :=
  (risk_meas Q c hc).comp (iterate_meas_S hA t)

lemma cost_iterate_meas {S : Set (EuclideanSpace ℝ (Fin d))}
    (Q : Measure Ψ) (c : EuclideanSpace ℝ (Fin d) → Ψ → ℝ)
    (hc : IsCost S Q c) {A : (t : ℕ) → (Fin t → Ψ) → EuclideanSpace ℝ (Fin d)}
    (hA : IsOnlineLearner S A) {T : ℕ} (t : Fin T) :
    Measurable (fun ψ : Fin T → Ψ => c (iterate A ψ t) (ψ t)) :=
  hc.measurable.comp ((iterate_meas_S hA t).prodMk (measurable_pi_apply t))

lemma meas_avg {Ω : Type*} [MeasurableSpace Ω] (T : ℕ) (g : Fin T → Ω → ℝ)
    (hg : ∀ t, Measurable (g t)) : Measurable (fun ω => (1 / (T : ℝ)) * ∑ t : Fin T, g t ω) := by
  have : Measurable (fun ω => ∑ t : Fin T, g t ω) := by
    have := Finset.measurable_sum (Finset.univ : Finset (Fin T)) (fun t _ => hg t)
    simpa [Finset.sum_apply] using this
  exact this.const_mul _

lemma lint_avg {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (T : ℕ) (hT : 0 < T)
    (g : Fin T → Ω → ℝ) (hg : ∀ t, Measurable (g t)) (h0 : ∀ t ω, 0 ≤ g t ω) :
    ∫⁻ ω, ENNReal.ofReal ((1 / (T : ℝ)) * ∑ t : Fin T, g t ω) ∂μ =
      ENNReal.ofReal (1 / (T : ℝ)) * ∑ t : Fin T, ∫⁻ ω, ENNReal.ofReal (g t ω) ∂μ := by
  have : ∀ ω, ENNReal.ofReal ((1 / (T : ℝ)) * ∑ t : Fin T, g t ω) =
      ENNReal.ofReal (1 / (T : ℝ)) * ∑ t : Fin T, ENNReal.ofReal (g t ω) := by
    intro ω
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg (fun t _ => h0 t ω)]
  simp_rw [this]
  rw [lintegral_const_mul _ (Finset.measurable_sum _ (fun t _ => (hg t).ennreal_ofReal)),
    lintegral_finsetSum _ (fun t _ => (hg t).ennreal_ofReal)]


lemma ofReal_inv_T (T : ℕ) (hT : 0 < T) : ENNReal.ofReal (1 / (T : ℝ)) = (T : ENNReal)⁻¹ := by
  rw [one_div, ENNReal.ofReal_inv_of_pos (by exact_mod_cast hT)]
  simp

lemma lint_unif (T : ℕ) (f : Fin T → ENNReal) :
    ∫⁻ r, f r ∂(uniformIndex T) = (T : ENNReal)⁻¹ * ∑ r, f r := by
  unfold uniformIndex
  rw [lintegral_smul_measure, lintegral_count, tsum_fintype]
  rfl

lemma eq51 {S : Set (EuclideanSpace ℝ (Fin d))}
    (Q : Measure Ψ) [IsProbabilityMeasure Q] (c : EuclideanSpace ℝ (Fin d) → Ψ → ℝ)
    (hc : IsCost S Q c) {A : (t : ℕ) → (Fin t → Ψ) → EuclideanSpace ℝ (Fin d)}
    (hA : IsOnlineLearner S A) (T : ℕ) (hT : 0 < T) :
    ∫ ψ, (1 / (T : ℝ)) * ∑ t : Fin T, risk Q c (iterate A ψ t) ∂(sampleLaw Q T) =
      ∫ ψ, (1 / (T : ℝ)) * ∑ t : Fin T, c (iterate A ψ t) (ψ t) ∂(sampleLaw Q T) := by
  have h1 : ∀ ψ : Fin T → Ψ, 0 ≤ (1 / (T : ℝ)) * ∑ t : Fin T, risk Q c (iterate A ψ t) :=
    fun ψ => mul_nonneg (by positivity)
      (Finset.sum_nonneg (fun t _ => risk_nonneg Q c hc (iterate_mem hA ψ t)))
  have h2 : ∀ ψ : Fin T → Ψ, 0 ≤ (1 / (T : ℝ)) * ∑ t : Fin T, c (iterate A ψ t) (ψ t) :=
    fun ψ => mul_nonneg (by positivity)
      (Finset.sum_nonneg (fun t _ => hc.nonneg _ (iterate_mem hA ψ t) _))
  rw [toReal_lint _ _ (meas_avg T _ (fun t => risk_iterate_meas Q c hc hA t)) h1,
    toReal_lint _ _ (meas_avg T _ (fun t => cost_iterate_meas Q c hc hA t)) h2,
    lint_avg _ T hT _ (fun t => risk_iterate_meas Q c hc hA t)
      (fun t ψ => risk_nonneg Q c hc (iterate_mem hA ψ t)),
    lint_avg _ T hT _ (fun t => cost_iterate_meas Q c hc hA t)
      (fun t ψ => hc.nonneg _ (iterate_mem hA ψ t) _)]
  congr 2
  refine Finset.sum_congr rfl (fun t _ => ?_)
  exact (round_lint Q c hc hA t).symm

lemma rand_meas {S : Set (EuclideanSpace ℝ (Fin d))}
    {A : (t : ℕ) → (Fin t → Ψ) → EuclideanSpace ℝ (Fin d)} (hA : IsOnlineLearner S A)
    (T : ℕ) :
    Measurable (fun p : (Fin T → Ψ) × Fin T => (⟨randomizedOutput A p.1 p.2, iterate_mem hA p.1 p.2⟩ : S)) :=
  measurable_from_prod_countable_left (fun r => iterate_meas_S hA r)

lemma thm51a {S : Set (EuclideanSpace ℝ (Fin d))}
    (Q : Measure Ψ) [IsProbabilityMeasure Q] (c : EuclideanSpace ℝ (Fin d) → Ψ → ℝ)
    (hc : IsCost S Q c) {A : (t : ℕ) → (Fin t → Ψ) → EuclideanSpace ℝ (Fin d)}
    (hA : IsOnlineLearner S A) (T : ℕ) (hT : 0 < T) :
    ∫ p, risk Q c (randomizedOutput A p.1 p.2) ∂((sampleLaw Q T).prod (uniformIndex T)) =
        ∫ ψ, avgOnlineLoss c A ψ ∂(sampleLaw Q T) := by
  have hU : IsProbabilityMeasure (uniformIndex T) := by
    constructor
    unfold uniformIndex
    obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
    simp [Measure.count_univ]
    exact ENNReal.inv_mul_cancel (by simp) (by simp)
  have hmeas : Measurable (fun p : (Fin T → Ψ) × Fin T => risk Q c (randomizedOutput A p.1 p.2)) :=
    (risk_meas Q c hc).comp (rand_meas hA T)
  have h0 : ∀ p : (Fin T → Ψ) × Fin T, 0 ≤ risk Q c (randomizedOutput A p.1 p.2) :=
    fun p => risk_nonneg Q c hc (iterate_mem hA p.1 p.2)
  have h2 : ∀ ψ : Fin T → Ψ, 0 ≤ avgOnlineLoss c A ψ :=
    fun ψ => mul_nonneg (by positivity)
      (Finset.sum_nonneg (fun t _ => hc.nonneg _ (iterate_mem hA ψ t) _))
  rw [toReal_lint _ _ hmeas h0]
  unfold avgOnlineLoss
  rw [toReal_lint _ _ (meas_avg T _ (fun t => cost_iterate_meas Q c hc hA t)) h2,
    lint_avg _ T hT _ (fun t => cost_iterate_meas Q c hc hA t)
      (fun t ψ => hc.nonneg _ (iterate_mem hA ψ t) _)]
  congr 1
  rw [lintegral_prod (fun p : (Fin T → Ψ) × Fin T => ENNReal.ofReal (risk Q c (randomizedOutput A p.1 p.2)))
    (ENNReal.measurable_ofReal.comp hmeas).aemeasurable]
  simp_rw [lint_unif]
  have : ∀ ψ : Fin T → Ψ, ∑ r : Fin T, ENNReal.ofReal (risk Q c (randomizedOutput A (ψ, r).1 (ψ, r).2)) = ∑ r : Fin T, ENNReal.ofReal (risk Q c (iterate A ψ r)) := fun ψ => rfl
  simp_rw [this]
  rw [lintegral_const_mul _ (Finset.measurable_sum _ (fun t _ => (risk_iterate_meas Q c hc hA t).ennreal_ofReal)),
    lintegral_finsetSum _ (fun t _ => (risk_iterate_meas Q c hc hA t).ennreal_ofReal), ofReal_inv_T T hT]
  have hs : ∑ t : Fin T, ∫⁻ ψ, ENNReal.ofReal (risk Q c (iterate A ψ t)) ∂(sampleLaw Q T) =
      ∑ t : Fin T, ∫⁻ ψ, ENNReal.ofReal (c (iterate A ψ t) (ψ t)) ∂(sampleLaw Q T) :=
    Finset.sum_congr rfl (fun t _ => (round_lint Q c hc hA t).symm)
  rw [hs]

lemma int_risk_iterate {S : Set (EuclideanSpace ℝ (Fin d))}
    (Q : Measure Ψ) [IsProbabilityMeasure Q] (c : EuclideanSpace ℝ (Fin d) → Ψ → ℝ)
    (hc : IsCost S Q c) {A : (t : ℕ) → (Fin t → Ψ) → EuclideanSpace ℝ (Fin d)}
    (hA : IsOnlineLearner S A) {T : ℕ} (t : Fin T)
    (hint : Integrable (fun ψ => c (iterate A ψ t) (ψ t)) (sampleLaw Q T)) :
    Integrable (fun ψ => risk Q c (iterate A ψ t)) (sampleLaw Q T) := by
  rw [← lintegral_ofReal_ne_top_iff_integrable (risk_iterate_meas Q c hc hA t).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ψ => risk_nonneg Q c hc (iterate_mem hA ψ t))), ← round_lint Q c hc hA t]
  exact (lintegral_ofReal_ne_top_iff_integrable (cost_iterate_meas Q c hc hA t).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ψ => hc.nonneg _ (iterate_mem hA ψ t) _))).2 hint

lemma thm51b {S : Set (EuclideanSpace ℝ (Fin d))}
    (Q : Measure Ψ) [IsProbabilityMeasure Q] (c : EuclideanSpace ℝ (Fin d) → Ψ → ℝ)
    (hc : IsCost S Q c) {A : (t : ℕ) → (Fin t → Ψ) → EuclideanSpace ℝ (Fin d)}
    (hA : IsOnlineLearner S A) (T : ℕ) (hT : 0 < T)
    (hSc : Convex ℝ S) (hrc : ConvexOn ℝ S (risk Q c))
    (hint : ∀ t : Fin T, Integrable (fun ψ => c (iterate A ψ t) (ψ t)) (sampleLaw Q T)) :
    ∫ ψ, risk Q c (averageOutput A ψ) ∂(sampleLaw Q T) ≤
          ∫ ψ, avgOnlineLoss c A ψ ∂(sampleLaw Q T) := by
  have hgi : Integrable (fun ψ => (1 / (T : ℝ)) * ∑ t : Fin T, risk Q c (iterate A ψ t)) (sampleLaw Q T) :=
    (integrable_finset_sum _ (fun t _ => int_risk_iterate Q c hc hA t (hint t))).const_mul _
  have hav : ∀ ψ : Fin T → Ψ, averageOutput A ψ = ∑ t : Fin T, (1 / (T : ℝ)) • iterate A ψ t := by
    intro ψ; unfold averageOutput; rw [Finset.smul_sum]
  have hmem : ∀ ψ : Fin T → Ψ, averageOutput A ψ ∈ S := by
    intro ψ
    rw [hav]
    exact hSc.sum_mem (fun t _ => by positivity) (by simp; field_simp) (fun t _ => iterate_mem hA ψ t)
  have hle : ∀ ψ : Fin T → Ψ, risk Q c (averageOutput A ψ) ≤ (1 / (T : ℝ)) * ∑ t : Fin T, risk Q c (iterate A ψ t) := by
    intro ψ
    rw [hav]
    have := hrc.map_sum_le (t := Finset.univ) (w := fun _ : Fin T => (1 / (T : ℝ)))
      (p := fun t => iterate A ψ t) (fun t _ => by positivity) (by simp; field_simp)
      (fun t _ => iterate_mem hA ψ t)
    simpa [smul_eq_mul, ← Finset.mul_sum] using this
  calc ∫ ψ, risk Q c (averageOutput A ψ) ∂(sampleLaw Q T)
      ≤ ∫ ψ, (1 / (T : ℝ)) * ∑ t : Fin T, risk Q c (iterate A ψ t) ∂(sampleLaw Q T) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (fun ψ => risk_nonneg Q c hc (hmem ψ)))
          hgi (Filter.Eventually.of_forall hle)
    _ = _ := eq51 Q c hc hA T hT

lemma int_comparator {S : Set (EuclideanSpace ℝ (Fin d))}
    (Q : Measure Ψ) [IsProbabilityMeasure Q] (c : EuclideanSpace ℝ (Fin d) → Ψ → ℝ)
    (hc : IsCost S Q c) (T : ℕ) (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ S) (t : Fin T) :
    Integrable (fun ψ : Fin T → Ψ => c u (ψ t)) (sampleLaw Q T) ∧
      ∫ ψ, c u (ψ t) ∂(sampleLaw Q T) = risk Q c u := by
  have hmp : MeasurePreserving (fun ψ : Fin T → Ψ => ψ t) (sampleLaw Q T) Q := by
    unfold sampleLaw
    exact measurePreserving_eval (fun _ : Fin T => Q) t
  refine ⟨hmp.integrable_comp_of_integrable (hc.integrable u hu), ?_⟩
  have hm : Measurable (fun y => c u y) :=
    hc.measurable.comp (measurable_const.prodMk measurable_id (f := fun y : Ψ => (⟨u, hu⟩ : S)))
  have := integral_map (μ := sampleLaw Q T) (φ := fun ψ : Fin T → Ψ => ψ t) (measurable_pi_apply t).aemeasurable
    (f := fun y => c u y) (by rw [hmp.map_eq]; exact hm.aestronglyMeasurable)
  rw [hmp.map_eq] at this
  exact this.symm.trans rfl

end OTBAux

open OTBAux in
theorem solution {d : ℕ} {Ψ : Type*} [MeasurableSpace Ψ] (S : Set (EuclideanSpace ℝ (Fin d)))
    (Q : Measure Ψ) [IsProbabilityMeasure Q] (c : EuclideanSpace ℝ (Fin d) → Ψ → ℝ)
    (hc : IsCost S Q c) (A : (t : ℕ) → (Fin t → Ψ) → EuclideanSpace ℝ (Fin d))
    (hA : IsOnlineLearner S A)
    (T : ℕ) (hT : 0 < T) :
    (∫ p, risk Q c (randomizedOutput A p.1 p.2) ∂((sampleLaw Q T).prod (uniformIndex T)) =
        ∫ ψ, avgOnlineLoss c A ψ ∂(sampleLaw Q T)) ∧
      (Convex ℝ S → ConvexOn ℝ S (risk Q c) →
        (∀ t : Fin T, Integrable (fun ψ => c (iterate A ψ t) (ψ t)) (sampleLaw Q T)) →
        ∫ ψ, risk Q c (averageOutput A ψ) ∂(sampleLaw Q T) ≤
          ∫ ψ, avgOnlineLoss c A ψ ∂(sampleLaw Q T)) :=
  ⟨thm51a Q c hc hA T hT, fun h1 h2 h3 => thm51b Q c hc hA T hT h1 h2 h3⟩
