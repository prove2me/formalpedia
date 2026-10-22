-- Prove2me | solution 1 for OnlineLearningOCO.OnlineToBatch.round_identity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:42:56.82884+00:00
-- url     : https://prove2.me/submissions/01f0128d-3060-4527-8656-16a9eb254ef6

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

end OTBAux

open OTBAux in
theorem solution {d : ℕ} {Ψ : Type*} [MeasurableSpace Ψ] (S : Set (EuclideanSpace ℝ (Fin d)))
    (Q : Measure Ψ) [IsProbabilityMeasure Q] (c : EuclideanSpace ℝ (Fin d) → Ψ → ℝ)
    (hc : IsCost S Q c) (A : (t : ℕ) → (Fin t → Ψ) → EuclideanSpace ℝ (Fin d))
    (hA : IsOnlineLearner S A)
    {T : ℕ} (t : Fin T) :
    ∫ ψ, c (iterate A ψ t) (ψ t) ∂(sampleLaw Q T) =
      ∫ ψ, risk Q c (iterate A ψ t) ∂(sampleLaw Q T) := by
  rw [toReal_lint _ _ (cost_iterate_meas Q c hc hA t) (fun ψ => hc.nonneg _ (iterate_mem hA ψ t) _),
    toReal_lint _ _ (risk_iterate_meas Q c hc hA t) (fun ψ => risk_nonneg Q c hc (iterate_mem hA ψ t)),
    round_lint Q c hc hA t]
