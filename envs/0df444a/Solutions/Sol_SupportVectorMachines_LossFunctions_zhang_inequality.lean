-- Prove2me | solution 1 for SupportVectorMachines.LossFunctions.zhang_inequality
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:54:39.218312+00:00
-- url     : https://prove2.me/submissions/9a85efc3-042a-4801-9c67-89f299f1f08d

import Mathlib
import Definitions.Def_SupportVectorMachines_LossFunctions_RiskBasics
import Definitions.Def_SupportVectorMachines_LossFunctions_ClassificationLosses

open MeasureTheory

namespace SupportVectorMachines.LossFunctions

/-- A two-point type carrying the trivial σ-algebra. -/
def aux_zh_B : Type := Bool

instance aux_zh_inst : MeasurableSpace aux_zh_B := ⊥

def aux_zh_t : aux_zh_B := true

def aux_zh_f : aux_zh_B := false

theorem aux_zh_measurableSet {s : Set aux_zh_B} (hs : MeasurableSet s) :
    s = ∅ ∨ s = Set.univ :=
  MeasurableSpace.measurableSet_bot_iff.mp hs

theorem aux_zh_meas (μ : Measure aux_zh_B) [IsProbabilityMeasure μ] (s : Set aux_zh_B)
    (hs : s.Nonempty) : μ s = 1 := by
  rw [← measure_toMeasurable s]
  rcases aux_zh_measurableSet (measurableSet_toMeasurable μ s) with h | h
  · exfalso
    have hsub := subset_toMeasurable μ s
    rw [h] at hsub
    exact hs.ne_empty (Set.subset_empty_iff.mp hsub)
  · rw [h, measure_univ]

theorem aux_zh_const (g : aux_zh_B → ℝ) (hg : StronglyMeasurable g) (x : aux_zh_B) :
    g x = g aux_zh_t := by
  have hm : MeasurableSet (g ⁻¹' {g aux_zh_t}) :=
    hg.measurable (measurableSet_singleton _)
  rcases aux_zh_measurableSet hm with h | h
  · exfalso
    have : aux_zh_t ∈ g ⁻¹' {g aux_zh_t} := rfl
    rw [h] at this
    exact this
  · have : x ∈ g ⁻¹' {g aux_zh_t} := by rw [h]; exact Set.mem_univ x
    exact this

theorem aux_zh_not_int (μ : Measure aux_zh_B) [IsProbabilityMeasure μ] (g : aux_zh_B → ℝ)
    (hg : g aux_zh_t ≠ g aux_zh_f) : ¬ Integrable g μ := by
  intro hint
  obtain ⟨g', hg', hae⟩ := hint.aestronglyMeasurable
  have h0 : μ {a | ¬ g a = g' a} = 0 := ae_iff.mp hae
  have hne : ({a | ¬ g a = g' a} : Set aux_zh_B).Nonempty := by
    by_cases ht : g aux_zh_t = g' aux_zh_t
    · refine ⟨aux_zh_f, ?_⟩
      intro hf
      apply hg
      rw [ht, hf, aux_zh_const g' hg' aux_zh_f]
    · exact ⟨aux_zh_t, ht⟩
  rw [aux_zh_meas μ _ hne] at h0
  exact one_ne_zero h0

theorem aux_zh_integral_zero (μ : Measure aux_zh_B) [IsProbabilityMeasure μ]
    (g : aux_zh_B → ℝ) (hg : g aux_zh_t ≠ g aux_zh_f) : ∫ x, g x ∂μ = 0 :=
  integral_undef (aux_zh_not_int μ g hg)

end SupportVectorMachines.LossFunctions

open SupportVectorMachines.LossFunctions
open MeasureTheory

theorem solution : ¬ (∀ {X : Type} [MeasurableSpace X] (P : Measure (X × ℝ))
    [IsProbabilityMeasure P] (hY : P (Set.univ ×ˢ ({-1, 1} : Set ℝ)) = 1) (η : X → ℝ)
    (hη : ∀ A, MeasurableSet A →
      (P (A ×ˢ ({1} : Set ℝ))).toReal = ∫ x in A, η x ∂(P.map Prod.fst)),
    (∀ f : X → ℝ, Measurable f → (∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) →
        Integrable (fun p : X × ℝ => hingeLoss p.1 p.2 (f p.1)) P →
        risk hingeLoss P f - bayesRisk hingeLoss P =
          ∫ x, |f x - bayesClassifier η x| * |2 * η x - 1| ∂(P.map Prod.fst)) ∧
      ∀ f : X → ℝ, Measurable f →
        Integrable (fun p : X × ℝ => hingeLoss p.1 p.2 (f p.1)) P →
        Integrable (fun p : X × ℝ => classLoss p.1 p.2 (f p.1)) P →
        risk classLoss P f - bayesRisk classLoss P ≤
          risk hingeLoss P f - bayesRisk hingeLoss P) := by
  intro h
  set P : Measure (aux_zh_B × ℝ) := Measure.dirac (aux_zh_t, (-1 : ℝ)) with hP
  let η : aux_zh_B → ℝ := fun x => cond x (1 / 2) 0
  have hηt : η aux_zh_t = 1 / 2 := rfl
  have hηf : η aux_zh_f = 0 := rfl
  have hmarg : P.map Prod.fst = Measure.dirac aux_zh_t := by
    rw [hP, Measure.map_dirac' measurable_fst]
  have hY : P (Set.univ ×ˢ ({-1, 1} : Set ℝ)) = 1 :=
    Measure.dirac_apply_of_mem (by simp)
  have hη : ∀ A, MeasurableSet A →
      (P (A ×ˢ ({1} : Set ℝ))).toReal = ∫ x in A, η x ∂(P.map Prod.fst) := by
    intro A hA
    have hL : P (A ×ˢ ({1} : Set ℝ)) = 0 := by
      rw [hP, Measure.dirac_apply' _ (hA.prod (measurableSet_singleton _))]
      apply Set.indicator_of_notMem
      intro hmem
      have := hmem.2
      norm_num at this
    rw [hL, ENNReal.toReal_zero]
    rcases aux_zh_measurableSet hA with h' | h'
    · rw [h', Measure.restrict_empty, integral_zero_measure]
    · rw [h', Measure.restrict_univ, hmarg]
      exact (aux_zh_integral_zero _ η (by rw [hηt, hηf]; norm_num)).symm
  have h1 := (h P hY η hη).1 (fun _ => 0) measurable_const
    (fun _ => ⟨by norm_num, by norm_num⟩)
  have hconst : (fun p : aux_zh_B × ℝ => hingeLoss p.1 p.2 ((fun _ : aux_zh_B => (0 : ℝ)) p.1))
      = fun _ => (1 : ℝ) := by
    funext p
    simp [hingeLoss]
  have hint : Integrable
      (fun p : aux_zh_B × ℝ => hingeLoss p.1 p.2 ((fun _ : aux_zh_B => (0 : ℝ)) p.1)) P := by
    rw [hconst]
    exact integrable_const _
  have hrisk : risk hingeLoss P (fun _ => 0) = 1 := by
    unfold risk
    rw [hconst]
    simp
  have hbayes : bayesRisk hingeLoss P = 0 := by
    unfold bayesRisk
    apply IsLeast.csInf_eq
    constructor
    · refine ⟨fun _ => -1, measurable_const, ?_, ?_⟩
      · have hm : Measurable
            (fun p : aux_zh_B × ℝ => hingeLoss p.1 p.2 ((fun _ : aux_zh_B => (-1 : ℝ)) p.1)) := by
          unfold hingeLoss
          fun_prop
        rw [hP]
        exact integrable_dirac' hm.stronglyMeasurable enorm_lt_top
      · have hm : Measurable
            (fun p : aux_zh_B × ℝ => hingeLoss p.1 p.2 ((fun _ : aux_zh_B => (-1 : ℝ)) p.1)) := by
          unfold hingeLoss
          fun_prop
        unfold risk
        rw [hP, integral_dirac' _ _ hm.stronglyMeasurable]
        simp [hingeLoss]
    · rintro r ⟨f, -, -, rfl⟩
      unfold risk
      exact integral_nonneg (fun p => le_max_left _ _)
  have hrhs : ∫ x, |(fun _ : aux_zh_B => (0 : ℝ)) x - bayesClassifier η x| * |2 * η x - 1|
      ∂(P.map Prod.fst) = 0 := by
    rw [hmarg]
    apply aux_zh_integral_zero
    simp only [bayesClassifier, sgn, hηt, hηf]
    norm_num
  have := h1 hint
  rw [hrisk, hbayes, hrhs] at this
  norm_num at this
