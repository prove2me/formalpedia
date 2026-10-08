-- Prove2me | solution 1 for OptimalPAC.SampleComplexity.sampleComplexity_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T04:36:13.763786+00:00
-- url     : https://prove2.me/submissions/5737755f-a11d-486c-9166-db6f49f17cf8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OptimalPAC_SampleComplexity_Model
import Definitions.Def_OptimalPAC_SampleComplexity_Algorithm
import Theorems.Thm_OptimalPAC_SampleComplexity_hanneke_learner_pac

set_option autoImplicit false

open MeasureTheory

namespace R1b0af

open OptimalPAC.SampleComplexity

open scoped ENNReal

theorem g1b_meas_count {X : Type*} [MeasurableSpace X] (L : List (X → Bool))
    (p : (X → Bool) → X → Bool) (hp : ∀ h ∈ L, MeasurableSet {x | p h x = true}) :
    Measurable (fun x => ((L.countP (fun h => p h x) : ℕ) : ℝ≥0∞)) := by
  induction L with
  | nil => simp
  | cons a l ih =>
    have ih' := ih (fun h hh => hp h (List.mem_cons_of_mem a hh))
    have ha := hp a List.mem_cons_self
    simp only [List.countP_cons, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    exact ih'.add (Measurable.ite ha measurable_const measurable_const)

theorem g1b_meas_majority {X : Type*} [MeasurableSpace X] (L : List (X → Bool))
    (hL : ∀ h ∈ L, Measurable h) : Measurable (majority L) := by
  apply measurable_to_bool
  have h1 := g1b_meas_count L (fun h x => decide (h x = false))
    (fun h hh => by
      convert (hL h hh) (measurableSet_singleton false) using 1
      ext x; simp)
  have h2 := g1b_meas_count L (fun h x => decide (h x = true))
    (fun h hh => by
      convert (hL h hh) (measurableSet_singleton true) using 1
      ext x; simp)
  have : majority L ⁻¹' {true} =
      {x | ((L.countP (fun h => decide (h x = false)) : ℕ) : ℝ≥0∞) ≤
        ((L.countP (fun h => decide (h x = true)) : ℕ) : ℝ≥0∞)} := by
    ext x; simp [majority]
  rw [this]
  exact measurableSet_le h1 h2

theorem g1b_meas_learner {X : Type*} [MeasurableSpace X] (L : List (X × Bool) → X → Bool)
    (hLm : LearnerMeasurable L) (S : List (X × Bool)) : Measurable (L S) := by
  have h := (hLm S.length).comp (measurable_const.prodMk measurable_id :
    Measurable (fun x : X => ((fun i : Fin S.length => S.get i), x)))
  have e : (fun p : (Fin S.length → X × Bool) × X => L (List.ofFn p.1) p.2) ∘
      (fun x : X => ((fun i : Fin S.length => S.get i), x)) = L S := by
    funext x; simp
  rwa [e] at h

/-- Glue: Theorem 2 follows from the PAC property of Hanneke's learner at the sample size
`⌊1800/ε (d + ln(18/δ))⌋` (the statement of `hanneke_learner_pac`, taken as a hypothesis). -/
theorem g1b_sampleComplexity_le_of_pac {X : Type*} [MeasurableSpace X] (C : Set (X → Bool))
    (ε δ : ℝ) (m₀ : ℕ) (L : List (X × Bool) → X → Bool) (hLm : LearnerMeasurable L)
    (hpac : ∀ (P : Measure X) [IsProbabilityMeasure P] (f : X → Bool), f ∈ C →
      Measure.pi (fun _ : Fin m₀ => P)
        {x | ε < er P (hannekeLearner L (labeled f x) []) f} ≤ ENNReal.ofReal δ) :
    sampleComplexity C ε δ ≤ (m₀ : ℕ∞) := by
  unfold sampleComplexity
  refine iInf₂_le m₀ ⟨fun S => hannekeLearner L S [], fun S => ?_, fun P hP f hf => ?_⟩
  · unfold hannekeLearner
    apply g1b_meas_majority
    intro h hh
    obtain ⟨S', -, rfl⟩ := List.mem_map.mp hh
    exact g1b_meas_learner L hLm S'
  · exact @hpac P hP f hf

end R1b0af

open OptimalPAC.SampleComplexity in
theorem solution {X : Type*} [MeasurableSpace X] (C : Set (X → Bool))
    (hCm : ∀ h ∈ C, Measurable h) (hC3 : 3 ≤ C.encard) (d : ℕ) (hd : vcDim C = d)
    (hWB : WellBehaved C)
    (hL : ∃ L : List (X × Bool) → X → Bool, IsConsistentLearner C L ∧ LearnerMeasurable L)
    (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    sampleComplexity C ε δ ≤ ((⌊1800 / ε * (d + Real.log (18 / δ))⌋₊ : ℕ) : ℕ∞) := by
  obtain ⟨L, hLc, hLm⟩ := hL
  exact R1b0af.g1b_sampleComplexity_le_of_pac C ε δ _ L hLm (fun P _ f hf =>
    hanneke_learner_pac C hCm hC3 d hd hWB L hLc hLm P f hf ε δ hε0 hε1 hδ0 hδ1 _ le_rfl)
