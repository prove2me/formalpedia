-- Prove2me | solution 1 for baxter_full
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:47:52.36581+00:00
-- url     : https://prove2.me/submissions/03741076-d7fb-49c5-a593-d380120098f4

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_Extended
public import Theorems.Thm_pac_lower_bound_member


set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (SML : SampleMetaLearner X)
    (C_new : ConceptClass X Bool)
    (d : ℕ) (hd : VCDim X C_new = d) (hd_pos : 1 ≤ d)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδ2 : δ ≤ 1 / 7)
    (n m : ℕ)
    (training_data : Fin n → Fin m → X × Bool)
    (hPAC : ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
      ∀ c ∈ C_new,
        let mf := SML.sampleComplexity n m ε δ
        MeasureTheory.Measure.pi
          (fun _ : Fin mf => D)
          { xs : Fin mf → X |
            D { x | (SML.learn training_data).learn (fun i => (xs i, c (xs i))) x ≠ c x }
              ≤ ENNReal.ofReal ε }
          ≥ ENNReal.ofReal (1 - δ)) :
    Nat.ceil ((d - 1 : ℝ) / 2) ≤ SML.sampleComplexity n m ε δ := by
  apply pac_lower_bound_member X C_new d hd ε δ hε hε1 hδ hδ1 hδ2 hd_pos
  exact ⟨SML.learn training_data, hPAC⟩
