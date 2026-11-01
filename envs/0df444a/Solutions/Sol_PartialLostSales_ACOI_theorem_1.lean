-- Prove2me | solution 1 for PartialLostSales.ACOI.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T10:43:24.234988+00:00
-- url     : https://prove2.me/submissions/d6266faa-1465-4150-81e6-5f318736f4bd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_PartialLostSales_ACOI_Model
import Theorems.Thm_PartialLostSales_ACOI_lemma_2
import Theorems.Thm_PartialLostSales_ACOI_lemma_3
import Theorems.Thm_PartialLostSales_ACOI_theorem_2
import Theorems.Thm_PartialLostSales_ACOI_wstar_holds
import Theorems.Thm_ProbabilityMeasureSpace_secondCountableTopology
import Theorems.Thm_ProbabilityMeasureSpace_borelSpace
import Theorems.Thm_ProbabilityMeasureSpace_standardBorelSpace

open MeasureTheory ProbabilityTheory Filter Topology FeinbergLiang.ACOE
open scoped ENNReal NNReal

open PartialLostSales.ACOI in
theorem solution (P : Params) (hP : Standing P) (M : MDP (Bel P) (Act P))
    (hM : IsCOMDP P M) :
    ∃ αs : ℕ → ℝ, IsDiscountSeq αs ∧
    ∃ φ : Bel P → Act P, ∃ hφ : Measurable φ,
      IsAvgOptimal M (Policy.ofStationary φ hφ) ∧
      (⨅ z, wOpt M z) ≠ ⊤ ∧ (∀ z, uTilde M αs z ≠ ⊤) ∧
      ∀ z, M.cost z (φ z) + ∫⁻ s, uTilde M αs s ∂(M.q (z, φ z)) ≤
        (⨅ z, wOpt M z) + uTilde M αs z := by
  haveI : SecondCountableTopology (ProbabilityMeasure ℝ≥0) :=
    ProbabilityMeasureSpace.secondCountableTopology
  haveI : BorelSpace (ProbabilityMeasure ℝ≥0) := ProbabilityMeasureSpace.borelSpace
  haveI : StandardBorelSpace (ProbabilityMeasure ℝ≥0) :=
    ProbabilityMeasureSpace.standardBorelSpace
  haveI : TopologicalSpace.MetrizableSpace (Bel P) := TopologicalSpace.MetrizableSpace.subtype _
  haveI : SecondCountableTopology (Bel P) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : BorelSpace (Bel P) := Subtype.borelSpace _
  have hmeas : MeasurableSet {z : ProbabilityMeasure ℝ≥0 | secondMoment (z : Measure ℝ≥0) < ⊤} := by
    have h1 : Measurable (fun z : ProbabilityMeasure ℝ≥0 => secondMoment (z : Measure ℝ≥0)) := by
      unfold secondMoment
      exact (Measure.measurable_lintegral (by fun_prop)).comp measurable_subtype_coe
    exact h1 measurableSet_Iio
  haveI : StandardBorelSpace (Bel P) := hmeas.standardBorel
  obtain ⟨-, αs, hαs, φ, hφ, hopt, hw, hu, hacoi⟩ :=
    lemma_2 M (wstar_holds P hP M hM) ⟨lemma_3 P hP M hM, theorem_2 P hP M hM⟩
  exact ⟨αs, hαs, φ, hφ, hopt, hw, hu, hacoi⟩
