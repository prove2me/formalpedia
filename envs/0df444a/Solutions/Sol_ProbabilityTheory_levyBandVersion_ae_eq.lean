-- Prove2me | solution 1 for ProbabilityTheory.levyBandVersion_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T12:03:18.691057+00:00
-- url     : https://prove2.me/submissions/34a9e899-01ba-4887-9c09-bc37fffe161d

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Theorems.Thm_ProbabilityTheory_aestronglyMeasurable_levyBandPath_band
import Theorems.Thm_ProbabilityTheory_levyBandPath_ae_eq_compensated
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ}
  {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω}
  {A : Set ℝ}

theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) (hAfin : ν A < ⊤) (t : ℝ≥0) :
    levyBandVersion hd hν hA hAsub hAfin t =ᵐ[μ] fun ω => levyBandPath K X ν A (t : ℝ) ω := by
  have hsub : Set.Ioc 0 (t : ℝ) ×ˢ Set.univ ⊆ Set.Iic (t : ℝ) ×ˢ (Set.univ : Set ℝ) :=
    Set.prod_mono Set.Ioc_subset_Iic_self (subset_refl _)
  have hprefix := (aestronglyMeasurable_levyBandPath_band hd hA hAsub hAfin 0 (t : ℝ)).mono
    (prmEvalSigma_mono hsub)
  change hprefix.mk _ =ᵐ[μ] fun ω => levyBandPath K X ν A (t : ℝ) ω
  exact hprefix.ae_eq_mk.symm.trans
    (levyBandPath_ae_eq_compensated hd hA hAsub hAfin (NNReal.coe_nonneg t)).symm
