-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.exists_fixed_parameters_all_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:32:54.356673+00:00
-- url     : https://prove2.me/submissions/5ef02dac-7cb4-40fd-b0eb-f049a0ac610d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurableSet_finiteSuccess
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_finiteSuccess_ae
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_finiteSuccess_geometry
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_geometricParameters_nonempty


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
namespace QEC.Coding.BDL26FiniteEmbeddingExperiment
theorem _root_.solution (L : ℝ) :
    ∃ p : GeometricParameters L, ∀ n : ℕ,
      MeasurableSet (finiteSuccess p n) ∧
      ∀ᵐ z ∂experimentLaw p n, z ∈ finiteSuccess p n ∧
        ∀ i : Fin (n+1), PhysicalGeometry (perturbationOddScale p) i.val (history p n z i) p.t := by
  obtain ⟨p⟩ := geometricParameters_nonempty L
  refine ⟨p, fun n => ⟨measurableSet_finiteSuccess p n, ?_⟩⟩
  filter_upwards [finiteSuccess_ae p n] with z hz
  exact ⟨hz, finiteSuccess_geometry p n hz⟩
end QEC.Coding.BDL26FiniteEmbeddingExperiment
