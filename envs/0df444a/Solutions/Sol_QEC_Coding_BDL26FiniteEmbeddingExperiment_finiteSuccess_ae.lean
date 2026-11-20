-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.finiteSuccess_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:17:06.29002+00:00
-- url     : https://prove2.me/submissions/7ae44b27-f4e1-4bc2-944e-09b06145af3d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stageFacts_ae
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_history_good_ae
import Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seed_parameter_localMap


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    ∀ᵐ z ∂experimentLaw p n, z ∈ finiteSuccess p n := by
  have hhalts : ∀ᵐ z ∂experimentLaw p n, ∀ i : Fin n, stageHalts p n i z := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [stageFacts_ae p n i] with z hz
    exact hz.1
  have hgood : ∀ᵐ z ∂experimentLaw p n, ∀ i : Fin (n+1),
      IsBoundedDensityLocalMap (StagePresentation p i.val) (history p n z i) p.t :=
    ae_all_iff.mpr (history_good_ae p n)
  filter_upwards [hhalts, hgood] with z hh hg
  exact ⟨BDL26RandomSeedEmbedding.seed_parameter_localMap p, hh, hg⟩
end QEC.Coding.BDL26FiniteEmbeddingExperiment
