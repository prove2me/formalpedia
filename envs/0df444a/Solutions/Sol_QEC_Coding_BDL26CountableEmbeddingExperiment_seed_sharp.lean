-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.seed_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:21:47.749642+00:00
-- url     : https://prove2.me/submissions/602bce14-0ff3-49e2-8113-313cbee1515a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seed_physical_card
import Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seed_physical_distance_zero
import Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seed_qubit_density


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26ReplacementEmbedding BDL26RandomPerturbation BDL26RandomPhysicalLocality
open BDL26CSSHamiltonian Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
namespace QEC.Coding.BDL26CountableEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (omega : Omega p) :
    Fintype.card (Physical (perturbationOddScale p) 0) = 5 ∧
    (∀ q : Physical (perturbationOddScale p) 0, levelMap p omega 0 (.q q) = 0) ∧
    (∀ r s : Physical (perturbationOddScale p) 0,
      dist (levelMap p omega 0 (.q r)) (levelMap p omega 0 (.q s)) = 0) ∧
    ∀ c, ((qubitHits (StagePresentation p 0) (levelMap p omega 0)
      (Metric.closedBall c 1)).card : ℝ) ≤ 5 :=
  ⟨BDL26RandomSeedEmbedding.seed_physical_card _, fun _ => rfl,
    BDL26RandomSeedEmbedding.seed_physical_distance_zero _,
    BDL26RandomSeedEmbedding.seed_qubit_density _⟩
end QEC.Coding.BDL26CountableEmbeddingExperiment
