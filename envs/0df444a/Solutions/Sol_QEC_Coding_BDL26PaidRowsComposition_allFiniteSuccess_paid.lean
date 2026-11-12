-- Prove2me | solution 1 for QEC.Coding.BDL26PaidRowsComposition.allFiniteSuccess_paid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:11:10.834844+00:00
-- url     : https://prove2.me/submissions/22307578-712a-4745-894d-7cb86e5a4422

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_streamTotalCost_finite_iff
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_allFiniteSuccess_geometry
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_allFiniteSuccess_halts
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_allFiniteSuccess_stageFacts


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PaidRowsComposition
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26ReplacementMaterialization BDL26IncomingRowsExecution
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
namespace QEC.Coding.BDL26PaidRowsComposition
theorem _root_.solution {L : ℝ} (p : GeometricParameters L)
    {omega : BDL26CountableEmbeddingExperiment.Omega p}
    (h : omega ∈ BDL26CountableEmbeddingExperiment.allFiniteSuccess p) :
    (∀ N, streamTotalCost p N omega < ∞) ∧
      (∀ n, PhysicalSuccessorFacts p n (BDL26CountableEmbeddingExperiment.levelMap p omega n) (omega n)) ∧
      ∀ n, PhysicalGeometry (perturbationOddScale p) n
        (BDL26CountableEmbeddingExperiment.levelMap p omega n) p.t :=
  ⟨fun N => (streamTotalCost_finite_iff p N omega).mpr
      (fun i => BDL26CountableEmbeddingExperiment.allFiniteSuccess_halts p h i.val),
    BDL26CountableEmbeddingExperiment.allFiniteSuccess_stageFacts p h,
    BDL26CountableEmbeddingExperiment.allFiniteSuccess_geometry p h⟩
end QEC.Coding.BDL26PaidRowsComposition
