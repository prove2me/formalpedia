-- Prove2me | solution 1 for QEC.Coding.BDL26PaidRowsComposition.source_even_paid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:45:37.705079+00:00
-- url     : https://prove2.me/submissions/7d363af4-261b-45c8-8d81-6f41a9aecd9a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_allFiniteSuccess_paid

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
    (h : omega ∈ BDL26CountableEmbeddingExperiment.allFiniteSuccess p) (k : ℕ) :
    streamTotalCost p (2*k) omega < ∞ ∧ PhysicalGeometry (perturbationOddScale p) (2*k)
      (BDL26CountableEmbeddingExperiment.levelMap p omega (2*k)) p.t :=
  ⟨(allFiniteSuccess_paid p h).1 (2*k),(allFiniteSuccess_paid p h).2.2 (2*k)⟩
end QEC.Coding.BDL26PaidRowsComposition
