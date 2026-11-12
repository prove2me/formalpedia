-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.streamTables_iIndepFun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:12:10.834103+00:00
-- url     : https://prove2.me/submissions/e88ab503-69b5-4535-b02c-9570cd2e0efa

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment_Core
import Mathlib.Probability.Independence.InfinitePi
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal ProbabilityTheory BigOperators
namespace QEC.Coding.BDL26CountableEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) :
    iIndepFun (fun n (omega : Omega p) => omega n) (streamLaw p) :=
  iIndepFun_infinitePi (P := physicalTableLaw p)
    (X := fun n (t : StageTables p n) => t) (fun _ => measurable_id)
end QEC.Coding.BDL26CountableEmbeddingExperiment
