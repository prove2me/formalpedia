-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.streamTable_law
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:11:32.042566+00:00
-- url     : https://prove2.me/submissions/b90a62ea-dd01-47d9-ab48-f9c627f3e631

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment_Core
import Mathlib.Probability.Independence.InfinitePi
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurePreserving_streamTable

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal ProbabilityTheory BigOperators
namespace QEC.Coding.BDL26CountableEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (streamLaw p).map (fun omega => omega n) = physicalTableLaw p n :=
  (measurePreserving_streamTable p n).map_eq
end QEC.Coding.BDL26CountableEmbeddingExperiment
