-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.truncate_prefix_proof_irrel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:10:46.586244+00:00
-- url     : https://prove2.me/submissions/ba52d740-0144-4ddf-afc2-611853ac81a8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment_Core

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
namespace QEC.Coding.BDL26CountableEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h h' : m ≤ n) (omega : Omega p) :
    experimentPrefix p m n h (truncate p n omega) =
      experimentPrefix p m n h' (truncate p n omega) := rfl
end QEC.Coding.BDL26CountableEmbeddingExperiment
