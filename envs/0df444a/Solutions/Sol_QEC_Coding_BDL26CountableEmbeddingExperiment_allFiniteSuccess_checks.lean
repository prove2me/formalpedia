-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.allFiniteSuccess_checks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:19:47.085076+00:00
-- url     : https://prove2.me/submissions/1f70822c-54de-4e0e-aa63-77189472eadb

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_allFiniteSuccess_geometry

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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L)
    {omega : Omega p} (h : omega ∈ allFiniteSuccess p) (n : ℕ)
    (j : Sum (ZLabel (perturbationOddScale p) n) (XLabel (perturbationOddScale p) n)) :
    (∀ r ∈ checkSupport (perturbationOddScale p) n j,
      dist (levelMap p omega n (.q r))
        (checkCenter (perturbationOddScale p) n (levelMap p omega n) j) ≤ 1) ∧
    (∀ r ∈ checkSupport (perturbationOddScale p) n j,
      ∀ s ∈ checkSupport (perturbationOddScale p) n j,
      dist (levelMap p omega n (.q r)) (levelMap p omega n (.q s)) ≤ 2) ∧
    (checkSupport (perturbationOddScale p) n j).card ≤ 7 :=
  (allFiniteSuccess_geometry p h n).2.1 j
end QEC.Coding.BDL26CountableEmbeddingExperiment
