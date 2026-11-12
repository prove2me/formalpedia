-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.allFiniteSuccess_frequency_physical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:20:01.914382+00:00
-- url     : https://prove2.me/submissions/3cbf625d-a244-4f32-b129-2918af18d0e2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_allFiniteSuccess_localMap
import Theorems.Thm_QEC_Coding_BDL26RandomPhysicalLocality_frequency_physical
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric


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
    (q : Physical (perturbationOddScale p) n) (a : CSSDaviesLocality.Axis) (w : ℝ) :
    (BDL26CSSDaviesLocality.subsystem (perturbationOddScale p) n q).OperatorSupportedOnRegister
      (actualFrequency (hamiltonian (perturbationOddScale p) n)
        (BDL26CSSDaviesLocality.hamiltonian_symmetric (perturbationOddScale p) n)
        (BDL26CSSDaviesLocality.coupling (perturbationOddScale p) n q a) w) ∧
    (∀ r ∈ region (perturbationOddScale p) n q,
      dist (levelMap p omega n (.q r)) (levelMap p omega n (.q q)) ≤ 2) ∧
    (∀ r ∈ region (perturbationOddScale p) n q,
      ∀ s ∈ region (perturbationOddScale p) n q,
      dist (levelMap p omega n (.q r)) (levelMap p omega n (.q s)) ≤ 4) ∧
    (BDL26CSSDaviesLocality.subsystem (perturbationOddScale p) n q).selected.card ≤ 50 :=
  frequency_physical _ _ _ (allFiniteSuccess_localMap p h n) q a w
end QEC.Coding.BDL26CountableEmbeddingExperiment
