-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.allFiniteSuccess_weightedJump_physical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:20:38.365864+00:00
-- url     : https://prove2.me/submissions/eee127db-c6ec-40dd-8e88-e440a9e1c4a5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_allFiniteSuccess_localMap
import Theorems.Thm_QEC_Coding_BDL26RandomPhysicalLocality_weightedJump_physical
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
    (rate : BDL26CSSDaviesLocality.CouplingIndex (perturbationOddScale p) n →
      BDL26CSSDaviesLocality.Frequency (perturbationOddScale p) n → ℝ)
    (q : Physical (perturbationOddScale p) n) (a : CSSDaviesLocality.Axis)
    (w : BDL26CSSDaviesLocality.Frequency (perturbationOddScale p) n) :
    (BDL26CSSDaviesLocality.subsystem (perturbationOddScale p) n q).OperatorSupportedOnRegister
      (hamiltonianJump (hamiltonian (perturbationOddScale p) n)
        (BDL26CSSDaviesLocality.hamiltonian_symmetric (perturbationOddScale p) n)
        (fun qa : BDL26CSSDaviesLocality.CouplingIndex (perturbationOddScale p) n =>
          BDL26CSSDaviesLocality.coupling (perturbationOddScale p) n qa.1 qa.2)
        rate ((q,a),w)) ∧
    (∀ r ∈ region (perturbationOddScale p) n q,
      dist (levelMap p omega n (.q r)) (levelMap p omega n (.q q)) ≤ 2) ∧
    (∀ r ∈ region (perturbationOddScale p) n q,
      ∀ s ∈ region (perturbationOddScale p) n q,
      dist (levelMap p omega n (.q r)) (levelMap p omega n (.q s)) ≤ 4) ∧
    (BDL26CSSDaviesLocality.subsystem (perturbationOddScale p) n q).selected.card ≤ 50 :=
  weightedJump_physical _ _ _ (allFiniteSuccess_localMap p h n) rate q a w
end QEC.Coding.BDL26CountableEmbeddingExperiment
