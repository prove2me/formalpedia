-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.finiteSuccess_weightedJump_physical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:10:06.352068+00:00
-- url     : https://prove2.me/submissions/208e5ab6-ae64-4768-823c-c4b042fe4b70

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
import Theorems.Thm_QEC_Coding_BDL26RandomPhysicalLocality_weightedJump_physical
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    {z : Experiment p n} (hz : z ∈ finiteSuccess p n) (i : Fin (n+1))
    (rate : BDL26CSSDaviesLocality.CouplingIndex (perturbationOddScale p) i.val →
      BDL26CSSDaviesLocality.Frequency (perturbationOddScale p) i.val → ℝ)
    (q : Physical (perturbationOddScale p) i.val) (a : CSSDaviesLocality.Axis)
    (ω : BDL26CSSDaviesLocality.Frequency (perturbationOddScale p) i.val) :
    (BDL26CSSDaviesLocality.subsystem (perturbationOddScale p) i.val q).OperatorSupportedOnRegister
      (hamiltonianJump (hamiltonian (perturbationOddScale p) i.val)
        (BDL26CSSDaviesLocality.hamiltonian_symmetric (perturbationOddScale p) i.val)
        (fun qa : BDL26CSSDaviesLocality.CouplingIndex (perturbationOddScale p) i.val =>
          BDL26CSSDaviesLocality.coupling (perturbationOddScale p) i.val qa.1 qa.2)
        rate ((q,a),ω)) ∧
    (∀ r ∈ region (perturbationOddScale p) i.val q,
      dist (history p n z i (.q r)) (history p n z i (.q q)) ≤ 2) ∧
    (∀ r ∈ region (perturbationOddScale p) i.val q,
      ∀ s ∈ region (perturbationOddScale p) i.val q,
      dist (history p n z i (.q r)) (history p n z i (.q s)) ≤ 4) ∧
    (BDL26CSSDaviesLocality.subsystem (perturbationOddScale p) i.val q).selected.card ≤ 50 :=
  weightedJump_physical _ _ _ (hz.2.2 i) rate q a ω
end QEC.Coding.BDL26FiniteEmbeddingExperiment
