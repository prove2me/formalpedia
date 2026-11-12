-- Prove2me | solution 1 for QEC.Coding.BDL26NativeHamiltonianLocality.zero_seed_hamiltonian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:51:49.047041+00:00
-- url     : https://prove2.me/submissions/0c792d35-fc2c-4eff-a69b-8fe54c3e176e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeHamiltonianLocality
import Theorems.Thm_QEC_Coding_BDL26NativeHamiltonianLocality_hamiltonianGeometry_of_physical
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_zero_experiment_seed
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_zero_experiment_seed


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeHamiltonianLocality
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open PauliSymplectic Semantics
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped ENNReal BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26NativeHamiltonianLocality
theorem _root_.solution {L : ℝ} (p : GeometricParameters L)
    (z : BDL26NativeFiniteComposition.Experiment p 0) :
    HamiltonianGeometry (perturbationOddScale p) 0
      (BDL26NativeFiniteComposition.evaluate p 0 z) p.t :=
  hamiltonianGeometry_of_physical _ _ _
    (BDL26NativeFiniteComposition.zero_experiment_seed p z).2.2
end QEC.Coding.BDL26NativeHamiltonianLocality
