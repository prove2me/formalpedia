-- Prove2me | solution 1 for QEC.Coding.BDL26NativeHamiltonianLocality.finiteHamiltonianSuccess_measure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:03:41.079187+00:00
-- url     : https://prove2.me/submissions/46c42d1a-12e7-46c1-a919-54206d9f4b6e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeHamiltonianLocality
import Theorems.Thm_QEC_Coding_BDL26NativeHamiltonianLocality_finiteHamiltonianSuccess_eq
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_finiteSuccess_measure
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_finiteSuccess_measure


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    BDL26NativeFiniteComposition.experimentLaw p N (finiteHamiltonianSuccess p N) = 1 := by
  rw [finiteHamiltonianSuccess_eq]
  exact BDL26NativeFiniteComposition.finiteSuccess_measure p N
end QEC.Coding.BDL26NativeHamiltonianLocality
