-- Prove2me | solution 1 for QEC.Coding.BDL26NativeHamiltonianLocality.measurableSet_finiteHamiltonianSuccess
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:49:54.838025+00:00
-- url     : https://prove2.me/submissions/6fe55e30-76fd-4521-9ee3-3dfbafab0fa2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeHamiltonianLocality
import Theorems.Thm_QEC_Coding_BDL26NativeHamiltonianLocality_finiteHamiltonianSuccess_eq
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurableSet_finiteSuccess
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_measurableSet_finiteSuccess


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
    MeasurableSet (finiteHamiltonianSuccess p N) := by
  rw [finiteHamiltonianSuccess_eq]
  exact BDL26NativeFiniteComposition.measurableSet_finiteSuccess p N
end QEC.Coding.BDL26NativeHamiltonianLocality
