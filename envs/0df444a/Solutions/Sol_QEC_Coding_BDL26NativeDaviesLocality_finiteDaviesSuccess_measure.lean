-- Prove2me | solution 1 for QEC.Coding.BDL26NativeDaviesLocality.finiteDaviesSuccess_measure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:03:37.864956+00:00
-- url     : https://prove2.me/submissions/a4c83014-7d64-4002-93a8-ff09459c84b1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeHamiltonianLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeDaviesLocality
import Theorems.Thm_QEC_Coding_BDL26NativeDaviesLocality_finiteDaviesSuccess_eq
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_finiteSuccess_measure
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_finiteSuccess_measure


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeDaviesLocality
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open BDL26CSSDaviesLocality
open PauliSymplectic Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped ENNReal BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26NativeDaviesLocality
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    BDL26NativeFiniteComposition.experimentLaw p N (finiteDaviesSuccess p N) = 1 := by
  rw [finiteDaviesSuccess_eq]
  exact BDL26NativeFiniteComposition.finiteSuccess_measure p N
end QEC.Coding.BDL26NativeDaviesLocality
