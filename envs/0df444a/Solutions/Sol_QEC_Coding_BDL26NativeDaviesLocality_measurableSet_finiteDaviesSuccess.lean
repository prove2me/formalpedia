-- Prove2me | solution 1 for QEC.Coding.BDL26NativeDaviesLocality.measurableSet_finiteDaviesSuccess
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:52:16.348044+00:00
-- url     : https://prove2.me/submissions/a452ada1-1591-4f99-aab2-2ced1cc1b784

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeHamiltonianLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeDaviesLocality
import Theorems.Thm_QEC_Coding_BDL26NativeDaviesLocality_finiteDaviesSuccess_eq
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurableSet_finiteSuccess
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_measurableSet_finiteSuccess


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
    MeasurableSet (finiteDaviesSuccess p N) := by
  rw [finiteDaviesSuccess_eq]
  exact BDL26NativeFiniteComposition.measurableSet_finiteSuccess p N
end QEC.Coding.BDL26NativeDaviesLocality
