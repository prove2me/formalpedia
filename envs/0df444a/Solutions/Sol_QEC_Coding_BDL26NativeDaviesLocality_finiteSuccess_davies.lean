-- Prove2me | solution 1 for QEC.Coding.BDL26NativeDaviesLocality.finiteSuccess_davies
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:11:38.429511+00:00
-- url     : https://prove2.me/submissions/a67a79f7-3379-4621-bc27-12fefd9b04e6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeHamiltonianLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeDaviesLocality
import Theorems.Thm_QEC_Coding_BDL26NativeDaviesLocality_daviesGeometry_of_physical
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_finiteSuccess_geometry
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_finiteSuccess_geometry


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    {z : BDL26NativeFiniteComposition.Experiment p N}
    (hz : z ∈ BDL26NativeFiniteComposition.finiteSuccess p N) :
    ∀ i : Fin (N+1), DaviesGeometry (perturbationOddScale p) i.val
      (BDL26NativeFiniteComposition.history p N z i) p.t := by
  intro i
  exact daviesGeometry_of_physical _ _ _
    (BDL26NativeFiniteComposition.finiteSuccess_geometry p N hz i)
end QEC.Coding.BDL26NativeDaviesLocality
