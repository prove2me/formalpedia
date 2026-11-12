-- Prove2me | solution 1 for QEC.Coding.BDL26NativeHamiltonianLocality.finiteSuccess_hamiltonian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:03:55.66001+00:00
-- url     : https://prove2.me/submissions/b729a25f-8122-4f21-bcd1-e0555a0fa6a8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeHamiltonianLocality
import Theorems.Thm_QEC_Coding_BDL26NativeHamiltonianLocality_hamiltonianGeometry_of_physical
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_finiteSuccess_geometry
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_finiteSuccess_geometry


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    {z : BDL26NativeFiniteComposition.Experiment p N}
    (hz : z ∈ BDL26NativeFiniteComposition.finiteSuccess p N) :
    ∀ i : Fin (N+1),
      HamiltonianGeometry (perturbationOddScale p) i.val
        (BDL26NativeFiniteComposition.history p N z i) p.t := by
  intro i
  exact hamiltonianGeometry_of_physical _ _ _
    (BDL26NativeFiniteComposition.finiteSuccess_geometry p N hz i)
end QEC.Coding.BDL26NativeHamiltonianLocality
