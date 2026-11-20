-- Prove2me | solution 1 for QEC.Coding.BDL26NativeHamiltonianLocality.finite_history_hamiltonian_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:57:06.507942+00:00
-- url     : https://prove2.me/submissions/d8826ba3-3f4e-4756-99e4-7ced78b6767c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeHamiltonianLocality
import Theorems.Thm_QEC_Coding_BDL26NativeHamiltonianLocality_finiteSuccess_hamiltonian
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_finiteSuccess_ae
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_finiteSuccess_ae


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
    ∀ᵐ z ∂BDL26NativeFiniteComposition.experimentLaw p N, ∀ i : Fin (N+1),
      HamiltonianGeometry (perturbationOddScale p) i.val
        (BDL26NativeFiniteComposition.history p N z i) p.t := by
  filter_upwards [BDL26NativeFiniteComposition.finiteSuccess_ae p N] with z hz
  exact finiteSuccess_hamiltonian p N hz
end QEC.Coding.BDL26NativeHamiltonianLocality
