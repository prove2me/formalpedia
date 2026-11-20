-- Prove2me | solution 1 for QEC.Coding.BDL26NativeHamiltonianLocality.fixed_parameters_all_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:55:54.281365+00:00
-- url     : https://prove2.me/submissions/84199253-12ed-4669-830d-5bf52796fed8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeHamiltonianLocality
import Theorems.Thm_QEC_Coding_BDL26NativeHamiltonianLocality_finite_history_hamiltonian_ae
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_finiteSuccess_ae
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_finiteSuccess_ae
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_totalCost_finite_on_success
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_totalCost_integrable
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_totalCost_integral_le
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_totalCost_integral_le
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_geometricParameters_nonempty


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
theorem _root_.solution (L : ℝ) :
    ∃ p : GeometricParameters L, ∀ N : ℕ,
      (∫⁻ z, BDL26NativeFiniteComposition.totalCost p N z
        ∂BDL26NativeFiniteComposition.experimentLaw p N) ≤
        (BDL26NativeFiniteComposition.totalCoefficient p*
          (BDL26FiniteEmbeddingExperiment.stageQubits p N+1)^1774 : ℕ) ∧
      Integrable (fun z => (BDL26NativeFiniteComposition.totalCost p N z).toReal)
        (BDL26NativeFiniteComposition.experimentLaw p N) ∧
      ∀ᵐ z ∂BDL26NativeFiniteComposition.experimentLaw p N,
        z ∈ BDL26NativeFiniteComposition.finiteSuccess p N ∧
        BDL26NativeFiniteComposition.totalCost p N z < ∞ ∧
        ∀ i : Fin (N+1), HamiltonianGeometry (perturbationOddScale p) i.val
          (BDL26NativeFiniteComposition.history p N z i) p.t := by
  obtain ⟨p⟩ := geometricParameters_nonempty L
  refine ⟨p, fun N => ⟨BDL26NativeFiniteComposition.totalCost_integral_le p N,
    (BDL26NativeFiniteComposition.totalCost_integrable p N).2, ?_⟩⟩
  filter_upwards [BDL26NativeFiniteComposition.finiteSuccess_ae p N,
    finite_history_hamiltonian_ae p N] with z hz hh
  exact ⟨hz, BDL26NativeFiniteComposition.totalCost_finite_on_success p N z hz, hh⟩
end QEC.Coding.BDL26NativeHamiltonianLocality
