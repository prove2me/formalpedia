-- Prove2me | solution 1 for QEC.Coding.BDL26NativeDaviesLocality.fixed_parameters_all_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:08:48.513857+00:00
-- url     : https://prove2.me/submissions/f2210f63-da97-430f-92dd-db347b8ffad4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeHamiltonianLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeDaviesLocality
import Theorems.Thm_QEC_Coding_BDL26NativeDaviesLocality_finiteSuccess_davies
import Theorems.Thm_QEC_Coding_BDL26NativeDaviesLocality_finiteDaviesSuccess_measure
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_finiteSuccess_ae
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_finiteSuccess_ae
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_totalCost_finite_on_success
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_totalCost_integrable
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_totalCost_integral_le
import Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_totalCost_integral_le
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_geometricParameters_nonempty


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
theorem _root_.solution (L : ℝ) :
    ∃ p : GeometricParameters L, ∀ N : ℕ,
      (∫⁻ z, BDL26NativeFiniteComposition.totalCost p N z
        ∂BDL26NativeFiniteComposition.experimentLaw p N) ≤
        (BDL26NativeFiniteComposition.totalCoefficient p*
          (BDL26FiniteEmbeddingExperiment.stageQubits p N+1)^1774 : ℕ) ∧
      (∫⁻ z, BDL26NativeFiniteComposition.totalCost p N z
        ∂BDL26NativeFiniteComposition.experimentLaw p N) < ∞ ∧
      Integrable (fun z => (BDL26NativeFiniteComposition.totalCost p N z).toReal)
        (BDL26NativeFiniteComposition.experimentLaw p N) ∧
      BDL26NativeFiniteComposition.experimentLaw p N (finiteDaviesSuccess p N) = 1 ∧
      ∀ᵐ z ∂BDL26NativeFiniteComposition.experimentLaw p N,
        z ∈ finiteDaviesSuccess p N ∧
        BDL26NativeFiniteComposition.totalCost p N z < ∞ ∧
        ∀ i : Fin (N+1), DaviesGeometry (perturbationOddScale p) i.val
          (BDL26NativeFiniteComposition.history p N z i) p.t := by
  obtain ⟨p⟩ := geometricParameters_nonempty L
  refine ⟨p, fun N => ⟨BDL26NativeFiniteComposition.totalCost_integral_le p N,
    (BDL26NativeFiniteComposition.totalCost_integrable p N).1,
    (BDL26NativeFiniteComposition.totalCost_integrable p N).2,
    finiteDaviesSuccess_measure p N, ?_⟩⟩
  filter_upwards [BDL26NativeFiniteComposition.finiteSuccess_ae p N] with z hz
  have hd := finiteSuccess_davies p N hz
  exact ⟨⟨hz,hd⟩, BDL26NativeFiniteComposition.totalCost_finite_on_success p N z hz, hd⟩
end QEC.Coding.BDL26NativeDaviesLocality
