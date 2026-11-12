-- Prove2me | solution 1 for QEC.Coding.BDL26NativeDaviesLocality.zero_seed_davies
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:52:46.7002+00:00
-- url     : https://prove2.me/submissions/36e5bebe-0195-442d-af31-f776fb987b25

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeHamiltonianLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeDaviesLocality
import Theorems.Thm_QEC_Coding_BDL26NativeDaviesLocality_daviesGeometry_of_physical
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_zero_experiment_seed
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_zero_experiment_seed


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L)
    (z : BDL26NativeFiniteComposition.Experiment p 0) :
    BDL26NativeFiniteComposition.evaluate p 0 z =
      BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p) ∧
    BDL26NativeFiniteComposition.totalCost p 0 z = 0 ∧
    DaviesGeometry (perturbationOddScale p) 0
      (BDL26NativeFiniteComposition.evaluate p 0 z) p.t := by
  obtain ⟨hs,hc,hg⟩ := BDL26NativeFiniteComposition.zero_experiment_seed p z
  exact ⟨hs,hc,daviesGeometry_of_physical _ _ _ hg⟩
end QEC.Coding.BDL26NativeDaviesLocality
