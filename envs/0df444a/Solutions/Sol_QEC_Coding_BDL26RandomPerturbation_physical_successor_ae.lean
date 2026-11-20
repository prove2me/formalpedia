-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.physical_successor_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:14:18.508176+00:00
-- url     : https://prove2.me/submissions/380bf7b1-60d8-41a4-a9e7-10637477b0a1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalSuccessor
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_replacementOutput_localMap
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_state_boundedValence
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_frequency_supported
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_weightedJump_supported
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_capCutoff_bounds
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_geometric_output_geometry_density_ae
import Theorems.Thm_QEC_Coding_BDL26RandomPhysicalLocality_physicalGeometry_of_localMap
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_frequency_supported
import Theorems.Thm_QEC_Coding_CSSDaviesLocality_weightedJump_supported


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RXLocalReplacement
open BDL26RandomPhysicalLocality BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26CSSHamiltonian Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling MeasureTheory
variable {L : ℝ}
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (p : GeometricParameters L) (n : Nat)
    (J : Vertex (state (perturbationOddScale p) n).presentation → Space)
    (hJ : IsBoundedDensityLocalMap (state (perturbationOddScale p) n).presentation J p.t) :
    ∀ᵐ T ∂physicalTableLaw p n, PhysicalSuccessorFacts p n J T := by
  let P := (state (perturbationOddScale p) n).presentation
  letI (v : Vertex P) := vertexLaw_probability P
    ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
  filter_upwards [geometric_output_geometry_density_ae P J p hJ
    (state_boundedValence (perturbationOddScale p) n)] with T hT
  have hout := replacementOutput_localMap p n (state (perturbationOddScale p) n)
    (perturbationEmbeddingOutput P J p T) (state_boundedValence (perturbationOddScale p) n)
    hT.2.1 hT.2.2
  exact ⟨hT.1, hout, physicalGeometry_of_localMap _ _ _ hout,
    BDL26CSSDaviesLocality.frequency_supported _ _,
    BDL26CSSDaviesLocality.weightedJump_supported _ _⟩
end QEC.Coding.BDL26RandomPerturbation
