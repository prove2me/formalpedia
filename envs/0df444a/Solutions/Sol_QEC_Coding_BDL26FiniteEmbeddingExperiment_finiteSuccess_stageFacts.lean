-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.finiteSuccess_stageFacts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:36:15.281741+00:00
-- url     : https://prove2.me/submissions/1294b149-2c94-421f-91c1-697b792a917b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_history_stage
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_physicalSuccessorFacts_of_halts_localMap


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
namespace QEC.Coding.BDL26FiniteEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    {z : Experiment p n} (hz : z ∈ finiteSuccess p n) (i : Fin n) :
    PhysicalSuccessorFacts p i.val (stageInput p n i z) (tableAt p n i z) := by
  apply physicalSuccessorFacts_of_halts_localMap p i.val
  · exact hz.2.1 i
  · have hg := hz.2.2 ⟨i.val+1, by omega⟩
    rw [history_stage] at hg
    exact hg
end QEC.Coding.BDL26FiniteEmbeddingExperiment
