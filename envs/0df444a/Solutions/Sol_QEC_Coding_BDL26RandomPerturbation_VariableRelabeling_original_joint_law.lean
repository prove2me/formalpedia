-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.VariableRelabeling.original_joint_law
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T23:04:29.389533+00:00
-- url     : https://prove2.me/submissions/d1dd3560-365c-4d7a-9242-ae9dd8159a5e

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_VariableRelabeling
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurableSet_eventBad
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_jointObservation_law


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation QEC.Coding.BDL26RandomPerturbation.VariableRelabeling
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding BDL26DecodingGraph
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
open QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling
variable {A : Type*} [Fintype A] [DecidableEq A]
namespace QEC.Coding.BDL26RandomPerturbation.VariableRelabeling
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (R c : ℝ) (hc : c<1) (u : A ≃ Vertex P) :
    letI (v : Vertex P) := vertexLaw_probability P R hc v
    letI (a : A) := pulledVertexLaw_probability P R c hc u a
    (tableLaw (pulledVertexLaw P R c u)).map
      (decodedObservation u (eventSupport P J r) (eventBad P J r lambda K))=
      (tableLaw (vertexLaw P R c)).map
        (jointObservation (eventSupport P J r) (eventBad P J r lambda K)) := by
  letI (v : Vertex P) := vertexLaw_probability P R hc v
  letI (a : A) := pulledVertexLaw_probability P R c hc u a
  exact jointObservation_law u _ _ (measurableSet_eventBad P J r lambda K) (vertexLaw P R c)
end QEC.Coding.BDL26RandomPerturbation.VariableRelabeling
