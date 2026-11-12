-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.VariableRelabeling.pulled_table_law
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:51:00.798773+00:00
-- url     : https://prove2.me/submissions/0ce732c0-9519-4bf3-b359-fa296172a003

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_VariableRelabeling
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_table_law


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
theorem _root_.solution (P : TannerSquarePresentation) (R c : ℝ) (hc : c<1)
    (u : A ≃ Vertex P) :
    letI (v : Vertex P) := vertexLaw_probability P R hc v
    letI (a : A) := pulledVertexLaw_probability P R c hc u a
    (tableLaw (vertexLaw P R c)).map (encodeTable u)=tableLaw (pulledVertexLaw P R c u) := by
  letI (v : Vertex P) := vertexLaw_probability P R hc v
  letI (a : A) := pulledVertexLaw_probability P R c hc u a
  exact table_law u (vertexLaw P R c)
end QEC.Coding.BDL26RandomPerturbation.VariableRelabeling
