-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.VariableRelabeling.original_totalSteps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:50:33.956937+00:00
-- url     : https://prove2.me/submissions/b5269cca-5505-4704-8181-238807f7ad7e

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_VariableRelabeling
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_totalSteps_conjugacy


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
    (r lambda : ℝ) (K : ℕ) (u : A ≃ Vertex P) (T : HTable (Vertex P) Space) :
    totalSteps (pulledSupport P J r u) (pulledBad P J r lambda K u) (encodeTable u T)=
      totalSteps (eventSupport P J r) (eventBad P J r lambda K) T :=
  totalSteps_conjugacy u _ _ T
end QEC.Coding.BDL26RandomPerturbation.VariableRelabeling
