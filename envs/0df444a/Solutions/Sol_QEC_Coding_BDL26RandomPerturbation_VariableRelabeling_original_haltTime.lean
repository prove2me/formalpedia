-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.VariableRelabeling.original_haltTime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:49:12.401379+00:00
-- url     : https://prove2.me/submissions/c416e830-541f-477e-a32e-498309fb0d86

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_VariableRelabeling
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_haltTime_conjugacy


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
    haltTime (pulledSupport P J r u) (pulledBad P J r lambda K u) (encodeTable u T)=
      haltTime (eventSupport P J r) (eventBad P J r lambda K) T := haltTime_conjugacy u _ _ T
end QEC.Coding.BDL26RandomPerturbation.VariableRelabeling
