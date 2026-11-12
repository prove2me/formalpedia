-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.VariableRelabeling.original_prefixCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:49:15.737199+00:00
-- url     : https://prove2.me/submissions/73bbd6db-d8ab-4c12-928c-738dc53dd4c1

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_VariableRelabeling
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_prefixCount_conjugacy


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
    (r lambda : ℝ) (K : ℕ) (u : A ≃ Vertex P) (T : HTable (Vertex P) Space)
    (m : ℕ) (e : Event P J r) :
    prefixCount (pulledSupport P J r u) (pulledBad P J r lambda K u) (encodeTable u T) m e=
      prefixCount (eventSupport P J r) (eventBad P J r lambda K) T m e :=
  prefixCount_conjugacy u _ _ T m e
end QEC.Coding.BDL26RandomPerturbation.VariableRelabeling
