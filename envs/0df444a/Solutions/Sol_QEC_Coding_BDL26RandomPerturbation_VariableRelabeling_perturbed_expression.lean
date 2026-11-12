-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.VariableRelabeling.perturbed_expression
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:50:57.630466+00:00
-- url     : https://prove2.me/submissions/a4585cbb-0125-42de-aaba-e266cf0d634b

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_VariableRelabeling
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_VariableRelabeling_geometric_output

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
    {L : ℝ} (p : GeometricParameters L) (u : A ≃ Vertex P)
    (T : HTable (Vertex P) Space) (a : A) :
    p.lambda • ((1/2 : ℝ) • (J ∘ u) a)+
      pulledOutput P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda) u (encodeTable u T) a=
      perturbedMap P J p.lambda (geometricOutput P J p T) (u a) := by
  rw [geometric_output]
  change p.lambda • ((1/2 : ℝ) • J (u a))+geometricOutput P J p T (u a)=
    (p.lambda : ℝ) • ((1/2 : ℝ) • J (u a))+geometricOutput P J p T (u a)
  rw [Nat.cast_smul_eq_nsmul]
end QEC.Coding.BDL26RandomPerturbation.VariableRelabeling
