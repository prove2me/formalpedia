-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.physical_scale_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T00:55:17.532057+00:00
-- url     : https://prove2.me/submissions/d6aa4ca6-8d15-417f-9ede-e4c18dd99185

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalSuccessor

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
theorem _root_.solution (p : GeometricParameters L) :
    replacementScale (6*(p.m : ℝ)) (p.lambda : ℝ) p.rounding = perturbationOddScale p := rfl
end QEC.Coding.BDL26RandomPerturbation
