-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.physicalSuccessorOutput_rx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T00:56:54.063814+00:00
-- url     : https://prove2.me/submissions/73598c57-158d-4190-af3a-df349169426c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalSuccessor
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_replacementOutput_rx

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
    (T : Table (X := fun _ : Vertex (state (perturbationOddScale p) n).presentation => Space))
    (h : n % 2 = 0) : physicalSuccessorOutput p n J T = fun v =>
      rxVertexPoint _ (perturbationOddScale p) (perturbationEmbeddingOutput _ J p T)
        (nextRXVertex _ n (state (perturbationOddScale p) n) h v) :=
  replacementOutput_rx _ _ _ _ h
end QEC.Coding.BDL26RandomPerturbation
