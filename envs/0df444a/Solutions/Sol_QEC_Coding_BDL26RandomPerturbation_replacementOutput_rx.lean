-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.replacementOutput_rx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T23:21:00.718146+00:00
-- url     : https://prove2.me/submissions/716f9093-6e99-42e9-8d3c-4d48274737d4

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
theorem _root_.solution (S : OddScale) (n : Nat) (C : ConstructionState)
    (J : Vertex C.presentation → Space) (h : n % 2 = 0) :
    replacementOutput S n C J =
      fun v => rxVertexPoint C.presentation S J (nextRXVertex S n C h v) := by
  exact @_root_.dif_pos (n % 2 = 0) (Nat.decEq (n % 2) 0) h
    (Vertex (nextState S n C).presentation → Space) _ _
end QEC.Coding.BDL26RandomPerturbation
