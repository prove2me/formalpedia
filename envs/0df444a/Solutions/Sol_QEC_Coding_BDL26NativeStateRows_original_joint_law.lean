-- Prove2me | solution 1 for QEC.Coding.BDL26NativeStateRows.original_joint_law
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:56:30.264482+00:00
-- url     : https://prove2.me/submissions/f5f2775c-3873-48ca-bb9e-94ca81fe96fd

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_VariableRelabeling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeStateRows
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_VariableRelabeling_original_joint_law


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeStateRows
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
open scoped Classical
open QEC.Coding.ProbabilisticConstruction
namespace QEC.Coding.BDL26NativeStateRows
theorem _root_.solution (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r lambda : ℝ) (K : ℕ) (radius cutoff : ℝ) (hc : cutoff<1) :
    letI (v : Vertex (P S n)) := vertexLaw_probability (P S n) radius hc v
    letI (a : Index S n) := BDL26RandomPerturbation.VariableRelabeling.pulledVertexLaw_probability
      (P S n) radius cutoff hc (decode S n) a
    (tableLaw (BDL26RandomPerturbation.VariableRelabeling.pulledVertexLaw
      (P S n) radius cutoff (decode S n))).map
      (QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.decodedObservation
        (decode S n) (eventSupport (P S n) J r) (eventBad (P S n) J r lambda K))=
      (tableLaw (vertexLaw (P S n) radius cutoff)).map
        (QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.jointObservation
          (eventSupport (P S n) J r) (eventBad (P S n) J r lambda K)) := by
  exact BDL26RandomPerturbation.VariableRelabeling.original_joint_law
    (P S n) J r lambda K radius cutoff hc (decode S n)
end QEC.Coding.BDL26NativeStateRows
