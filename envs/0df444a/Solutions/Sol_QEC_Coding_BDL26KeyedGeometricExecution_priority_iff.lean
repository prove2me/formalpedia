-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometricExecution.priority_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:56:34.39553+00:00
-- url     : https://prove2.me/submissions/2378d01f-e8d7-4588-ae3e-acade93de3af

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricAvoidance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricExecution

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26KeyedGeometricExecution
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26KeyedGeometric
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal
namespace QEC.Coding.BDL26KeyedGeometricExecution
theorem _root_.solution (P : TannerSquarePresentation) (k : Triangle P → ℕ)
    (hk : Function.Injective k) (J : Vertex P → Space) (r : ℝ)
    (e f : KeyEvent P k hk J r) :
    (keyExecutionOrder P k hk J r).toLE.le e f ↔
      scanKey P k hk J r e ≤ scanKey P k hk J r f := Iff.rfl
end QEC.Coding.BDL26KeyedGeometricExecution
