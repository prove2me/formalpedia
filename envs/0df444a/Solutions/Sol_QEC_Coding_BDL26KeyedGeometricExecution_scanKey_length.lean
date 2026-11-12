-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometricExecution.scanKey_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:17:55.859024+00:00
-- url     : https://prove2.me/submissions/436bbb08-28a6-4619-8523-4fbdbe37ac7c

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
    (e : KeyEvent P k hk J r) : (scanKey P k hk J r e).length = 4 := by
  rw [scanKey, Finset.length_sort, Finset.card_image_of_injective _ hk]
  exact e.property.1
end QEC.Coding.BDL26KeyedGeometricExecution
