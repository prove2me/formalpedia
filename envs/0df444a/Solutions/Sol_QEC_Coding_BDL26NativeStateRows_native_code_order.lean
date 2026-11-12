-- Prove2me | solution 1 for QEC.Coding.BDL26NativeStateRows.native_code_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:54:59.832135+00:00
-- url     : https://prove2.me/submissions/db669235-45eb-4862-a22a-f5379c5abc3a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_VariableRelabeling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeStateRows
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_indices_get
import Theorems.Thm_QEC_Coding_BDL26NativeStateRows_initialize_order

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeStateRows
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace QEC.Coding.BDL26NativeStateRows
theorem _root_.solution (S : OddScale) (n : ℕ) (T : Samples (Index S n)) :
    ((initializeQ S n T).value.map Prod.fst).map
        (BDL26NativePresentationGenerator.setupQ S n).1.data.vertices.get=
      (BDL26NativePresentationGenerator.setupQ S n).1.data.vertices := by
  rw [initialize_order]
  exact indices_get _
end QEC.Coding.BDL26NativeStateRows
