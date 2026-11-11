-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleKeys.keyOfCode_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:30:41.282373+00:00
-- url     : https://prove2.me/submissions/e17c2cc9-4f09-4c63-9ea8-7169d7193207

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_lookup_rows_value

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
noncomputable section
open scoped Classical
namespace QEC.Coding.BDL26NativeTriangleKeys
theorem _root_.solution (S : OddScale) (n : ℕ) (c : Code) :
    (keyOfCodeQ S n c).1=
      if c∈(BDL26NativePresentationGenerator.setupQ S n).1.triangles then some (2*c.owner+c.copy) else none := by
  exact lookup_rows_value c _
end QEC.Coding.BDL26NativeTriangleKeys
