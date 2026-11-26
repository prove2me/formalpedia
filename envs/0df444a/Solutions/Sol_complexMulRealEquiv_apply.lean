-- Prove2me | solution 1 for complexMulRealEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:57:09.697931+00:00
-- url     : https://prove2.me/submissions/4f0a44ac-d788-45f9-8d11-9e438ef0c6fb

import Definitions.Def_Operator_Crouzeix_SmoothJordanAffine
import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
import Definitions.Def_Operator_Crouzeix_SmoothJordanSimilarity

set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace
theorem _root_.solution (a : ℂ) (ha : a ≠ 0)
    (z : ℂ) :
    complexMulRealEquiv a ha z = a * z := rfl
