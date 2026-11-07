-- Prove2me | solution 1 for QEC.Coding.f256SelectorFunctional_eq_coefficient_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:49:31.259458+00:00
-- url     : https://prove2.me/submissions/42bb21e8-c082-43a0-b185-1b07bd446e4a

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_BinaryConversion

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators
namespace QEC.Coding
theorem _root_.solution (v : Fin 512 → ZMod 2) :
    f256SelectorFunctional v = ∑ q, v q * f256SelectorCoefficient q := by
  have hv : v = ∑ q, v q • Pi.single q 1 := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply, Pi.smul_apply]
  calc
    f256SelectorFunctional v = f256SelectorFunctional (∑ q, v q • Pi.single q 1) := congrArg _ hv
    _ = ∑ q, v q * f256SelectorCoefficient q := by
      simp only [map_sum, map_smul, f256SelectorCoefficient, smul_eq_mul]
end QEC.Coding
