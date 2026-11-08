-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsE2DifferenceThetaBasis_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:02:04.781195+00:00
-- url     : https://prove2.me/submissions/affd7c66-a5d1-4bcb-b5dd-727db572c7fa

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (a : Fin 5) (b : Fin 3) (z : ℍ) :
    lpsE2DifferenceThetaBasis q a b z=lpsE2Difference (2^a.val*q^b.val)
      (mul_pos (pow_pos (by decide) _) (pow_pos (Fact.out : q.Prime).pos _)) z := rfl
end QEC.Coding.TannerLiftedProduct
