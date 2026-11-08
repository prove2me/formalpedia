-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChi4E2ThetaBasis_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:02:06.506137+00:00
-- url     : https://prove2.me/submissions/8cd0b8c9-ec10-4369-9a49-3311ff8d6686

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (b : Fin 3) (z : ℍ) :
    lpsChi4E2ThetaBasis q b z=lpsChi4E2Dilate (q^b.val) (pow_pos (Fact.out : q.Prime).pos _) z := rfl
end QEC.Coding.TannerLiftedProduct
