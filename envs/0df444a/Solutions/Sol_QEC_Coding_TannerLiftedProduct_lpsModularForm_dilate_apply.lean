-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsModularForm_dilate_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:01:25.796285+00:00
-- url     : https://prove2.me/submissions/40713c05-faf7-43ff-8ec4-44413cc9b816

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N m : ℕ) [NeZero N] (hm : 0 < m)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (z : ℍ) :
    lpsModularForm_dilate N m hm f z=f (lpsE2AffineMatrix m hm 0 • z) := rfl
end QEC.Coding.TannerLiftedProduct
