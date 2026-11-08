-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsModularForm_raiseLevel_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:01:07.833095+00:00
-- url     : https://prove2.me/submissions/62f96ca6-dd2b-40b5-9276-9af9607a364b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N L : ℕ) (hNL : N ∣ L)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (z : ℍ) :
    lpsModularForm_raiseLevel N L hNL f z=f z := rfl
end QEC.Coding.TannerLiftedProduct
