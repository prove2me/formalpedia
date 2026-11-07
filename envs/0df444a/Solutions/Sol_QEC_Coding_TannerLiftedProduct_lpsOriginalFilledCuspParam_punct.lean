-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspParam_punct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:40:25.785493+00:00
-- url     : https://prove2.me/submissions/4e0d73f5-fb61-46a8-af1d-95644302ebff

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (q : lpsOriginalCuspDisk N (lpsOriginalCuspRepresentative N c)) :
    lpsOriginalFilledCuspParam N c
      (lpsOriginalCuspPunctToFull N (lpsOriginalCuspRepresentative N c) q)=
        Sum.inl (lpsOriginalCuspPunctInverse N (lpsOriginalCuspRepresentative N c) q) := by
  change lpsOriginalFilledCuspInvFun N (lpsOriginalCuspRepresentative N c) q.val=_
  rw [lpsOriginalFilledCuspInvFun,dif_neg q.property.1,dif_pos q.property.2]
  rfl
end QEC.Coding.TannerLiftedProduct
