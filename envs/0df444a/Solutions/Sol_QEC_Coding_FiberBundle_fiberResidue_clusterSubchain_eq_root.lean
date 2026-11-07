-- Prove2me | solution 1 for QEC.Coding.FiberBundle.fiberResidue_clusterSubchain_eq_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:15:11.390494+00:00
-- url     : https://prove2.me/submissions/2b9db88f-854e-4f6b-bd2e-8c652c540bac

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_fiberResidue_eq_of_inSameSupportedHorizontalCluster
import Theorems.Thm_QEC_Coding_FiberBundle_inSameSupportedHorizontalCluster_of_clusterSubchain_ne_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (root x : Fin (4 * r) × ZMod (ell * ell))
    (hx : horizontalClusterSubchain
      baseSample twistSample z root x ≠ 0) :
    fiberResidue ell x.2 = fiberResidue ell root.2 := by
  exact (fiberResidue_eq_of_inSameSupportedHorizontalCluster
    baseSample twistSample z
    (inSameSupportedHorizontalCluster_of_clusterSubchain_ne_zero
      baseSample twistSample z root x hx)).symm
end QEC.Coding.FiberBundle
