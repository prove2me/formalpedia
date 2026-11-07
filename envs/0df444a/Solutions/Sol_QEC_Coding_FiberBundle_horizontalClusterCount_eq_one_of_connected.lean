-- Prove2me | solution 1 for QEC.Coding.FiberBundle.horizontalClusterCount_eq_one_of_connected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:02:16.476107+00:00
-- url     : https://prove2.me/submissions/8168b9be-66e3-45f1-9881-1e7af67f062d

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives

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
    (root : SupportedHorizontalCell z)
    (hConnected :
      ∀ x : SupportedHorizontalCell z,
        InSameSupportedHorizontalCluster
          baseSample twistSample z root.1 x.1) :
    horizontalClusterCount baseSample twistSample z = 1 := by
  classical
  rw [horizontalClusterCount, Nat.card_eq_one_iff_exists]
  refine ⟨Quotient.mk
    (supportedHorizontalClusterSetoid
      baseSample twistSample z) root, ?_⟩
  intro q
  induction q using Quotient.inductionOn with
  | _ x =>
      apply Quotient.sound
      exact inSameSupportedHorizontalCluster_symmetric
        baseSample twistSample z (hConnected x)
end QEC.Coding.FiberBundle
