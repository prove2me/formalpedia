-- Prove2me | solution 1 for QEC.Coding.FiberBundle.connected_of_horizontalClusterCount_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:54:56.01896+00:00
-- url     : https://prove2.me/submissions/958c3097-9a42-449e-b1b1-39ec673101dc

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
    (hCount :
      horizontalClusterCount baseSample twistSample z = 1) :
    ∀ x : SupportedHorizontalCell z,
      InSameSupportedHorizontalCluster
        baseSample twistSample z root.1 x.1 := by
  classical
  rw [horizontalClusterCount, Nat.card_eq_one_iff_exists] at hCount
  rcases hCount with ⟨q, hq⟩
  intro x
  apply @Quotient.exact _
    (supportedHorizontalClusterSetoid
      baseSample twistSample z) root x
  calc
    Quotient.mk
        (supportedHorizontalClusterSetoid
          baseSample twistSample z) root = q := hq _
    _ = Quotient.mk
        (supportedHorizontalClusterSetoid
          baseSample twistSample z) x := (hq _).symm
end QEC.Coding.FiberBundle
