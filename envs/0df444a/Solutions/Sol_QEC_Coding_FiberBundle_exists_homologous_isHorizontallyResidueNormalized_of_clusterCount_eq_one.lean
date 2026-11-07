-- Prove2me | solution 1 for QEC.Coding.FiberBundle.exists_homologous_isHorizontallyResidueNormalized_of_clusterCount_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:48:10.473425+00:00
-- url     : https://prove2.me/submissions/89059637-00f3-4974-8ad4-566d1a00c6fc

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_connected_of_horizontalClusterCount_eq_one
import Theorems.Thm_QEC_Coding_FiberBundle_nonempty_supportedHorizontalCell_of_homologyBaseProjection_ne_zero
import Theorems.Thm_QEC_Coding_FiberBundle_exists_globalSlideIterate_isHorizontallyResidueNormalized_of_connected

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
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier)
    (hProjection : homologyBaseProjection z ≠ 0)
    (hCount :
      horizontalClusterCount baseSample twistSample z = 1) :
    ∃ z',
      HammingWeight z' = HammingWeight z ∧
      z' + z ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier ∧
      IsHorizontallyResidueNormalized z' := by
  let root : SupportedHorizontalCell z :=
    Classical.choice
      (nonempty_supportedHorizontalCell_of_homologyBaseProjection_ne_zero
        z hProjection)
  have hConnected :
      ∀ x, z (Sum.inl x) ≠ 0 →
        InSameSupportedHorizontalCluster
          baseSample twistSample z root.1 x := by
    intro x hx
    exact connected_of_horizontalClusterCount_eq_one
      baseSample twistSample z root hCount ⟨x, hx⟩
  rcases
      exists_globalSlideIterate_isHorizontallyResidueNormalized_of_connected
        baseSample twistSample z hz root.1 hConnected with
    ⟨k, hWeight, hHomologous, hNormalized⟩
  exact ⟨globalSlideIterate baseSample twistSample z k,
    hWeight, hHomologous, hNormalized⟩
end QEC.Coding.FiberBundle
