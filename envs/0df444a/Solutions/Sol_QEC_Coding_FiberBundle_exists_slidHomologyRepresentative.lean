-- Prove2me | solution 1 for QEC.Coding.FiberBundle.exists_slidHomologyRepresentative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:36:17.589257+00:00
-- url     : https://prove2.me/submissions/20d8588f-78e6-49f9-9d0e-f243626f3bc0

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_ell_mul_card_horizontalBoundaryShadow_le_verticalComponent
import Theorems.Thm_QEC_Coding_FiberBundle_exists_homologous_isHorizontallyResidueNormalized
import Theorems.Thm_QEC_Coding_FiberBundle_homologyBaseProjection_eq_of_add_mem_middleBoundaryCode
import Theorems.Thm_QEC_Coding_FiberBundle_mem_middleBoundaryCode_iff_of_add_mem

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
        ).middleCycleCode.carrier) :
    ∃ z',
      z' ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier ∧
      HammingWeight z' ≤ HammingWeight z ∧
      z' + z ∈
        (chainComplex
          (RandomTwist.fiberBundleData baseSample twistSample)
          ).middleBoundaryCode.carrier ∧
      homologyBaseProjection z' = homologyBaseProjection z ∧
      (z' ∉
          (chainComplex
            (RandomTwist.fiberBundleData baseSample twistSample)
            ).middleBoundaryCode.carrier ↔
        z ∉
          (chainComplex
            (RandomTwist.fiberBundleData baseSample twistSample)
            ).middleBoundaryCode.carrier) ∧
      IsHorizontallyResidueNormalized z' ∧
      ell *
          (horizontalBoundaryShadow baseSample twistSample
            (horizontalComponent z')).card ≤
        HammingWeight (verticalComponent z') := by
  rcases exists_homologous_isHorizontallyResidueNormalized
      baseSample twistSample z hz with
    ⟨z', hz', hWeight, hHomologous, hNormalized⟩
  refine ⟨z', hz', hWeight, hHomologous, ?_, ?_,
    hNormalized, ?_⟩
  · exact homologyBaseProjection_eq_of_add_mem_middleBoundaryCode
      baseSample twistSample z' z hHomologous
  · exact not_congr
      (mem_middleBoundaryCode_iff_of_add_mem
        baseSample twistSample z' z hHomologous)
  · exact ell_mul_card_horizontalBoundaryShadow_le_verticalComponent
      baseSample twistSample z' hz' hNormalized
end QEC.Coding.FiberBundle
