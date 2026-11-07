-- Prove2me | solution 1 for QEC.Coding.FiberBundle.exists_isHorizontalWeightMinimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:31:19.441745+00:00
-- url     : https://prove2.me/submissions/bdaae0a9-e88a-45ba-bb76-3a18cfbb12b5

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r))) :
    ∃ u : Word (ZMod 2)
        (C0Index (Fin (3 * r)) (ZMod (ell * ell))),
      IsHorizontalWeightMinimal baseSample twistSample x u := by
  classical
  let weight := fun u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))) =>
    HammingWeight
      (horizontalComponent
        (horizontalBaseLift
            (baseZero := Fin (3 * r))
            (fiberZero := ZMod (ell * ell))
            (fiberOne := ZMod (ell * ell)) x +
          bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample) u))
  obtain ⟨u, _hu, hleast⟩ :=
    Finset.exists_min_image
      (Finset.univ : Finset
        (Word (ZMod 2)
          (C0Index (Fin (3 * r)) (ZMod (ell * ell)))))
      weight Finset.univ_nonempty
  refine ⟨u, ?_⟩
  intro v
  exact hleast v (Finset.mem_univ v)
end QEC.Coding.FiberBundle
