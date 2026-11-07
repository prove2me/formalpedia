-- Prove2me | solution 1 for QEC.Coding.FiberBundle.twice_hammingWeight_horizontalFiber_bundleCoboundary_le_card_of_counique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:09:29.057315+00:00
-- url     : https://prove2.me/submissions/36e378ac-33db-40c4-8a9e-f6d7f36fe16a

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Theorems.Thm_QEC_Coding_FiberBundle_c0Fiber_eq_zero_of_not_mem_c0Shadow
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_reindexWord
import Theorems.Thm_QEC_Coding_FiberBundle_exists_horizontalFiber_bundleCoboundary_eq_of_counique

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hu : C0FibersNormalized u)
    (b : Fin (4 * r))
    (hb : b ∈ RandomBase.couniqueNeighbors baseSample (c0Shadow u)) :
    2 * HammingWeight
        (horizontalFiber
          (bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample) u) b) ≤
      Fintype.card (ZMod (ell * ell)) := by
  have huOutside :
      ∀ a, a ∉ c0Shadow u → c0Fiber u a = 0 := by
    intro a ha
    exact c0Fiber_eq_zero_of_not_mem_c0Shadow u ha
  rcases
      exists_horizontalFiber_bundleCoboundary_eq_of_counique
        baseSample twistSample u (c0Shadow u) b hb huOutside with
    ⟨a, _ha, _haEdge, hfiber⟩
  rw [hfiber, hammingWeight_reindexWord]
  exact hu a
end QEC.Coding.FiberBundle
