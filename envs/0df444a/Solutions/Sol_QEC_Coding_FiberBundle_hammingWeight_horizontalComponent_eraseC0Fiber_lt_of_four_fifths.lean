-- Prove2me | solution 1 for QEC.Coding.FiberBundle.hammingWeight_horizontalComponent_eraseC0Fiber_lt_of_four_fifths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:32:18.581278+00:00
-- url     : https://prove2.me/submissions/60f65de3-1d39-4f4f-a497-b5a8c06971c4

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Theorems.Thm_QEC_Coding_FiberBundle_horizontalBaseLift_add_bundleCoboundary_eraseC0Fiber
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_horizontalFiber_before_after_erase_of_counique
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_horizontalComponent_eq_sum_fibers
import Theorems.Thm_QEC_Coding_FiberBundle_sum_strictly_decreases_of_erased_savings
import Theorems.Thm_QEC_Coding_FiberBundle_erasureCorrection_cost_outside_counique_lt
import Theorems.Thm_QEC_Coding_HammingWeight_add_le


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (a : Fin (3 * r))
    (ha : a ∈ c0Shadow u)
    (hCounique :
      4 * RandomBase.checkDegree baseSample a <
        5 * RandomBase.couniqueDegree baseSample (c0Shadow u) a)
    (hDisjoint :
      ∀ b ∈ RandomBase.couniqueNeighbors baseSample (c0Shadow u),
        x b = 0) :
    HammingWeight
        (horizontalComponent
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample)
              (eraseC0Fiber u a))) <
      HammingWeight
        (horizontalComponent
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u)) := by
  let C :=
    (RandomBase.couniqueNeighbors baseSample (c0Shadow u)).filter
      fun b => baseSample (a, b)
  let oldRepresentative :=
    horizontalBaseLift
        (baseZero := Fin (3 * r))
        (fiberZero := ZMod (ell * ell))
        (fiberOne := ZMod (ell * ell)) x +
      bundleCoboundary
        (RandomTwist.fiberBundleData baseSample twistSample) u
  let newRepresentative :=
    horizontalBaseLift
        (baseZero := Fin (3 * r))
        (fiberZero := ZMod (ell * ell))
        (fiberOne := ZMod (ell * ell)) x +
      bundleCoboundary
        (RandomTwist.fiberBundleData baseSample twistSample)
        (eraseC0Fiber u a)
  let correction :=
    bundleCoboundary
      (RandomTwist.fiberBundleData baseSample twistSample)
      (eraseC0FiberCorrection u a)
  rw [hammingWeight_horizontalComponent_eq_sum_fibers,
    hammingWeight_horizontalComponent_eq_sum_fibers]
  apply sum_strictly_decreases_of_erased_savings
    C
    (fun b => HammingWeight (horizontalFiber oldRepresentative b))
    (fun b => HammingWeight (horizontalFiber newRepresentative b))
    (fun b => HammingWeight (horizontalFiber correction b))
    (HammingWeight (c0Fiber u a))
  · intro b hbC
    have hbCounique := (Finset.mem_filter.mp hbC).1
    have hab := (Finset.mem_filter.mp hbC).2
    exact
      (hammingWeight_horizontalFiber_before_after_erase_of_counique
        baseSample twistSample x u a b ha hbCounique hab
        (hDisjoint b hbCounique)).2
  · intro b hbC
    have hbCounique := (Finset.mem_filter.mp hbC).1
    have hab := (Finset.mem_filter.mp hbC).2
    exact
      (hammingWeight_horizontalFiber_before_after_erase_of_counique
        baseSample twistSample x u a b ha hbCounique hab
        (hDisjoint b hbCounique)).1
  · intro b _hbOutside
    have hRepresentative :=
      horizontalBaseLift_add_bundleCoboundary_eraseC0Fiber
        (RandomTwist.fiberBundleData baseSample twistSample) x u a
    have hFiber :
        horizontalFiber newRepresentative b =
          horizontalFiber oldRepresentative b + horizontalFiber correction b := by
      exact congrArg (fun y => horizontalFiber y b) hRepresentative
    rw [hFiber]
    exact HammingWeight_add_le _ _
  · exact erasureCorrection_cost_outside_counique_lt
      baseSample twistSample u (c0Shadow u) a ha hCounique
end QEC.Coding.FiberBundle
