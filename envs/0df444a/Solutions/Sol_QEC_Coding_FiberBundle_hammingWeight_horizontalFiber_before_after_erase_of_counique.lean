-- Prove2me | solution 1 for QEC.Coding.FiberBundle.hammingWeight_horizontalFiber_before_after_erase_of_counique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:29:22.197334+00:00
-- url     : https://prove2.me/submissions/e53f2deb-ec0e-4afd-a712-93486aa0458c

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Theorems.Thm_QEC_Coding_FiberBundle_c0Fiber_eq_zero_of_not_mem_c0Shadow
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_reindexWord
import Theorems.Thm_QEC_Coding_FiberBundle_horizontalBaseLift_add_bundleCoboundary_eraseC0Fiber
import Theorems.Thm_QEC_Coding_FiberBundle_horizontalFiber_bundleCoboundary_eraseC0FiberCorrection
import Theorems.Thm_QEC_Coding_FiberBundle_exists_horizontalFiber_bundleCoboundary_eq_of_counique
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_mem_couniqueNeighbors_iff_exists_unique


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
    (a : Fin (3 * r)) (b : Fin (4 * r))
    (ha : a ∈ c0Shadow u)
    (hb : b ∈ RandomBase.couniqueNeighbors baseSample (c0Shadow u))
    (hab : baseSample (a, b) = true)
    (hxb : x b = 0) :
    HammingWeight
        (horizontalFiber
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u) b) =
        HammingWeight (c0Fiber u a) ∧
      HammingWeight
        (horizontalFiber
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample)
              (eraseC0Fiber u a)) b) = 0 := by
  have huOutside :
      ∀ a', a' ∉ c0Shadow u → c0Fiber u a' = 0 := by
    intro a' ha'
    exact c0Fiber_eq_zero_of_not_mem_c0Shadow u ha'
  rcases
      exists_horizontalFiber_bundleCoboundary_eq_of_counique
        baseSample twistSample u (c0Shadow u) b hb huOutside with
    ⟨a', ha'Shadow, ha'Edge, hCoboundary⟩
  rcases
      (RandomBase.mem_couniqueNeighbors_iff_exists_unique
        baseSample (c0Shadow u) b).mp hb with
    ⟨aUnique, _haUniqueShadow, _haUniqueEdge, hUnique⟩
  have ha'eq : a' = a := by
    exact (hUnique a' ha'Shadow ha'Edge).trans
      (hUnique a ha hab).symm
  subst a'
  let f :=
    reindexWord
      ((RandomTwist.fiberBundleData baseSample twistSample).connection b a).onZero.symm
      (c0Fiber u a)
  have hOldFiber :
      horizontalFiber
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u) b =
        f := by
    funext i
    change x b + horizontalFiber
      (bundleCoboundary
        (RandomTwist.fiberBundleData baseSample twistSample) u) b i = f i
    rw [hxb, zero_add, hCoboundary]
  have hCorrection :
      horizontalFiber
          (bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (eraseC0FiberCorrection u a)) b =
        f := by
    rw [horizontalFiber_bundleCoboundary_eraseC0FiberCorrection,
      if_pos hab]
  constructor
  · rw [hOldFiber, hammingWeight_reindexWord]
  · have hRepresentative :=
      horizontalBaseLift_add_bundleCoboundary_eraseC0Fiber
        (RandomTwist.fiberBundleData baseSample twistSample) x u a
    apply (HammingWeight_eq_zero_iff _).2
    rw [hRepresentative]
    funext i
    change
      horizontalFiber
          (horizontalBaseLift
              (baseZero := Fin (3 * r))
              (fiberZero := ZMod (ell * ell))
              (fiberOne := ZMod (ell * ell)) x +
            bundleCoboundary
              (RandomTwist.fiberBundleData baseSample twistSample) u) b i +
        horizontalFiber
          (bundleCoboundary
            (RandomTwist.fiberBundleData baseSample twistSample)
            (eraseC0FiberCorrection u a)) b i = 0
    rw [hOldFiber, hCorrection]
    calc
      f i + f i = f i + (-f i) := by rw [ZMod.neg_eq_self_mod_two]
      _ = 0 := add_neg_cancel _
end QEC.Coding.FiberBundle
