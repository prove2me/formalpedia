-- Prove2me | solution 1 for QEC.Coding.FiberBundle.horizontal_half_or_exists_descent_check
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:01:06.06937+00:00
-- url     : https://prove2.me/submissions/0ab8686d-005b-4ab7-842c-b5a1560d4600

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Theorems.Thm_QEC_Coding_FiberBundle_card_le_twice_hammingWeight_horizontalComponent_add_lift_of_counique
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_exists_check_four_fifths_counique


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (u : Word (ZMod 2)
      (C0Index (Fin (3 * r)) (ZMod (ell * ell))))
    (hDelta : 0 < Delta)
    (hDegree : RandomBase.HasDegreeWindows (Delta := Delta) baseSample)
    (hExpansion :
      RandomBase.HasStrongSmallSetExpansion (Delta := Delta) baseSample)
    (hShadowNonempty : (c0Shadow (normalizeC0Fibers u)).Nonempty)
    (hSmall :
      100000 * Delta * (c0Shadow (normalizeC0Fibers u)).card ≤ 3 * r) :
    Fintype.card (ZMod (ell * ell)) ≤
        2 * HammingWeight
          (horizontalComponent
            (horizontalBaseLift
                (baseZero := Fin (3 * r))
                (fiberZero := ZMod (ell * ell))
                (fiberOne := ZMod (ell * ell)) x +
              bundleCoboundary
                (RandomTwist.fiberBundleData baseSample twistSample)
                (normalizeC0Fibers u))) ∨
      ∃ a ∈ c0Shadow (normalizeC0Fibers u),
        4 * RandomBase.checkDegree baseSample a <
          5 * RandomBase.couniqueDegree baseSample
            (c0Shadow (normalizeC0Fibers u)) a ∧
        ∀ b ∈ RandomBase.couniqueNeighbors baseSample
            (c0Shadow (normalizeC0Fibers u)),
          x b = 0 := by
  rcases RandomBase.exists_check_four_fifths_counique
      hDelta hDegree hExpansion
      (c0Shadow (normalizeC0Fibers u)) hShadowNonempty hSmall with
    ⟨a, haShadow, haCounique⟩
  by_cases hSupported :
      ∃ b ∈ RandomBase.couniqueNeighbors baseSample
        (c0Shadow (normalizeC0Fibers u)), x b ≠ 0
  · rcases hSupported with ⟨b, hbCounique, hxb⟩
    exact Or.inl
      (card_le_twice_hammingWeight_horizontalComponent_add_lift_of_counique
        baseSample twistSample x u b hbCounique hxb)
  · right
    refine ⟨a, haShadow, haCounique, ?_⟩
    intro b hbCounique
    by_contra hxb
    exact hSupported ⟨b, hbCounique, hxb⟩
end QEC.Coding.FiberBundle
