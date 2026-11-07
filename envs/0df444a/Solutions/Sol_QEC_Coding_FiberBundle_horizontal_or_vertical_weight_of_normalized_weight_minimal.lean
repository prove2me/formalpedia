-- Prove2me | solution 1 for QEC.Coding.FiberBundle.horizontal_or_vertical_weight_of_normalized_weight_minimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:54:00.444076+00:00
-- url     : https://prove2.me/submissions/595c2fdb-189a-4f92-831b-17440e124f68

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Theorems.Thm_QEC_Coding_FiberBundle_card_le_twice_hammingWeight_horizontalComponent_add_lift_of_shadow_empty
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_eraseC0Fiber_lt_of_four_fifths
import Theorems.Thm_QEC_Coding_FiberBundle_large_shadow_vertical_weight_of_normalized
import Theorems.Thm_QEC_Coding_FiberBundle_horizontal_half_or_exists_descent_check_of_normalized

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
    (hx : x ≠ 0)
    (hu : C0FibersNormalized u)
    (hMinimal : IsWeightMinimal baseSample twistSample x u)
    (hDelta : 0 < Delta)
    (hDegree : RandomBase.HasDegreeWindows (Delta := Delta) baseSample)
    (hExpansion :
      RandomBase.HasStrongSmallSetExpansion (Delta := Delta) baseSample) :
    Fintype.card (ZMod (ell * ell)) ≤
        2 * HammingWeight
          (horizontalComponent
            (horizontalBaseLift
                (baseZero := Fin (3 * r))
                (fiberZero := ZMod (ell * ell))
                (fiberOne := ZMod (ell * ell)) x +
              bundleCoboundary
                (RandomTwist.fiberBundleData baseSample twistSample) u)) ∨
      6 * r <
        100000 * Delta *
          HammingWeight
            (verticalComponent
              (horizontalBaseLift
                  (baseZero := Fin (3 * r))
                  (fiberZero := ZMod (ell * ell))
                  (fiberOne := ZMod (ell * ell)) x +
                bundleCoboundary
                  (RandomTwist.fiberBundleData baseSample twistSample) u)) := by
  by_cases hShadowEmpty : c0Shadow u = ∅
  · exact Or.inl
      (card_le_twice_hammingWeight_horizontalComponent_add_lift_of_shadow_empty
        baseSample twistSample x u hx hShadowEmpty)
  · have hShadowNonempty : (c0Shadow u).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hShadowEmpty
    by_cases hLarge : 3 * r < 100000 * Delta * (c0Shadow u).card
    · exact Or.inr
        (large_shadow_vertical_weight_of_normalized
          baseSample twistSample x u hu hLarge)
    · have hSmall :
          100000 * Delta * (c0Shadow u).card ≤ 3 * r :=
        Nat.le_of_not_gt hLarge
      rcases
          horizontal_half_or_exists_descent_check_of_normalized
            baseSample twistSample x u hu hDelta hDegree hExpansion
            hShadowNonempty hSmall with
        hHorizontal | ⟨a, haShadow, haCounique, hDisjoint⟩
      · exact Or.inl hHorizontal
      · have hStrict :=
          hammingWeight_eraseC0Fiber_lt_of_four_fifths
            baseSample twistSample x u a haShadow haCounique hDisjoint
        have hLeast := hMinimal (eraseC0Fiber u a)
        exact (Nat.not_lt_of_ge hLeast hStrict).elim
end QEC.Coding.FiberBundle
