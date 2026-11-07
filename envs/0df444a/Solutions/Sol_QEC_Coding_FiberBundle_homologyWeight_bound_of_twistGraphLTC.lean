-- Prove2me | solution 1 for QEC.Coding.FiberBundle.homologyWeight_bound_of_twistGraphLTC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:04:26.015967+00:00
-- url     : https://prove2.me/submissions/ba937762-edf7-43e6-a6c3-4f06025340a4

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_homologyBaseProjection_le_horizontalComponent
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_horizontalComponent_le
import Theorems.Thm_QEC_Coding_FiberBundle_baseDistance_bound_of_nontrivial_bundleCycle
import Theorems.Thm_QEC_Coding_FiberBundle_ell_mul_horizontalComponent_le_500_mul_verticalComponent_of_twistGraphLTC
import Theorems.Thm_QEC_Coding_FiberBundle_exists_slidHomologyRepresentative
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_eq_horizontal_add_vertical


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample)
    (hDistance : RandomBase.HasLinearDistance baseSample)
    (hLTC :
      TwistGraph.HasHHO20LocalTestability
        Delta baseSample twistSample)
    (hDelta : 1 ≤ Delta)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier)
    (hzNontrivial :
      z ∉ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleBoundaryCode.carrier) :
    ell * (4 * r) ≤
      5000 * Delta * HammingWeight z := by
  rcases exists_slidHomologyRepresentative
      baseSample twistSample z hz with
    ⟨z', hz', hWeight, _hHomologous, _hProjection,
      hNontrivialIff, hNormalized, _hShadow⟩
  have hz'Nontrivial := hNontrivialIff.mpr hzNontrivial
  have hBase :=
    baseDistance_bound_of_nontrivial_bundleCycle
      baseSample twistSample hRank hDistance z' hz' hz'Nontrivial
  have hProjection :=
    hammingWeight_homologyBaseProjection_le_horizontalComponent z'
  have hBaseHorizontal :
      4 * r ≤ 5 * HammingWeight (horizontalComponent z') :=
    hBase.trans (Nat.mul_le_mul_left 5 hProjection)
  have hHorizontalTotal :
      HammingWeight (horizontalComponent z') ≤ HammingWeight z' :=
    hammingWeight_horizontalComponent_le z'
  have hVerticalTotal :
      HammingWeight (verticalComponent z') ≤ HammingWeight z' := by
    have hDecomp := hammingWeight_eq_horizontal_add_vertical z'
    omega
  by_cases hSmall :
      5000 * Delta * HammingWeight (horizontalComponent z') ≤
        ell * (4 * r)
  · have hStrong :=
      ell_mul_horizontalComponent_le_500_mul_verticalComponent_of_twistGraphLTC
        baseSample twistSample hLTC z' hz' hNormalized hSmall
    calc
      ell * (4 * r) ≤
          ell * (5 * HammingWeight (horizontalComponent z')) :=
        Nat.mul_le_mul_left ell hBaseHorizontal
      _ = 5 * (ell * HammingWeight (horizontalComponent z')) := by
        ac_rfl
      _ ≤ 5 * (500 * HammingWeight (verticalComponent z')) :=
        Nat.mul_le_mul_left 5 hStrong
      _ = 2500 * HammingWeight (verticalComponent z') := by ring
      _ ≤ 2500 * HammingWeight z' :=
        Nat.mul_le_mul_left 2500 hVerticalTotal
      _ ≤ 2500 * HammingWeight z :=
        Nat.mul_le_mul_left 2500 hWeight
      _ ≤ 5000 * Delta * HammingWeight z := by
        have hCoefficient : 2500 ≤ 5000 * Delta := by nlinarith
        exact Nat.mul_le_mul_right (HammingWeight z) hCoefficient
  · have hLarge :
        ell * (4 * r) <
          5000 * Delta * HammingWeight (horizontalComponent z') :=
      Nat.lt_of_not_ge hSmall
    calc
      ell * (4 * r) ≤
          5000 * Delta * HammingWeight (horizontalComponent z') :=
        Nat.le_of_lt hLarge
      _ ≤ 5000 * Delta * HammingWeight z' :=
        Nat.mul_le_mul_left (5000 * Delta) hHorizontalTotal
      _ ≤ 5000 * Delta * HammingWeight z :=
        Nat.mul_le_mul_left (5000 * Delta) hWeight
end QEC.Coding.FiberBundle
