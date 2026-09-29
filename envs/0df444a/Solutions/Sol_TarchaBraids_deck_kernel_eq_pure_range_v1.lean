-- Prove2me | solution 1 for TarchaBraids.deck_kernel_eq_pure_range_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-22T04:32:37.327005+00:00
-- url     : https://prove2.me/submissions/2955e0f3-a396-4cd3-87e5-40472b66128c

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_endpoint_permutation_action_v1

open BraidsLinksMCG TarchaBraids

theorem solution (n : ℕ)
    (hp : IsQuotientCoveringMap (configProj n) (Equiv.Perm (Fin n))) :
    (hp.fundamentalGroupToMulOpposite
      (⟨baseOrdered n, rfl⟩ : (configProj n) ⁻¹' {baseUnordered n})).ker =
    (FundamentalGroup.mapOfEq
      ⟨configProj n, hp.continuous⟩
      (show configProj n (baseOrdered n) = baseUnordered n from rfl)).range := by
  let e : (configProj n) ⁻¹' {baseUnordered n} :=
    ⟨baseOrdered n, rfl⟩
  calc
    (hp.fundamentalGroupToMulOpposite
      (⟨baseOrdered n, rfl⟩ : (configProj n) ⁻¹' {baseUnordered n})).ker =
        (hp.isCoveringMap.monodromyPerm (baseUnordered n)).ker := by
      simpa [e] using hp.ker_fundamentalGroupToMulOpposite e
    _ = (FundamentalGroup.mapOfEq
        ⟨configProj n, hp.continuous⟩
        (show configProj n (baseOrdered n) = baseUnordered n from rfl)).range := by
      simpa [e] using hp.ker_monodromyPerm e
