-- Prove2me | solution 1 for TarchaBraids.braid_corrects_to_pure_range_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-23T00:28:11.070962+00:00
-- url     : https://prove2.me/submissions/3592204c-891e-44da-a067-39e16a2d202a

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Theorems.Thm_TarchaBraids_configProj_isQuotientCoveringMap_v1
import Theorems.Thm_TarchaBraids_braid_corrects_to_pure_range_of_quotient_v1

open BraidsLinksMCG TarchaBraids

/-- Every geometric braid is corrected into the image of the ordered-configuration
fundamental group by an explicit half-twist word; obtained by specialising the
quotient-covering statement to `configProj_isQuotientCoveringMap_v1`. -/
theorem solution (n : ℕ) (β : GeomBraidGroup n) :
    ∃ w : FreeGroup (Fin (n - 1)),
      β * (FreeGroup.lift (fun i : Fin (n - 1) => halfTwistBraid n i) w)⁻¹ ∈
        (FundamentalGroup.mapOfEq
          ⟨configProj n, (configProj_isQuotientCoveringMap_v1 n).continuous⟩
          (show configProj n (baseOrdered n) = baseUnordered n from rfl)).range :=
  braid_corrects_to_pure_range_of_quotient_v1 n
    (configProj_isQuotientCoveringMap_v1 n) β
