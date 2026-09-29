-- Prove2me | solution 1 for WeierstrassProjModel.toProjective_isElliptic_map_of_isGoodPrimeFor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/c237557b-3cd8-5cc6-b19f-71c54e348772

import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_GaloisRep_ratLocalizedAt_isUnit_iff
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_toProjective_isElliptic_map_of_isGoodPrimeFor

set_option autoImplicit false

open WeierstrassCurve GaloisRep

private theorem coe_algebraMap_int_ratLocalizedAt (p : ℕ) (n : ℤ) :
    ((algebraMap ℤ (ratLocalizedAt p) n : ratLocalizedAt p) : ℚ) = (n : ℚ) :=
  eq_intCast ((ratLocalizedAt p).subtype.comp (algebraMap ℤ (ratLocalizedAt p))) n

private theorem isUnit_map_Δ_of_isGoodPrimeFor
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hgood : W.IsGoodPrimeFor p) :
    IsUnit (algebraMap ℤ (ratLocalizedAt p) W.Δ) := by
  rw [GaloisRep.ratLocalizedAt.isUnit_iff (Fact.out : p.Prime),
    coe_algebraMap_int_ratLocalizedAt, Rat.num_intCast]
  exact fun h => hgood (Int.natCast_dvd.mpr h)

private theorem isElliptic_map_of_isGoodPrimeFor
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hgood : W.IsGoodPrimeFor p) :
    (W.map (algebraMap ℤ (ratLocalizedAt p))).IsElliptic := by
  rw [isElliptic_iff, map_Δ]
  exact isUnit_map_Δ_of_isGoodPrimeFor W p hgood

theorem solution
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hgood : W.IsGoodPrimeFor p) :
    (W.map (algebraMap ℤ (ratLocalizedAt p))).toProjective.IsElliptic :=
  ⟨(isElliptic_map_of_isGoodPrimeFor W p hgood).isUnit⟩

end S_WeierstrassProjModel_toProjective_isElliptic_map_of_isGoodPrimeFor
end P2MW
export P2MW.S_WeierstrassProjModel_toProjective_isElliptic_map_of_isGoodPrimeFor (solution)
