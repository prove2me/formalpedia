-- Prove2me | solution 1 for WeierstrassCurve.exists_formalGroup_toPowerSeries_eq_formalGroupLawFixed_map_and_nthSeries_eq_X_mul_map_mul_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/7931ccf9-850e-5596-8e08-c4f92700cf0d

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Theorems.Thm_FormalGroup_IsBaseChange_nthSeries_eq_map
import Theorems.Thm_WeierstrassCurve_formalW_map_and_formalGroupLawFixed_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_formalGroup_toPowerSeries_eq_formalGroupLawFixed_map_and_nthSeries_eq_X_mul_map_mul_map

set_option autoImplicit false

open Polynomial

theorem solution
    {S T : Type} [CommRing S] [CommRing T] (Φ : S →+* T)
    (V : WeierstrassCurve S) (FS : FormalGroup S) (hFS : FS.toPowerSeries = V.formalGroupLawFixed)
    (q : ℕ) (g : S[X]) (v : PowerSeries S)
    (hfacq : FS.nthSeries q = PowerSeries.X * (↑g : PowerSeries S) * v) :
    ∃ FT : FormalGroup T, FT.toPowerSeries = (V.map Φ).formalGroupLawFixed ∧
      FT.nthSeries q = PowerSeries.X * (↑(g.map Φ) : PowerSeries T) * PowerSeries.map Φ v := by
  refine ⟨FS.map Φ, ?_, ?_⟩
  · rw [FormalGroup.map_toPowerSeries, hFS, (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map V Φ).2]
  · have hbc : FS.IsBaseChange Φ (FS.map Φ) := FormalGroup.map_toPowerSeries FS Φ
    rw [FormalGroup.IsBaseChange.nthSeries_eq_map FS Φ (FS.map Φ) hbc q, hfacq, map_mul, map_mul,
      PowerSeries.map_X, Polynomial.polynomial_map_coe]

end S_WeierstrassCurve_exists_formalGroup_toPowerSeries_eq_formalGroupLawFixed_map_and_nthSeries_eq_X_mul_map_mul_map
end P2MW
export P2MW.S_WeierstrassCurve_exists_formalGroup_toPowerSeries_eq_formalGroupLawFixed_map_and_nthSeries_eq_X_mul_map_mul_map (solution)
