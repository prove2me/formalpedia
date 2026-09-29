-- Prove2me | solution 1 for TwoChartCech.Cover.LaurentChart.residue_mapOfRingHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/6a50bd1c-277b-58ac-bc38-1695880f61d2

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechLaurentChart
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TwoChartCech_Cover_LaurentChart_residue_mapOfRingHom

universe u v

theorem solution {R : Type u} {S : Type u} [CommRing R] [CommRing S]
    {𝒰 : TwoChartCech.Cover.{u, v} R} {𝒲 : TwoChartCech.Cover.{u, v} S}
    (τ : R →+* S) (φ : 𝒰.A01 →+* 𝒲.A01)
    (h : φ.comp (algebraMap R 𝒰.A01) = (algebraMap S 𝒲.A01).comp τ)
    (Λ : 𝒰.LaurentChart) (Λ' : 𝒲.LaurentChart) (hΛ : ∀ y : 𝒰.A01, Λ'.expand (φ y) = (Λ.expand y).map τ)
    (η : Ω[𝒰.A01⁄R]) :
    Λ'.residue (KaehlerDifferential.mapOfRingHom τ φ h η) = τ (Λ.residue η) := by
  have key := KaehlerDifferential.addMonoidHom_ext_smul_D
    (f := Λ'.residue.toAddMonoidHom.comp (KaehlerDifferential.mapOfRingHom τ φ h).toAddMonoidHom)
    (g := τ.toAddMonoidHom.comp Λ.residue.toAddMonoidHom) (fun a s => by
      change Λ'.residue (KaehlerDifferential.mapOfRingHom τ φ h (a • KaehlerDifferential.D R 𝒰.A01 s)) =
        τ (Λ.residue (a • KaehlerDifferential.D R 𝒰.A01 s))
      rw [KaehlerDifferential.mapOfRingHom_smul_D, TwoChartCech.Cover.LaurentChart.residue_smul_D,
        TwoChartCech.Cover.LaurentChart.residue_smul_D, hΛ, hΛ, ← LaurentSeries.map_derivative, ← HahnSeries.map_coeff]
      congr 1
      exact (HahnSeries.map_mul τ.toNonUnitalRingHom).symm)
  exact DFunLike.congr_fun key η

end S_TwoChartCech_Cover_LaurentChart_residue_mapOfRingHom
end P2MW
export P2MW.S_TwoChartCech_Cover_LaurentChart_residue_mapOfRingHom (solution)
