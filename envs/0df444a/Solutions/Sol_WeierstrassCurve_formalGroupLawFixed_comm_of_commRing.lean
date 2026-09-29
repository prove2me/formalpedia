-- Prove2me | solution 1 for WeierstrassCurve.formalGroupLawFixed_comm_of_commRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/ea500376-74dd-5455-8252-ffc19fe24323

import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Theorems.Thm_WeierstrassCurve_formalW_map_and_formalGroupLawFixed_map
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_formalGroupLawFixed_comm_of_commRing

set_option autoImplicit false

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "a₃ ofJ0 a₁ map a₄ ofJ0_Δ a₂ a₆ map_Δ Δ formalGroupLawFixed formalGroupLawFixed_comm formalW_map_and_formalGroupLawFixed_map"
p2m_open "WeierstrassCurve"

open MvPowerSeries

theorem commW_swap_map {U R : Type*} [CommRing U] [CommRing R] (φ : U →+* R) :
    (fun i => MvPowerSeries.map φ ((![MvPowerSeries.X 1, MvPowerSeries.X 0] : Fin 2 → MvPowerSeries (Fin 2) U) i)) =
      (![MvPowerSeries.X 1, MvPowerSeries.X 0] : Fin 2 → MvPowerSeries (Fin 2) R) := by
  funext i
  fin_cases i <;> simp [MvPowerSeries.map_X]

theorem commW_of_map {U R : Type*} [CommRing U] [CommRing R] (φ : U →+* R) (Wu : WeierstrassCurve U)
    (hU : Wu.formalGroupLawFixed =
      MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] Wu.formalGroupLawFixed) :
    (Wu.map φ).formalGroupLawFixed =
      MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] (Wu.map φ).formalGroupLawFixed := by
  rw [(Wu.formalW_map_and_formalGroupLawFixed_map φ).2]
  conv_lhs => rw [hU]
  rw [MvPowerSeries.map_subst MvPowerSeries.HasSubst.X_X, commW_swap_map]

theorem commW_of_injective {U K : Type*} [CommRing U] [CommRing K] [IsDomain K] (ι : U →+* K)
    (hι : Function.Injective ι) (Wu : WeierstrassCurve U) [(Wu.map ι).IsElliptic] :
    Wu.formalGroupLawFixed =
      MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] Wu.formalGroupLawFixed := by
  have hK := (Wu.map ι).formalGroupLawFixed_comm
  rw [(Wu.formalW_map_and_formalGroupLawFixed_map ι).2, ← commW_swap_map ι,
    ← MvPowerSeries.map_subst MvPowerSeries.HasSubst.X_X] at hK

  ext d
  have h := congrArg (MvPowerSeries.coeff d) hK
  rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map] at h
  exact (hι h).symm

noncomputable def commW_univ : WeierstrassCurve (MvPolynomial (Fin 5) ℤ) :=
  ⟨MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, MvPolynomial.X 3, MvPolynomial.X 4⟩

theorem commW_univ_Δ_ne_zero : commW_univ.Δ ≠ 0 := by
  intro h0
  have h1 : (commW_univ.map (MvPolynomial.eval ![(0 : ℤ), 0, 1, 0, 0])).Δ = (WeierstrassCurve.ofJ0 ℤ).Δ := by
    congr 1
    ext <;> simp [commW_univ, WeierstrassCurve.ofJ0, MvPolynomial.eval_X]
  rw [WeierstrassCurve.map_Δ, h0, map_zero, WeierstrassCurve.ofJ0_Δ] at h1
  norm_num at h1

theorem commW_univ_comm :
    commW_univ.formalGroupLawFixed =
      MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] commW_univ.formalGroupLawFixed := by
  let K := FractionRing (MvPolynomial (Fin 5) ℤ)
  have hι : Function.Injective (algebraMap (MvPolynomial (Fin 5) ℤ) K) :=
    IsFractionRing.injective (MvPolynomial (Fin 5) ℤ) K
  haveI : (commW_univ.map (algebraMap (MvPolynomial (Fin 5) ℤ) K)).IsElliptic :=
    ⟨by
      rw [WeierstrassCurve.map_Δ, isUnit_iff_ne_zero]
      exact (map_ne_zero_iff _ hι).mpr commW_univ_Δ_ne_zero⟩
  exact commW_of_injective (algebraMap (MvPolynomial (Fin 5) ℤ) K) hι commW_univ

end WeierstrassCurve

theorem solution
    {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    W.formalGroupLawFixed =
      MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] W.formalGroupLawFixed := by
  have hW : WeierstrassCurve.commW_univ.map
      (MvPolynomial.eval₂Hom (Int.castRingHom R) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]) = W := by
    ext <;> simp [WeierstrassCurve.commW_univ, MvPolynomial.eval₂Hom_X']
  have h := WeierstrassCurve.commW_of_map
    (MvPolynomial.eval₂Hom (Int.castRingHom R) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆])
    WeierstrassCurve.commW_univ WeierstrassCurve.commW_univ_comm
  rwa [hW] at h

end S_WeierstrassCurve_formalGroupLawFixed_comm_of_commRing
end P2MW
export P2MW.S_WeierstrassCurve_formalGroupLawFixed_comm_of_commRing (solution)
