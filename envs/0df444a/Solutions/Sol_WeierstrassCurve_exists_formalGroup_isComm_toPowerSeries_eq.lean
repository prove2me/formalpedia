-- Prove2me | solution 1 for WeierstrassCurve.exists_formalGroup_isComm_toPowerSeries_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/44b55475-8da0-5efb-a3f5-0a606ce1964c

import Mathlib
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Theorems.Thm_WeierstrassCurve_formalW_map_and_formalGroupLawFixed_map
import Theorems.Thm_WeierstrassCurve_formalGroupLawFixed_comm_of_commRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_formalGroup_isComm_toPowerSeries_eq

set_option autoImplicit false

universe u

open MvPowerSeries

namespace FGLExists

abbrev U : Type := MvPolynomial (Fin 5) ℤ

noncomputable def Wu : WeierstrassCurve U :=
  ⟨MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, MvPolynomial.X 3, MvPolynomial.X 4⟩

theorem map_Wu {R : Type u} [CommRing R] (W : WeierstrassCurve R) :
    Wu.map (MvPolynomial.eval₂Hom (Int.castRingHom R) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]) = W := by
  ext <;> simp [Wu, WeierstrassCurve.map]

theorem Δ_Wu_ne_zero : Wu.Δ ≠ 0 := by
  intro h
  have h2 : (Wu.map (MvPolynomial.eval (![0, 0, 0, -1, 0] : Fin 5 → ℤ))).Δ = 64 := by
    simp [Wu, WeierstrassCurve.map, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  rw [WeierstrassCurve.map_Δ, h, map_zero] at h2
  norm_num at h2

theorem map_injective' {σ : Type*} {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) : Function.Injective (MvPowerSeries.map (σ := σ) f) := by
  intro a b h
  ext n
  apply hf
  rw [← MvPowerSeries.coeff_map, ← MvPowerSeries.coeff_map, h]

theorem exists_G₀ : ∃ G : FormalGroup U, G.toPowerSeries = Wu.formalGroupLawFixed := by
  let ι : U →+* FractionRing U := algebraMap U (FractionRing U)
  have hι : Function.Injective ι := IsFractionRing.injective U (FractionRing U)
  haveI : (Wu.map ι).IsElliptic := ⟨isUnit_iff_ne_zero.mpr (by
    rw [WeierstrassCurve.map_Δ]; exact (map_ne_zero_iff ι hι).mpr Δ_Wu_ne_zero)⟩
  have hG : (Wu.map ι).formalGroup.toPowerSeries = MvPowerSeries.map ι Wu.formalGroupLawFixed :=
    (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map Wu ι).2
  have hinj3 := map_injective' (σ := Fin 3) ι hι
  have h0 : Wu.formalGroupLawFixed.constantCoeff = 0 := by
    apply hι
    rw [← MvPowerSeries.constantCoeff_map, ← hG, map_zero]
    exact (Wu.map ι).formalGroup.zero_constantCoeff
  have hX : Wu.formalGroupLawFixed.coeff (Finsupp.single 0 1) = 1 := by
    apply hι
    rw [← MvPowerSeries.coeff_map, ← hG, map_one]
    exact (Wu.map ι).formalGroup.lin_coeff_X
  have hY : Wu.formalGroupLawFixed.coeff (Finsupp.single 1 1) = 1 := by
    apply hι
    rw [← MvPowerSeries.coeff_map, ← hG, map_one]
    exact (Wu.map ι).formalGroup.lin_coeff_Y
  have key := (Wu.map ι).formalGroup.assoc
  rw [hG] at key
  have hvec : ∀ (g₁ g₂ : MvPowerSeries (Fin 3) U),
      ![g₁.map ι, g₂.map ι] = fun i => (![g₁, g₂] i).map ι := by
    intro g₁ g₂; ext1 i; fin_cases i <;> simp
  simp_rw [(MvPowerSeries.map_X ι _).symm, hvec, ← MvPowerSeries.map_subst .X_X, hvec,
    ← MvPowerSeries.map_subst (HasSubst.cons_subst_zero_left (0 : Fin 3) 1 2 h0),
    ← MvPowerSeries.map_subst (HasSubst.cons_subst_zero_right (0 : Fin 3) 1 2 h0)] at key
  exact ⟨{ toPowerSeries := Wu.formalGroupLawFixed
           zero_constantCoeff := h0
           lin_coeff_X := hX
           lin_coeff_Y := hY
           assoc := hinj3 key }, rfl⟩

end FGLExists

theorem solution
    {R : Type u} [CommRing R] (W : WeierstrassCurve R) :
    ∃ (F : FormalGroup R) (_ : F.IsComm), F.toPowerSeries = W.formalGroupLawFixed := by
  obtain ⟨G, hG⟩ := FGLExists.exists_G₀
  let φ : FGLExists.U →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]
  have hF : (G.map φ).toPowerSeries = W.formalGroupLawFixed := by
    show MvPowerSeries.map φ G.toPowerSeries = _
    rw [hG, ← (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map FGLExists.Wu φ).2, FGLExists.map_Wu]
  refine ⟨G.map φ, ⟨?_⟩, hF⟩
  show (G.map φ).toPowerSeries = (G.map φ).toPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0]
  rw [hF]
  exact WeierstrassCurve.formalGroupLawFixed_comm_of_commRing W

end S_WeierstrassCurve_exists_formalGroup_isComm_toPowerSeries_eq
end P2MW
export P2MW.S_WeierstrassCurve_exists_formalGroup_isComm_toPowerSeries_eq (solution)
