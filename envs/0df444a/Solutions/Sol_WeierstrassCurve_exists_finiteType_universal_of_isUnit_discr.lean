-- Prove2me | solution 1 for WeierstrassCurve.exists_finiteType_universal_of_isUnit_discr
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/5140f8d8-c70e-5d3a-a555-a4f02e435756

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_finiteType_universal_of_isUnit_discr

set_option autoImplicit false

universe u

open MvPolynomial

noncomputable section

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "a₃ map_map a₁ map a₄ a₂ a₆ ψ₂ map_Δ Δ"
namespace UnivAux
p2m_open "WeierstrassCurve"

variable (A : Type u) [CommRing A]

abbrev R₀ : Type u := MvPolynomial (Fin 5) A

abbrev Wgen : WeierstrassCurve (R₀ A) := ⟨X 0, X 1, X 2, X 3, X 4⟩

abbrev S₀ : Type u := Localization.Away (Wgen A).Δ

abbrev W₀ : WeierstrassCurve (S₀ A) := (Wgen A).map (algebraMap (R₀ A) (S₀ A))

theorem isUnit_W₀_Δ : IsUnit (W₀ A).Δ := by
  rw [WeierstrassCurve.map_Δ]
  exact IsLocalization.Away.algebraMap_isUnit (Wgen A).Δ

scoped instance finiteType_S₀ : Algebra.FiniteType A (S₀ A) := inferInstance

variable {A}

abbrev coefHom {T : Type u} [CommRing T] [Algebra A T] (W : WeierstrassCurve T) : R₀ A →ₐ[A] T :=
  MvPolynomial.aeval ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]

theorem map_coefHom {T : Type u} [CommRing T] [Algebra A T] (W : WeierstrassCurve T) :
    (Wgen A).map (coefHom W).toRingHom = W := by
  ext <;> simp [Wgen, coefHom, WeierstrassCurve.map]

theorem isUnit_coefHom_Δ {T : Type u} [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) :
    ∀ y : Submonoid.powers (Wgen A).Δ, IsUnit (coefHom W (y : R₀ A)) := by
  rintro ⟨y, n, rfl⟩
  have h : IsUnit (coefHom W (Wgen A).Δ) := by
    have := congrArg WeierstrassCurve.Δ (map_coefHom (A := A) W)
    rw [WeierstrassCurve.map_Δ] at this
    rw [show (coefHom W) (Wgen A).Δ = (coefHom W).toRingHom (Wgen A).Δ from rfl, this]
    exact hΔ
  simpa using h.pow n

theorem exists_algHom_map_eq {T : Type u} [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) :
    ∃ ψ : S₀ A →ₐ[A] T, (W₀ A).map ψ.toRingHom = W := by
  refine ⟨IsLocalization.liftAlgHom (M := Submonoid.powers (Wgen A).Δ) (isUnit_coefHom_Δ W hΔ), ?_⟩
  rw [WeierstrassCurve.map_map]
  have hc : (IsLocalization.liftAlgHom (M := Submonoid.powers (Wgen A).Δ) (S := S₀ A)
      (isUnit_coefHom_Δ W hΔ)).toRingHom.comp (algebraMap (R₀ A) (S₀ A)) = (coefHom W).toRingHom := by
    rw [IsLocalization.liftAlgHom_toRingHom]
    exact IsLocalization.lift_comp _
  rw [hc, map_coefHom]

theorem algHom_eq_of_map_eq {T : Type u} [CommRing T] [Algebra A T] (ψ₁ ψ₂ : S₀ A →ₐ[A] T)
    (h₁₂ : (W₀ A).map ψ₁.toRingHom = (W₀ A).map ψ₂.toRingHom) : ψ₁ = ψ₂ := by

  have hgen : ∀ i : Fin 5, ψ₁ (algebraMap (R₀ A) (S₀ A) (X i)) = ψ₂ (algebraMap (R₀ A) (S₀ A) (X i)) := by
    have h1 := congrArg WeierstrassCurve.a₁ h₁₂
    have h2 := congrArg WeierstrassCurve.a₂ h₁₂
    have h3 := congrArg WeierstrassCurve.a₃ h₁₂
    have h4 := congrArg WeierstrassCurve.a₄ h₁₂
    have h6 := congrArg WeierstrassCurve.a₆ h₁₂
    simp only [WeierstrassCurve.map, W₀, Wgen] at h1 h2 h3 h4 h6
    intro i
    fin_cases i
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h6
  have hcomp : ψ₁.comp (IsScalarTower.toAlgHom A (R₀ A) (S₀ A)) = ψ₂.comp (IsScalarTower.toAlgHom A (R₀ A) (S₀ A)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa [IsScalarTower.toAlgHom_apply] using hgen i
  apply AlgHom.coe_ringHom_injective
  refine IsLocalization.ringHom_ext (Submonoid.powers (Wgen A).Δ) (RingHom.ext fun x => ?_)
  have := AlgHom.congr_fun hcomp x
  simpa [IsScalarTower.toAlgHom_apply] using this

end WeierstrassCurve.UnivAux
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_finiteType_universal_of_isUnit_discr.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_finiteType_universal_of_isUnit_discr.WeierstrassCurve.UnivAux"
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_finiteType_universal_of_isUnit_discr.WeierstrassCurve"

open WeierstrassCurve.UnivAux in
set_option maxHeartbeats 6400000 in

theorem solution (A : Type u) [CommRing A] :
    ∃ (S₀ : Type u) (_ : CommRing S₀) (_ : Algebra A S₀) (_ : Algebra.FiniteType A S₀)
      (W₀ : WeierstrassCurve S₀) (_ : IsUnit W₀.Δ),
      ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T), IsUnit W.Δ →
        ∃! ψ : S₀ →ₐ[A] T, W₀.map ψ.toRingHom = W := by
  have key : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T), IsUnit W.Δ →
      ∃! ψ : S₀ A →ₐ[A] T, (W₀ A).map ψ.toRingHom = W := by
    intro T _ _ W hΔ
    obtain ⟨ψ, hψ⟩ := exists_algHom_map_eq (A := A) W hΔ
    exact ⟨ψ, hψ, fun ψ' hψ' => algHom_eq_of_map_eq (A := A) ψ' ψ (hψ'.trans hψ.symm)⟩
  exact ⟨S₀ A, _, _, finiteType_S₀ A, W₀ A, isUnit_W₀_Δ A, key⟩

end
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_finiteType_universal_of_isUnit_discr.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_finiteType_universal_of_isUnit_discr.WeierstrassCurve.UnivAux"

end S_WeierstrassCurve_exists_finiteType_universal_of_isUnit_discr
end P2MW
export P2MW.S_WeierstrassCurve_exists_finiteType_universal_of_isUnit_discr (solution)
