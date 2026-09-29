-- Prove2me | solution 1 for WeierstrassCurve.VariableChange.exists_addEquiv_affine_point_baseChange_gal_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/e534d9ec-f031-5933-aa29-b5e19c64052b

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_VariableChange_exists_addEquiv_affine_point_baseChange_gal_equiv

set_option maxHeartbeats 12800000
open scoped WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution
    (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K)
    (C : WeierstrassCurve.VariableChange K) :
    letI : DecidableEq (AlgebraicClosure K) := Classical.decEq _
    ∃ e : ((C • W)⁄(AlgebraicClosure K)).Point ≃+ (W⁄(AlgebraicClosure K)).Point,
      ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) P,
        e (σ • P) = σ • (e P) := by
  letI : DecidableEq (AlgebraicClosure K) := Classical.decEq _
  let φ := algebraMap K (AlgebraicClosure K)
  let Cbar : VariableChange (AlgebraicClosure K) := C.map φ
  have hEq : (Cbar • (W⁄(AlgebraicClosure K))).toAffine = ((C • W)⁄(AlgebraicClosure K)) :=
    map_variableChange W C φ
  have hσu : ∀ σ : (AlgebraicClosure K) ≃ₐ[K] (AlgebraicClosure K),
      σ ((Cbar.u : AlgebraicClosure K)) = (Cbar.u : AlgebraicClosure K) := by
    intro σ
    simp only [Cbar, VariableChange.map_u, Units.coe_map, MonoidHom.coe_coe]
    exact σ.commutes _
  have hσr : ∀ σ : (AlgebraicClosure K) ≃ₐ[K] (AlgebraicClosure K), σ Cbar.r = Cbar.r := by
    intro σ; simp only [Cbar, VariableChange.map_r]; exact σ.commutes _
  have hσs : ∀ σ : (AlgebraicClosure K) ≃ₐ[K] (AlgebraicClosure K), σ Cbar.s = Cbar.s := by
    intro σ; simp only [Cbar, VariableChange.map_s]; exact σ.commutes _
  have hσt : ∀ σ : (AlgebraicClosure K) ≃ₐ[K] (AlgebraicClosure K), σ Cbar.t = Cbar.t := by
    intro σ; simp only [Cbar, VariableChange.map_t]; exact σ.commutes _
  have hvcX : ∀ (σ : (AlgebraicClosure K) ≃ₐ[K] (AlgebraicClosure K)) (x : AlgebraicClosure K),
      σ (vcX Cbar x) = vcX Cbar (σ x) := by
    intro σ x
    simp only [vcX, map_add, map_mul, map_pow, hσu σ, hσr σ]
  have hvcY : ∀ (σ : (AlgebraicClosure K) ≃ₐ[K] (AlgebraicClosure K)) (x y : AlgebraicClosure K),
      σ (vcY Cbar x y) = vcY Cbar (σ x) (σ y) := by
    intro σ x y
    simp only [vcY, map_add, map_mul, map_pow, hσu σ, hσs σ, hσt σ]
  have hNS : ∀ x y, (Cbar • (W⁄(AlgebraicClosure K))).toAffine.Nonsingular x y →
      (W⁄(AlgebraicClosure K)).Nonsingular (vcX Cbar x) (vcY Cbar x y) :=
    fun x y h => (nonsingular_variableChange_iff x y).mp h
  obtain ⟨e₀, he₀_some⟩ :
      ∃ e₀ : (Cbar • (W⁄(AlgebraicClosure K))).toAffine.Point ≃+ (W⁄(AlgebraicClosure K)).Point,
        ∀ x y h, e₀ (.some x y h) = .some (vcX Cbar x) (vcY Cbar x y) (hNS x y h) :=
    ⟨(AddEquiv.mk' (variableChangeEquiv Cbar (W⁄(AlgebraicClosure K))).symm
      (fun P Q => vcInvFun_add Cbar (W⁄(AlgebraicClosure K)) P Q)).symm, fun x y h => rfl⟩
  clear hσu hσr hσs hσt
  clear_value Cbar
  revert hNS e₀ he₀_some
  generalize hZ : (Cbar • (W⁄(AlgebraicClosure K))).toAffine = Z at hEq
  subst hEq
  intro hNS e₀ he₀_some
  refine ⟨e₀, ?_⟩
  intro σ P
  rcases P with _ | ⟨x, y, h⟩
  · show e₀ (Point.map (↑σ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K) 0)
      = Point.map (↑σ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K) (e₀ 0)
    simp only [_root_.map_zero]
  · rw [show σ • (.some x y h : ((C • W)⁄(AlgebraicClosure K)).Point)
          = Point.map (↑σ : (AlgebraicClosure K) →ₐ[K] (AlgebraicClosure K)) (.some x y h)
          from rfl,
        map_some (f := (↑σ : (AlgebraicClosure K) →ₐ[K] (AlgebraicClosure K))) h,
        he₀_some, he₀_some,
        show σ • (.some (vcX Cbar x) (vcY Cbar x y) (hNS x y h) : (W⁄(AlgebraicClosure K)).Point)
          = Point.map (↑σ : (AlgebraicClosure K) →ₐ[K] (AlgebraicClosure K))
              (.some (vcX Cbar x) (vcY Cbar x y) (hNS x y h)) from rfl,
        map_some (f := (↑σ : (AlgebraicClosure K) →ₐ[K] (AlgebraicClosure K))) (hNS x y h),
        Point.some.injEq]
    exact ⟨(hvcX σ x).symm, (hvcY σ x y).symm⟩

end S_WeierstrassCurve_VariableChange_exists_addEquiv_affine_point_baseChange_gal_equiv
end P2MW
export P2MW.S_WeierstrassCurve_VariableChange_exists_addEquiv_affine_point_baseChange_gal_equiv (solution)
