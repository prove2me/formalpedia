-- Prove2me | solution 1 for WeierstrassCurve.Affine.Point.exists_linearEquiv_torsionBy_of_addEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/1cebcb23-b9d4-5a6a-9954-6bd46973aa8f

import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_Point_exists_linearEquiv_torsionBy_of_addEquiv

set_option autoImplicit false

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_Point_exists_linearEquiv_torsionBy_of_addEquiv.WeierstrassCurve WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_Point_exists_linearEquiv_torsionBy_of_addEquiv.WeierstrassCurve.Affine WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_Affine_Point_exists_linearEquiv_torsionBy_of_addEquiv.WeierstrassCurve.Affine.Point"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.Point"
p2m_open "WeierstrassCurve"

section Torsion

variable {F : Type*} {K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
  {E₁ E₂ : WeierstrassCurve F}

namespace Affine
p2m_export "WeierstrassCurve.Affine" "Point"
namespace Point
p2m_export "WeierstrassCurve.Affine.Point" "map_zero"
p2m_open "WeierstrassCurve.Affine.Point WeierstrassCurve.Affine"

noncomputable def torsionByMap (e : (E₁⁄K).Point →+ (E₂⁄K).Point) (n : ℕ) :
    Submodule.torsionBy ℤ (E₁⁄K).Point n →+ Submodule.torsionBy ℤ (E₂⁄K).Point n where
  toFun x := ⟨e x, by
    rw [Submodule.mem_torsionBy_iff, ← e.map_zsmul, (Submodule.mem_torsionBy_iff _ _).mp x.2,
      e.map_zero]⟩
  map_zero' := Subtype.ext e.map_zero
  map_add' x y := Subtype.ext (e.map_add x y)

@[scoped simp] lemma coe_torsionByMap (e : (E₁⁄K).Point →+ (E₂⁄K).Point) (n : ℕ)
    (x : Submodule.torsionBy ℤ (E₁⁄K).Point n) : (torsionByMap e n x : (E₂⁄K).Point) = e x := rfl

noncomputable def torsionByEquiv (e : (E₁⁄K).Point ≃+ (E₂⁄K).Point) (n : ℕ) :
    Submodule.torsionBy ℤ (E₁⁄K).Point n ≃ₗ[ZMod n] Submodule.torsionBy ℤ (E₂⁄K).Point n :=
  { (torsionByMap e.toAddMonoidHom n).toZModLinearMap n with
    invFun := torsionByMap e.symm.toAddMonoidHom n
    left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
    right_inv := fun y => Subtype.ext (e.apply_symm_apply y) }

@[scoped simp] lemma coe_torsionByEquiv (e : (E₁⁄K).Point ≃+ (E₂⁄K).Point) (n : ℕ)
    (x : Submodule.torsionBy ℤ (E₁⁄K).Point n) : (torsionByEquiv e n x : (E₂⁄K).Point) = e x := rfl

lemma torsionByEquiv_smul (e : (E₁⁄K).Point ≃+ (E₂⁄K).Point)
    (he : ∀ (σ : K ≃ₐ[F] K) (P : (E₁⁄K).Point), e (σ • P) = σ • e P) (n : ℕ)
    (σ : K ≃ₐ[F] K) (x : Submodule.torsionBy ℤ (E₁⁄K).Point n) :
    torsionByEquiv e n (σ • x) = σ • torsionByEquiv e n x :=
  Subtype.ext (he σ x)

theorem exists_linearEquiv_torsionBy_of_addEquiv_dev (e : (E₁⁄K).Point ≃+ (E₂⁄K).Point)
    (he : ∀ (σ : K ≃ₐ[F] K) (P : (E₁⁄K).Point), e (σ • P) = σ • e P) (n : ℕ) :
    ∃ φ : Submodule.torsionBy ℤ (E₁⁄K).Point n ≃ₗ[ZMod n] Submodule.torsionBy ℤ (E₂⁄K).Point n,
      (∀ x : Submodule.torsionBy ℤ (E₁⁄K).Point n, (φ x : (E₂⁄K).Point) = e x) ∧
      ∀ (σ : K ≃ₐ[F] K) (x : Submodule.torsionBy ℤ (E₁⁄K).Point n), φ (σ • x) = σ • φ x :=
  ⟨torsionByEquiv e n, coe_torsionByEquiv e n, torsionByEquiv_smul e he n⟩

end Affine.Point
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_Point_exists_linearEquiv_torsionBy_of_addEquiv.WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_Point_exists_linearEquiv_torsionBy_of_addEquiv.WeierstrassCurve.Affine.Point"
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_Point_exists_linearEquiv_torsionBy_of_addEquiv.WeierstrassCurve.Affine"

end Torsion
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_Point_exists_linearEquiv_torsionBy_of_addEquiv.WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_Point_exists_linearEquiv_torsionBy_of_addEquiv.WeierstrassCurve.Affine.Point"

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_Point_exists_linearEquiv_torsionBy_of_addEquiv.WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_Point_exists_linearEquiv_torsionBy_of_addEquiv.WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_Affine_Point_exists_linearEquiv_torsionBy_of_addEquiv.WeierstrassCurve"

theorem solution {F : Type*} [Field F] {K : Type*} [Field K] [Algebra F K] [DecidableEq K] {E₁ E₂ : WeierstrassCurve F} (e : (E₁⁄K).Point ≃+ (E₂⁄K).Point) (he : ∀ (σ : K ≃ₐ[F] K) (P : (E₁⁄K).Point), e (σ • P) = σ • e P) (n : ℕ) : ∃ φ : Submodule.torsionBy ℤ (E₁⁄K).Point n ≃ₗ[ZMod n] Submodule.torsionBy ℤ (E₂⁄K).Point n, (∀ x : Submodule.torsionBy ℤ (E₁⁄K).Point n, (φ x : (E₂⁄K).Point) = e x) ∧ ∀ (σ : K ≃ₐ[F] K) (x : Submodule.torsionBy ℤ (E₁⁄K).Point n), φ (σ • x) = σ • φ x :=
  ⟨WeierstrassCurve.Affine.Point.torsionByEquiv e n, WeierstrassCurve.Affine.Point.coe_torsionByEquiv e n,
    WeierstrassCurve.Affine.Point.torsionByEquiv_smul e he n⟩

end S_WeierstrassCurve_Affine_Point_exists_linearEquiv_torsionBy_of_addEquiv
end P2MW
export P2MW.S_WeierstrassCurve_Affine_Point_exists_linearEquiv_torsionBy_of_addEquiv (solution)
