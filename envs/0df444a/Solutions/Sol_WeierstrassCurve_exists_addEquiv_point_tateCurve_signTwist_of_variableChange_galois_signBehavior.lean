-- Prove2me | solution 1 for WeierstrassCurve.exists_addEquiv_point_tateCurve_signTwist_of_variableChange_galois_signBehavior
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/f78fb997-7647-5c4d-bb63-67a87cd3cf90

import Mathlib
import Definitions.Def_TateCurve_TateParameter
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_addEquiv_point_tateCurve_signTwist_of_variableChange_galois_signBehavior

open scoped NNReal WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

set_option maxHeartbeats 2400000

namespace C1b1Helper

variable {K : Type*} [Field K] [DecidableEq K]

private noncomputable def ψAE (C : VariableChange K) (W₁ E₂ : WeierstrassCurve.Affine K)
    (hC : C • W₁ = E₂) : W₁.Point ≃+ E₂.Point :=
  ((AddEquiv.mk' (variableChangeEquiv C W₁).symm
    (fun P Q => WeierstrassCurve.Affine.Point.vcInvFun_add C W₁ P Q)).trans
    (show (C • W₁).toAffine.Point ≃+ E₂.Point from hC ▸ AddEquiv.refl _))

private lemma ψAE_some (C : VariableChange K) (W₁ E₂ : Affine K) (hC : C • W₁ = E₂)
    {x y : K} (h : W₁.Nonsingular x y) (h' : E₂.Nonsingular (vcXInv C x) (vcYInv C x y)) :
    ψAE C W₁ E₂ hC (.some x y h) = .some (vcXInv C x) (vcYInv C x y) h' := by
  subst hC; rfl

private lemma ns_vcInv (C : VariableChange K) (W₁ E₂ : Affine K) (hC : C • W₁ = E₂)
    {x y : K} (h : W₁.Nonsingular x y) :
    E₂.Nonsingular (vcXInv C x) (vcYInv C x y) := by
  subst hC
  exact (nonsingular_variableChange_iff (vcXInv C x) (vcYInv C x y)).mpr
    (by rwa [vcX_vcXInv, vcY_vcYInv])

private lemma some_ext {V : Affine K} {x₁ y₁ x₂ y₂ : K}
    (hx : x₁ = x₂) (hy : y₁ = y₂) {h₁ : V.Nonsingular x₁ y₁} {h₂ : V.Nonsingular x₂ y₂} :
    (Point.some x₁ y₁ h₁ : V.Point) = .some x₂ y₂ h₂ := by
  subst hx hy; rfl

end C1b1Helper

open C1b1Helper

theorem solution
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] [DecidableEq (AlgebraicClosure ℚ_[p])]
    (qT : ℚ_[p])
    (s : AlgebraicClosure ℚ_[p])
    (C : VariableChange (AlgebraicClosure ℚ_[p]))
    (hC : C • ((W.map (Int.castRingHom ℚ_[p])).map (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])))
          = (TateCurve.curve qT).map (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])))
    (hCσ : ∀ σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p],
        (σ s = s → C.map σ.toAlgHom.toRingHom = C) ∧
        (σ s ≠ s → C.map σ.toAlgHom.toRingHom
          = (⟨-1, 0, -1, 0⟩ : VariableChange (AlgebraicClosure ℚ_[p])) * C)) :
    ∃ ψ : ((W.map (Int.castRingHom ℚ_[p]))⁄(AlgebraicClosure ℚ_[p])).Point
          ≃+ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point,
      ∀ σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p],
        (σ s = s → ∀ P, ψ (σ • P) = σ • ψ P) ∧
        (σ s ≠ s → ∀ P, ψ (σ • P) = -(σ • ψ P)) := by

  change C • ((W.map (Int.castRingHom ℚ_[p]))⁄(AlgebraicClosure ℚ_[p]))
    = ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])) at hC
  refine ⟨ψAE C ((W.map (Int.castRingHom ℚ_[p]))⁄(AlgebraicClosure ℚ_[p]))
    ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])) hC, ?_⟩
  intro σ
  set φ : AlgebraicClosure ℚ_[p] →+* AlgebraicClosure ℚ_[p] := σ.toAlgHom.toRingHom with hφdef
  have map_vcXInv : ∀ x : AlgebraicClosure ℚ_[p],
      φ (vcXInv C x) = (φ (↑(C.u⁻¹) : _)) ^ 2 * (φ x - φ C.r) := fun x => by
    simp only [vcXInv, map_mul, map_pow, map_sub]
  have map_vcYInv : ∀ x y : AlgebraicClosure ℚ_[p],
      φ (vcYInv C x y)
        = (φ (↑(C.u⁻¹) : _)) ^ 3 * (φ y - φ C.t - φ C.s * (φ x - φ C.r)) := fun x y => by
    simp only [vcYInv, map_mul, map_pow, map_sub]
  have hCφu : φ (↑C.u : _) = ↑((C.map φ).u : _) := by
    simp only [VariableChange.map_u, Units.coe_map, MonoidHom.coe_coe]
  have hCφr : φ C.r = (C.map φ).r := rfl
  have hCφs : φ C.s = (C.map φ).s := rfl
  have hCφt : φ C.t = (C.map φ).t := rfl
  have hCφuinv : φ (↑(C.u⁻¹) : _) = (φ (↑C.u : _))⁻¹ := by
    rw [Units.val_inv_eq_inv_val, map_inv₀]
  have hσφ : (σ.toAlgHom : AlgebraicClosure ℚ_[p] → AlgebraicClosure ℚ_[p]) = φ := rfl
  refine ⟨fun hσs P => ?_, fun hσs P => ?_⟩
  ·
    have hσC : C.map φ = C := (hCσ σ).1 hσs
    have hfu : φ (↑C.u : _) = ↑C.u := by rw [hCφu, hσC]
    have hfr : φ C.r = C.r := by rw [hCφr, hσC]
    have hfs : φ C.s = C.s := by rw [hCφs, hσC]
    have hft : φ C.t = C.t := by rw [hCφt, hσC]
    have hfuinv : φ (↑(C.u⁻¹) : _) = ↑(C.u⁻¹) := by
      rw [hCφuinv, hfu, ← Units.val_inv_eq_inv_val]
    rcases P with _ | ⟨x, y, h⟩
    · show ψAE C _ _ hC (σ • (0 : _)) = σ • ψAE C _ _ hC (0 : _)
      rw [smul_zero, _root_.map_zero, smul_zero]
    ·
      have hσh : ((W.map (Int.castRingHom ℚ_[p]))⁄(AlgebraicClosure ℚ_[p])).Nonsingular
          (σ.toAlgHom x) (σ.toAlgHom y) :=
        (baseChange_nonsingular (W.map (Int.castRingHom ℚ_[p])) σ.toAlgHom.injective x y).mpr h
      rw [algEquiv_smul_def, Point.map_some σ.toAlgHom h,
        ψAE_some C _ _ hC hσh (ns_vcInv C _ _ hC hσh),
        ψAE_some C _ _ hC h (ns_vcInv C _ _ hC h),
        algEquiv_smul_def, Point.map_some σ.toAlgHom (ns_vcInv C _ _ hC h)]
      refine some_ext ?_ ?_
      · show vcXInv C (σ.toAlgHom x) = σ.toAlgHom (vcXInv C x)
        rw [hσφ, map_vcXInv, hfuinv, hfr]; rfl
      · show vcYInv C (σ.toAlgHom x) (σ.toAlgHom y) = σ.toAlgHom (vcYInv C x y)
        rw [hσφ, map_vcYInv, hfuinv, hfr, hfs, hft]; rfl
  ·
    have hσC : C.map φ
        = (⟨-1, 0, -1, 0⟩ : VariableChange (AlgebraicClosure ℚ_[p])) * C := (hCσ σ).2 hσs
    have hfu : φ (↑C.u : _) = -↑C.u := by
      rw [hCφu, hσC]
      show (↑((-1 : (AlgebraicClosure ℚ_[p])ˣ) * C.u) : AlgebraicClosure ℚ_[p]) = -↑C.u
      rw [Units.val_mul, Units.val_neg, Units.val_one, neg_one_mul]
    have hfr : φ C.r = C.r := by
      rw [hCφr, hσC]; simp only [VariableChange.mul_def]; ring
    have hfs : φ C.s = -(↑C.u : _) + C.s := by
      rw [hCφs, hσC]; simp only [VariableChange.mul_def]; ring
    have hft : φ C.t = C.t := by
      rw [hCφt, hσC]; simp only [VariableChange.mul_def]; ring
    have hfuinv : φ (↑(C.u⁻¹) : _) = -(↑(C.u⁻¹) : _) := by
      rw [hCφuinv, hfu, Units.val_inv_eq_inv_val, neg_inv]
    have hu_ne : (↑C.u : AlgebraicClosure ℚ_[p]) ≠ 0 := C.u.ne_zero
    have hE₂a₁ : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).a₁ = 1 := by
      show algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) (TateCurve.curve qT).a₁ = 1
      rw [TateCurve.curve_a₁]; exact _root_.map_one _
    have hE₂a₃ : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).a₃ = 0 := by
      show algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) (TateCurve.curve qT).a₃ = 0
      rw [TateCurve.curve_a₃]; exact _root_.map_zero _
    rcases P with _ | ⟨x, y, h⟩
    · show ψAE C _ _ hC (σ • (0 : _)) = -(σ • ψAE C _ _ hC (0 : _))
      rw [smul_zero, _root_.map_zero, smul_zero, _root_.neg_zero]
    · have hσh : ((W.map (Int.castRingHom ℚ_[p]))⁄(AlgebraicClosure ℚ_[p])).Nonsingular
          (σ.toAlgHom x) (σ.toAlgHom y) :=
        (baseChange_nonsingular (W.map (Int.castRingHom ℚ_[p])) σ.toAlgHom.injective x y).mpr h
      rw [algEquiv_smul_def, Point.map_some σ.toAlgHom h,
        ψAE_some C _ _ hC hσh (ns_vcInv C _ _ hC hσh),
        ψAE_some C _ _ hC h (ns_vcInv C _ _ hC h),
        algEquiv_smul_def, Point.map_some σ.toAlgHom (ns_vcInv C _ _ hC h),
        neg_some]
      refine some_ext ?_ ?_
      · show vcXInv C (σ.toAlgHom x) = σ.toAlgHom (vcXInv C x)
        rw [hσφ, map_vcXInv, hfuinv, hfr, neg_sq]; rfl
      · show vcYInv C (σ.toAlgHom x) (σ.toAlgHom y)
          = ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).negY
              (σ.toAlgHom (vcXInv C x)) (σ.toAlgHom (vcYInv C x y))
        rw [hσφ, negY, hE₂a₁, hE₂a₃, one_mul, sub_zero,
          map_vcXInv, map_vcYInv, hfuinv, hfr, hfs, hft]
        simp only [vcXInv, vcYInv, Units.val_inv_eq_inv_val]
        field_simp
        ring

end S_WeierstrassCurve_exists_addEquiv_point_tateCurve_signTwist_of_variableChange_galois_signBehavior
end P2MW
export P2MW.S_WeierstrassCurve_exists_addEquiv_point_tateCurve_signTwist_of_variableChange_galois_signBehavior (solution)
