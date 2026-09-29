-- Prove2me | solution 1 for WeierstrassCurve.IsTwoKernel.exists_moduleFinite_represents
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/11c7919b-95ae-5cf4-8bf6-9cc83657a4c2

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassGamma0Sqf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_IsTwoKernel_exists_moduleFinite_represents

set_option autoImplicit false

universe u

open Polynomial

theorem solution
    {B : Type u} [CommRing B] (W : WeierstrassCurve B) (h2 : IsUnit ((2 : ℕ) : B)) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra B C) (_ : Module.Finite B C) (hᵤ : Polynomial C)
      (_ : (W.map (algebraMap B C)).IsTwoKernel hᵤ),
      ∀ (T : Type u) [CommRing T] (φ : B →+* T) (h : Polynomial T),
        (W.map φ).IsTwoKernel h ↔
          ∃! ψ : C →+* T, ψ.comp (algebraMap B C) = φ ∧ hᵤ.map ψ = h := by
  classical

  have h4 : IsUnit ((4 : B)) := by
    have h22 := h2.mul h2
    have : ((2 : ℕ) : B) * ((2 : ℕ) : B) = 4 := by norm_num
    rwa [this] at h22
  obtain ⟨w, hw⟩ : ∃ w : B, w * 4 = 1 := h4.exists_left_inv
  have hwC : C w * C (4 : B) = 1 := by rw [← C_mul, hw, C_1]
  let p₂ : B[X] := C w * C W.b₂ * X ^ 2 + C w * C (2 * W.b₄) * X + C w * C W.b₆
  let F : B[X] := X ^ 3 + p₂
  have hFdef : C w * W.Ψ₂Sq = F := by
    simp only [F, p₂, WeierstrassCurve.Ψ₂Sq]
    linear_combination (X ^ 3 : B[X]) * hwC
  have hΨF : W.Ψ₂Sq = C (4 : B) * F := by
    rw [← hFdef, ← mul_assoc, mul_comm (C (4:B)), hwC, one_mul]
  have hp₂ : p₂.degree < 3 := by
    have : p₂.degree ≤ 2 := by
      simp only [p₂]
      rw [show C w * C W.b₂ * X ^ 2 + C w * C (2 * W.b₄) * X + C w * C W.b₆ =
          C (w * W.b₂) * X ^ 2 + C (w * (2 * W.b₄)) * X + C (w * W.b₆) by simp only [C_mul]]
      exact degree_quadratic_le
    exact lt_of_le_of_lt this (by exact_mod_cast (show (2 : ℕ) < 3 by norm_num))
  have hFm : F.Monic := monic_X_pow_add hp₂

  refine ⟨AdjoinRoot F, inferInstance, inferInstance, hFm.finite_adjoinRoot, X - C (AdjoinRoot.root F), ?_, ?_⟩
  ·
    refine ⟨natDegree_X_sub_C_le _, by simp [coeff_X, coeff_C], ?_⟩
    rw [WeierstrassCurve.map_Ψ₂Sq, dvd_iff_isRoot, hΨF, Polynomial.map_mul, map_C, IsRoot, eval_mul,
      AdjoinRoot.algebraMap_eq, (AdjoinRoot.isRoot_root F), mul_zero]
  ·
    intro T _ φ h
    constructor
    · intro hh

      have hh1 := hh.natDegree_le
      have hh2 := hh.coeff_eq_one
      set r : T := - h.coeff 0 with hr
      have hhr : h = X - C r := by
        rw [eq_X_add_C_of_natDegree_le_one hh1, hh2, C_1, one_mul, hr, C_neg, sub_neg_eq_add]

      have hroot : F.eval₂ φ r = 0 := by
        have hd := hh.dvd_Ψ₂Sq
        rw [WeierstrassCurve.map_Ψ₂Sq, hhr, dvd_iff_isRoot, IsRoot] at hd
        rw [eval₂_eq_eval_map]
        have : F.map φ = C (φ w) * (W.Ψ₂Sq.map φ) := by rw [← hFdef, Polynomial.map_mul, map_C]
        rw [this, eval_mul, hd, mul_zero]
      refine ⟨AdjoinRoot.lift φ r hroot, ⟨?_, ?_⟩, ?_⟩
      · ext b
        simp [AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of]
      · rw [Polynomial.map_sub, map_X, map_C, AdjoinRoot.lift_root, hhr]
      · rintro ψ ⟨hψc, hψh⟩
        have hψr : ψ (AdjoinRoot.root F) = r := by
          rw [Polynomial.map_sub, map_X, map_C, hhr, sub_right_inj, C_inj] at hψh
          exact hψh
        letI : Algebra B T := φ.toAlgebra
        let g₁ : AdjoinRoot F →ₐ[B] T :=
          { toRingHom := ψ, commutes' := fun b => by
              show ψ (algebraMap B (AdjoinRoot F) b) = φ b
              rw [← RingHom.comp_apply, hψc] }
        let g₂ : AdjoinRoot F →ₐ[B] T :=
          { toRingHom := AdjoinRoot.lift φ r hroot, commutes' := fun b => by
              show AdjoinRoot.lift φ r hroot (algebraMap B (AdjoinRoot F) b) = φ b
              rw [AdjoinRoot.algebraMap_eq]; exact AdjoinRoot.lift_of hroot }
        have : g₁ = g₂ := AdjoinRoot.algHom_ext (by
          show ψ (AdjoinRoot.root F) = AdjoinRoot.lift φ r hroot (AdjoinRoot.root F)
          rw [hψr, AdjoinRoot.lift_root])
        exact congrArg AlgHom.toRingHom this
    · rintro ⟨ψ, ⟨hψc, hψh⟩, -⟩
      rw [← hψc, ← hψh, ← WeierstrassCurve.map_map]
      refine WeierstrassCurve.IsTwoKernel.map _ ψ ⟨natDegree_X_sub_C_le _, by simp [coeff_X, coeff_C], ?_⟩
      rw [WeierstrassCurve.map_Ψ₂Sq, dvd_iff_isRoot, hΨF, Polynomial.map_mul, map_C, IsRoot, eval_mul,
        AdjoinRoot.algebraMap_eq, (AdjoinRoot.isRoot_root F), mul_zero]

end S_WeierstrassCurve_IsTwoKernel_exists_moduleFinite_represents
end P2MW
export P2MW.S_WeierstrassCurve_IsTwoKernel_exists_moduleFinite_represents (solution)
