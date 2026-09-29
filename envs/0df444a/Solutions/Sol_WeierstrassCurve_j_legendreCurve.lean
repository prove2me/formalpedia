-- Prove2me | solution 1 for WeierstrassCurve.j_legendreCurve
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/afeda7b6-af9e-5848-9495-ea3a0c55df80

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_ModularCurve_LegendreJ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_j_legendreCurve

set_option autoImplicit false

open Polynomial

noncomputable section

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "isUnit_Δ a₃ a₁ b₂ twoTorsionPolynomial coe_Δ' a₄ a₂ a₆ b₆ b₈ Δ c₄ j b₄ legendreCurve"
p2m_open "WeierstrassCurve"

section invariants

variable {R : Type*} [CommRing R] (t : R)

@[scoped simp] lemma legendreCurve_a₁ : (legendreCurve t).a₁ = 0 := rfl
@[scoped simp] lemma legendreCurve_a₂ : (legendreCurve t).a₂ = -(1 + t) := rfl
@[scoped simp] lemma legendreCurve_a₃ : (legendreCurve t).a₃ = 0 := rfl
@[scoped simp] lemma legendreCurve_a₄ : (legendreCurve t).a₄ = t := rfl
@[scoped simp] lemma legendreCurve_a₆ : (legendreCurve t).a₆ = 0 := rfl

@[scoped simp] lemma legendreCurve_b₂ : (legendreCurve t).b₂ = -4 * (1 + t) := by
  simp [b₂]; ring
@[scoped simp] lemma legendreCurve_b₄ : (legendreCurve t).b₄ = 2 * t := by
  simp [b₄]
@[scoped simp] lemma legendreCurve_b₆ : (legendreCurve t).b₆ = 0 := by
  simp [b₆]
@[scoped simp] lemma legendreCurve_b₈ : (legendreCurve t).b₈ = -t ^ 2 := by
  simp [b₈]
@[scoped simp] lemma legendreCurve_c₄ : (legendreCurve t).c₄ = 16 * (t ^ 2 - t + 1) := by
  simp [c₄]; ring
@[scoped simp] lemma legendreCurve_Δ : (legendreCurve t).Δ = 16 * t ^ 2 * (t - 1) ^ 2 := by
  simp [Δ]; ring

theorem twoTorsionPolynomial_legendreCurve_toPoly :
    (legendreCurve t).twoTorsionPolynomial.toPoly = C 4 * X * ((X - C 1) * (X - C t)) := by
  simp only [twoTorsionPolynomial, Cubic.toPoly, legendreCurve_b₂, legendreCurve_b₄, legendreCurve_b₆,
    map_neg, map_mul, map_add, map_one, map_zero, map_ofNat]
  ring

end invariants

theorem isElliptic_legendreCurve_iff {K : Type*} [Field K] (t : K) (h2 : (2 : K) ≠ 0) :
    (legendreCurve t).IsElliptic ↔ t ≠ 0 ∧ t ≠ 1 := by
  have h16 : (16 : K) ≠ 0 := by
    have : (16 : K) = 2 ^ 4 := by norm_num
    rw [this]; exact pow_ne_zero _ h2
  constructor
  · intro h
    have hΔ := (legendreCurve t).isUnit_Δ.ne_zero
    rw [legendreCurve_Δ] at hΔ
    refine ⟨?_, ?_⟩
    · rintro rfl; simp at hΔ
    · rintro rfl; simp at hΔ
  · rintro ⟨h0, h1⟩
    refine ⟨?_⟩
    rw [legendreCurve_Δ, isUnit_iff_ne_zero]
    exact mul_ne_zero (mul_ne_zero h16 (pow_ne_zero _ h0)) (pow_ne_zero _ (sub_ne_zero.mpr h1))

theorem isElliptic_legendreCurve {K : Type*} [Field K] (t : K) (h2 : (2 : K) ≠ 0) (h0 : t ≠ 0)
    (h1 : t ≠ 1) : (legendreCurve t).IsElliptic :=
  (isElliptic_legendreCurve_iff t h2).mpr ⟨h0, h1⟩

theorem j_legendreCurve' {K : Type*} [Field K] (t : K) [(legendreCurve t).IsElliptic] :
    (legendreCurve t).j = ModularCurve.legendreJ t := by
  have hΔ := (legendreCurve t).isUnit_Δ.ne_zero
  rw [legendreCurve_Δ] at hΔ
  have h16 : (16 : K) ≠ 0 := fun h => hΔ (by simp [h])
  have h0 : t ≠ 0 := fun h => hΔ (by simp [h])
  have h1 : t - 1 ≠ 0 := fun h => hΔ (by simp [h])
  rw [j, Units.val_inv_eq_inv_val, coe_Δ', legendreCurve_Δ, legendreCurve_c₄, ModularCurve.legendreJ]
  field_simp
  ring

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_j_legendreCurve.WeierstrassCurve"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_j_legendreCurve.WeierstrassCurve"

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_j_legendreCurve.WeierstrassCurve"

theorem solution {K : Type*} [Field K] (t : K) [(legendreCurve t).IsElliptic] :
    (legendreCurve t).j = ModularCurve.legendreJ t :=
  WeierstrassCurve.j_legendreCurve' t

end S_WeierstrassCurve_j_legendreCurve
end P2MW
export P2MW.S_WeierstrassCurve_j_legendreCurve (solution)
