-- Prove2me | solution 1 for WeierstrassCurve.Affine.Point.smul_eq_self_of_mem_inertiaSubgroupIn_of_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/eb316c66-5b09-5d6d-a219-0ea86c2bd706

import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_Point_smul_eq_self_of_mem_inertiaSubgroupIn_of_level

open scoped Pointwise
open WeierstrassCurve WeierstrassCurve.Affine

namespace M3dS12

theorem sub_mem_nonunits_of_mem_inertiaSubgroupIn (A : ValuationSubring (AlgebraicClosure ℚ))
    {σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    {a : AlgebraicClosure ℚ} (ha : a ∈ A) : σ a - a ∈ A.nonunits := by
  classical
  obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.mp hσ
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at hτ
  have h := RingEquiv.congr_fun hτ (IsLocalRing.residue A ⟨a, ha⟩)
  rw [RingAut.one_apply, MulSemiringAction.toRingAut_apply, MulSemiringAction.toRingEquiv_apply,
    ← IsLocalRing.ResidueField.residue_smul, IsLocalRing.residue_def, IsLocalRing.residue_def] at h
  have h2 := Ideal.Quotient.eq.mp h
  rw [← ValuationSubring.coe_mem_nonunits_iff] at h2
  exact h2

theorem smul_eq_of_mem_inertiaSubgroupIn (A : ValuationSubring (AlgebraicClosure ℚ))
    {σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) :
    σ • A = A := by
  obtain ⟨τ, -, rfl⟩ := Subgroup.mem_map.mp hσ
  exact MulAction.mem_stabilizer_iff.mp τ.2

section stabilizer

variable (A : ValuationSubring (AlgebraicClosure ℚ))
  {σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)} (hstab : σ • A = A)
include hstab

theorem mem_iff_apply_mem (z : AlgebraicClosure ℚ) : z ∈ A ↔ σ z ∈ A := by
  rw [← ValuationSubring.smul_mem_pointwise_smul_iff (g := σ) (S := A), hstab, AlgEquiv.smul_def]

theorem mem_iff_symm_apply_mem (z : AlgebraicClosure ℚ) : z ∈ A ↔ σ⁻¹ z ∈ A := by
  conv_lhs => rw [← hstab]
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]

theorem valuation_apply_eq_one {z : AlgebraicClosure ℚ} (hz : A.valuation z = 1) :
    A.valuation (σ z) = 1 := by
  have hz0 : z ≠ 0 := fun h => by rw [h, map_zero] at hz; exact zero_ne_one hz
  have hzA : z ∈ A := (A.valuation_le_one_iff z).mp hz.le
  have hziA : z⁻¹ ∈ A := (A.valuation_le_one_iff _).mp (by rw [map_inv₀, hz, inv_one])
  have h1 : A.valuation (σ z) ≤ 1 := (A.valuation_le_one_iff _).mpr ((mem_iff_apply_mem A hstab z).mp hzA)
  have h2 : A.valuation (σ z)⁻¹ ≤ 1 := by
    rw [← map_inv₀]
    exact (A.valuation_le_one_iff _).mpr ((mem_iff_apply_mem A hstab _).mp hziA)
  have hσz0 : A.valuation (σ z) ≠ 0 := (Valuation.ne_zero_iff _).mpr (by simpa using hz0)
  rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr hσz0)] at h2
  exact le_antisymm h1 h2

theorem valuation_apply_lt_one {z : AlgebraicClosure ℚ} (hzA : z ∈ A) (hz : A.valuation z < 1) :
    A.valuation (σ z) < 1 := by
  have h1 : A.valuation (σ z) ≤ 1 := (A.valuation_le_one_iff _).mpr ((mem_iff_apply_mem A hstab z).mp hzA)
  refine lt_of_le_of_ne h1 fun heq => ?_

  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero] at heq; exact zero_ne_one heq
  have hinvA : (σ z)⁻¹ ∈ A := (A.valuation_le_one_iff _).mp (by rw [map_inv₀, heq, inv_one])
  have hzinvA : z⁻¹ ∈ A := by
    have := (mem_iff_symm_apply_mem A hstab _).mp hinvA
    rwa [map_inv₀, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply] at this
  have : A.valuation z⁻¹ ≤ 1 := (A.valuation_le_one_iff _).mpr hzinvA
  rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hz0))] at this
  exact absurd hz (not_lt.mpr this)

theorem valuation_apply_eq {z r : AlgebraicClosure ℚ} (hr : σ r = r) (hzr : A.valuation z = A.valuation r) :
    A.valuation (σ z) = A.valuation z := by
  by_cases hr0 : r = 0
  · subst hr0
    rw [map_zero, Valuation.zero_iff] at hzr
    rw [hzr, map_zero]
  have hvr0 : A.valuation r ≠ 0 := (Valuation.ne_zero_iff _).mpr hr0
  have hu : A.valuation (z / r) = 1 := by rw [map_div₀, hzr, div_self hvr0]
  have hσu := valuation_apply_eq_one A hstab hu
  rw [map_div₀, hr, map_div₀, div_eq_one_iff_eq hvr0] at hσu
  rw [hσu, hzr]

end stabilizer

theorem valuation_sub_lt_of_mem_inertiaSubgroupIn (A : ValuationSubring (AlgebraicClosure ℚ))
    {σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    {z r : AlgebraicClosure ℚ} (hr : σ r = r) (hz0 : z ≠ 0)
    (hzr : A.valuation z = A.valuation r) : A.valuation (σ z - z) < A.valuation z := by
  classical
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero, Valuation.zero_iff] at hzr
    exact hz0 hzr
  have hvr0 : A.valuation r ≠ 0 := (Valuation.ne_zero_iff _).mpr hr0

  have hu1 : A.valuation (z / r) = 1 := by rw [map_div₀, hzr, div_self hvr0]
  have huA : z / r ∈ A := (A.valuation_le_one_iff _).mp hu1.le
  have hlt : A.valuation (σ (z / r) - z / r) < 1 :=
    (ValuationSubring.mem_nonunits_iff _).mp (sub_mem_nonunits_of_mem_inertiaSubgroupIn A hσ huA)

  have hzur : z = z / r * r := (div_mul_cancel₀ z hr0).symm
  have key : σ z - z = (σ (z / r) - z / r) * r := by
    conv_lhs => rw [hzur, map_mul, hr]
    ring
  rw [key, map_mul, hzr]
  calc A.valuation (σ (z / r) - z / r) * A.valuation r
      < 1 * A.valuation r := mul_lt_mul_of_pos_right hlt (zero_lt_iff.mpr hvr0)
    _ = A.valuation r := one_mul _

end M3dS12

open M3dS12 in

theorem solution (W : WeierstrassCurve ℚ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} (hq : q.Prime)
    {σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (x₀ y₀ α β : AlgebraicClosure ℚ) (hσx₀ : σ x₀ = x₀) (hσy₀ : σ y₀ = y₀) (hα : α ∈ A)
    (hαβ : A.valuation (α - β) = 1)
    (hsum : A.valuation (α + β + (W⁄(AlgebraicClosure ℚ)).a₁) < 1)
    (hFy : 2 * y₀ + (W⁄(AlgebraicClosure ℚ)).a₁ * x₀ + (W⁄(AlgebraicClosure ℚ)).a₃ = 0)
    {ℓ : ℕ} {x y : AlgebraicClosure ℚ} (h : (W⁄(AlgebraicClosure ℚ)).Nonsingular x y)
    (hP : ℓ • (Point.some x y h) = 0)
    (k : ℕ) (hlev : A.valuation (x - x₀) = A.valuation (q : AlgebraicClosure ℚ) ^ k)
    (hbr : A.valuation (y - y₀ - α * (x - x₀)) < A.valuation (x - x₀))
    (htrans : ∀ (x' y' : AlgebraicClosure ℚ) (h' : (W⁄(AlgebraicClosure ℚ)).Nonsingular x' y'),
      ℓ • (Point.some x' y' h') = 0 →
      A.valuation (x' - x₀) = A.valuation (x - x₀) →
      Point.some x' y' h' ≠ Point.some x y h →
      Point.some x' y' h' ≠ -Point.some x y h →
      A.valuation (x' - x) = A.valuation (x - x₀)) :
    σ • Point.some x y h = Point.some x y h := by
  classical
  have hstab : σ • A = A := smul_eq_of_mem_inertiaSubgroupIn A hσ

  have hns : (W⁄(AlgebraicClosure ℚ)).Nonsingular (σ x) (σ y) :=
    (W.toAffine.baseChange_nonsingular
      (σ.toAlgHom : (AlgebraicClosure ℚ) →ₐ[ℚ] (AlgebraicClosure ℚ)).injective x y).mpr h
  have hσP : σ • Point.some x y h = Point.some (σ x) (σ y) hns := rfl

  have hq0 : (q : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hvq0 : A.valuation (q : AlgebraicClosure ℚ) ≠ 0 := (Valuation.ne_zero_iff _).mpr hq0
  have hlev' : A.valuation (x - x₀) = A.valuation ((q : AlgebraicClosure ℚ) ^ k) := by
    rw [map_pow, hlev]
  have hvX0 : A.valuation (x - x₀) ≠ 0 := by rw [hlev]; exact pow_ne_zero _ hvq0
  have hX0 : x - x₀ ≠ 0 := (Valuation.ne_zero_iff _).mp hvX0

  have hσqk : σ ((q : AlgebraicClosure ℚ) ^ k) = (q : AlgebraicClosure ℚ) ^ k := by
    rw [map_pow, map_natCast]
  have hσX : σ x - x₀ = σ (x - x₀) := by rw [map_sub, hσx₀]
  have hσY : σ y - y₀ = σ (y - y₀) := by rw [map_sub, hσy₀]

  have hlevσ : A.valuation (σ x - x₀) = A.valuation (x - x₀) := by
    rw [hσX]
    exact valuation_apply_eq A hstab hσqk hlev'
  have hvσX0 : A.valuation (σ (x - x₀)) ≠ 0 := by rw [← hσX, hlevσ]; exact hvX0

  have hcontr : A.valuation (σ x - x) < A.valuation (x - x₀) := by
    have := valuation_sub_lt_of_mem_inertiaSubgroupIn A hσ hσqk hX0 hlev'
    have heq : σ (x - x₀) - (x - x₀) = σ x - x := by rw [map_sub, hσx₀]; ring
    rwa [heq] at this

  have hbrσ : A.valuation (σ y - y₀ - α * (σ x - x₀)) < A.valuation (σ x - x₀) := by

    have hwA : (y - y₀ - α * (x - x₀)) / (x - x₀) ∈ A.nonunits := by
      rw [ValuationSubring.mem_nonunits_iff, map_div₀, div_lt_one₀ (zero_lt_iff.mpr hvX0)]
      exact hbr
    have hwA' : (y - y₀ - α * (x - x₀)) / (x - x₀) ∈ A := A.nonunits_subset hwA
    have hw : A.valuation ((y - y₀ - α * (x - x₀)) / (x - x₀)) < 1 :=
      (ValuationSubring.mem_nonunits_iff _).mp hwA
    have hσw : A.valuation (σ ((y - y₀ - α * (x - x₀)) / (x - x₀))) < 1 :=
      valuation_apply_lt_one A hstab hwA' hw

    have hdecomp : σ y - y₀ - α * (σ x - x₀)
        = σ ((y - y₀ - α * (x - x₀)) / (x - x₀)) * σ (x - x₀) + (σ α - α) * σ (x - x₀) := by
      rw [← map_mul, div_mul_cancel₀ _ hX0, hσY, hσX, map_sub σ (y - y₀), map_mul]
      ring
    rw [hdecomp, hσX]
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]
      calc A.valuation (σ ((y - y₀ - α * (x - x₀)) / (x - x₀))) * A.valuation (σ (x - x₀))
          < 1 * A.valuation (σ (x - x₀)) := mul_lt_mul_of_pos_right hσw (zero_lt_iff.mpr hvσX0)
        _ = A.valuation (σ (x - x₀)) := one_mul _
    · rw [map_mul]
      have hα1 : A.valuation (σ α - α) < 1 :=
        (ValuationSubring.mem_nonunits_iff _).mp (sub_mem_nonunits_of_mem_inertiaSubgroupIn A hσ hα)
      calc A.valuation (σ α - α) * A.valuation (σ (x - x₀))
          < 1 * A.valuation (σ (x - x₀)) := mul_lt_mul_of_pos_right hα1 (zero_lt_iff.mpr hvσX0)
        _ = A.valuation (σ (x - x₀)) := one_mul _

  have hPσ : ℓ • (Point.some (σ x) (σ y) hns) = 0 := by
    rw [← hσP, WeierstrassCurve.Affine.Point.algEquiv_smul_def, ← map_nsmul, hP, map_zero]

  have hne' : Point.some (σ x) (σ y) hns ≠ -Point.some x y h := by
    intro heq
    rw [WeierstrassCurve.Affine.Point.neg_some] at heq
    obtain ⟨hxx, hyy⟩ := WeierstrassCurve.Affine.Point.some.inj heq

    have hyy' : σ y - y₀ = -(y - y₀) - (W⁄(AlgebraicClosure ℚ)).a₁ * (x - x₀) := by
      rw [hyy]
      simp only [WeierstrassCurve.Affine.negY]
      linear_combination (-1 : AlgebraicClosure ℚ) * hFy
    have h1 : A.valuation (-(y - y₀) - (W⁄(AlgebraicClosure ℚ)).a₁ * (x - x₀) - α * (x - x₀))
        < A.valuation (x - x₀) := by
      have := hbrσ
      rwa [hyy', hxx] at this

    have h2 : A.valuation (-((α + β + (W⁄(AlgebraicClosure ℚ)).a₁) * (x - x₀) + (α - β) * (x - x₀)))
        < A.valuation (x - x₀) := by
      have hsum' := Valuation.map_add_lt A.valuation h1 hbr
      have heq : -(y - y₀) - (W⁄(AlgebraicClosure ℚ)).a₁ * (x - x₀) - α * (x - x₀)
          + (y - y₀ - α * (x - x₀))
          = -((α + β + (W⁄(AlgebraicClosure ℚ)).a₁) * (x - x₀) + (α - β) * (x - x₀)) := by ring
      rwa [heq] at hsum'
    rw [Valuation.map_neg] at h2
    have h3 : A.valuation ((α + β + (W⁄(AlgebraicClosure ℚ)).a₁) * (x - x₀)) < A.valuation (x - x₀) := by
      rw [map_mul]
      calc A.valuation (α + β + (W⁄(AlgebraicClosure ℚ)).a₁) * A.valuation (x - x₀)
          < 1 * A.valuation (x - x₀) := mul_lt_mul_of_pos_right hsum (zero_lt_iff.mpr hvX0)
        _ = A.valuation (x - x₀) := one_mul _

    have h4 : A.valuation ((α - β) * (x - x₀)) < A.valuation (x - x₀) := by
      have := Valuation.map_add_lt A.valuation h2 (by rwa [Valuation.map_neg] : A.valuation
        (-((α + β + (W⁄(AlgebraicClosure ℚ)).a₁) * (x - x₀))) < A.valuation (x - x₀))
      have heq : (α + β + (W⁄(AlgebraicClosure ℚ)).a₁) * (x - x₀) + (α - β) * (x - x₀)
          + -((α + β + (W⁄(AlgebraicClosure ℚ)).a₁) * (x - x₀)) = (α - β) * (x - x₀) := by ring
      rwa [heq] at this
    rw [map_mul, hαβ, one_mul] at h4
    exact lt_irrefl _ h4

  rw [hσP]
  by_contra hne
  have := htrans (σ x) (σ y) hns hPσ hlevσ hne hne'
  rw [this] at hcontr
  exact lt_irrefl _ hcontr

end S_WeierstrassCurve_Affine_Point_smul_eq_self_of_mem_inertiaSubgroupIn_of_level
end P2MW
export P2MW.S_WeierstrassCurve_Affine_Point_smul_eq_self_of_mem_inertiaSubgroupIn_of_level (solution)
