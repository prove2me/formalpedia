-- Prove2me | solution 1 for WeierstrassCurve.exists_reductionKernel_absorbing_inertia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/ba78696a-22d0-5abf-a045-4cbc0e2d69e0

import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_reductionKernel_absorbing_inertia

set_option autoImplicit false

open IsLocalRing

namespace ValuationSubring
p2m_export "ValuationSubring" "subtype coe_mem_nonunits_iff neg_mem inertiaSubgroup toSubring ext mem_nonunits_iff_or zero_mem nonunits mem_nonunits_iff smul_mem_pointwise_smul inv_mem_nonunits_iff mul_mem one_mem mem_or_inv_mem nonunits_subset add_mem decompositionSubgroup valuation_le_one_iff algebra valuation subtype_injective inertiaSubgroupIn smul_mem_of_mem_decompositionSubgroup residue_smul_eq_of_mem_inertiaSubgroup"
p2m_open "ValuationSubring"

variable {L : Type*} [Field L] (A : ValuationSubring L)

private theorem _root_.ValuationSubring.mul_mem_nonunits {a x : L} (ha : a ∈ A) (hx : x ∈ A.nonunits) :
    a * x ∈ A.nonunits := by
  rw [mem_nonunits_iff] at hx ⊢
  calc A.valuation (a * x) = A.valuation a * A.valuation x := map_mul _ _ _
    _ ≤ 1 * A.valuation x := mul_le_mul_left ((A.valuation_le_one_iff a).mpr ha) _
    _ = A.valuation x := one_mul _
    _ < 1 := hx

p2m_export "ValuationSubring" "mul_mem_nonunits"
private theorem _root_.ValuationSubring.one_notMem_nonunits : (1 : L) ∉ A.nonunits := by
  simp [mem_nonunits_iff]

p2m_export "ValuationSubring" "one_notMem_nonunits"
end ValuationSubring

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.negY Affine.slope_of_X_ne Affine.equation_neg a₃ Affine.Point.add_of_Y_eq Affine.addPolynomial_slope a₁ map Affine.equation_iff_nonsingular_of_Δ_ne_zero Affine.nonsingular_iff a₄ a₂ a₆ Affine.Point.some Affine.Point.some.inj Affine.negAddY reduction Affine.negY_negY toAffine Affine.slope_of_Y_ne Affine.Point Affine.addX Affine.Point.add_some Affine.nonsingular_neg map_Δ Affine.addPolynomial_eq Affine.Point.map Affine.Point.some_ne_zero Δ Affine.map_negY Affine.Y_eq_of_X_eq Affine.equation_iff Affine.Point.neg_some"
p2m_open "WeierstrassCurve"

variable {L : Type*} [Field L] {A : ValuationSubring L}

private lemma some_congr {R : Type*} [CommRing R] {V : Affine R} {x₁ x₂ y₁ y₂ : R}
    (hx : x₁ = x₂) (hy : y₁ = y₂) (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

variable (W : WeierstrassCurve A)

namespace Affine p2m_export "WeierstrassCurve.Affine" "Equation negY Y_eq_of_Y_ne slope_of_X_ne equation_neg Point.add_of_Y_eq addPolynomial_slope equation_iff_nonsingular_of_Δ_ne_zero slope nonsingular_iff map map_equation Point.some Nonsingular Point.some.inj negAddY negY_negY equation_negAdd slope_of_Y_ne Point addX Point.add_some nonsingular_neg addPolynomial_eq Point.map Point.some_ne_zero map_negY addY Y_eq_of_X_eq equation_iff polynomial Point.neg_some" end Affine
p2m_open_scoped "WeierstrassCurve.Affine" in

theorem Affine.Y_mem_of_X_mem {x y : L}
    (h : (W.map A.subtype).toAffine.Equation x y) (hx : x ∈ A) : y ∈ A := by
  by_contra hy

  have hy0 : y ≠ 0 := fun h0 => hy (h0 ▸ A.zero_mem)
  have hyinv : y⁻¹ ∈ A.nonunits := A.inv_mem_nonunits_iff.mpr (Or.inr hy)
  rw [equation_iff] at h

  have key : (1 : L) =
      (x ^ 3 + (W.map A.subtype).toAffine.a₂ * x ^ 2 + (W.map A.subtype).toAffine.a₄ * x
          + (W.map A.subtype).toAffine.a₆) * (y⁻¹ * y⁻¹)
        - (W.map A.subtype).toAffine.a₁ * x * y⁻¹
        - (W.map A.subtype).toAffine.a₃ * y⁻¹ := by
    field_simp
    linear_combination h

  refine A.one_notMem_nonunits ?_
  rw [key]
  have ha₁ : (W.map A.subtype).toAffine.a₁ ∈ A := SetLike.coe_mem W.a₁
  have ha₂ : (W.map A.subtype).toAffine.a₂ ∈ A := SetLike.coe_mem W.a₂
  have ha₃ : (W.map A.subtype).toAffine.a₃ ∈ A := SetLike.coe_mem W.a₃
  have ha₄ : (W.map A.subtype).toAffine.a₄ ∈ A := SetLike.coe_mem W.a₄
  have ha₆ : (W.map A.subtype).toAffine.a₆ ∈ A := SetLike.coe_mem W.a₆
  have hcubic : x ^ 3 + (W.map A.subtype).toAffine.a₂ * x ^ 2
      + (W.map A.subtype).toAffine.a₄ * x + (W.map A.subtype).toAffine.a₆ ∈ A :=
    add_mem (add_mem (add_mem (pow_mem hx 3) (mul_mem ha₂ (pow_mem hx 2))) (mul_mem ha₄ hx)) ha₆
  exact sub_mem (sub_mem (A.mul_mem_nonunits hcubic (mul_mem hyinv hyinv))
      (A.mul_mem_nonunits (mul_mem ha₁ hx) hyinv))
    (A.mul_mem_nonunits ha₃ hyinv)

theorem map_residue_Δ_ne_zero_iff : (W.map (residue A)).Δ ≠ 0 ↔ IsUnit W.Δ := by
  rw [map_Δ]
  exact residue_ne_zero_iff_isUnit W.Δ

p2m_open_scoped "WeierstrassCurve.Affine" in

theorem Affine.equation_residue {x y : A}
    (h : (W.map A.subtype).toAffine.Equation (x : L) (y : L)) :
    (W.map (residue A)).toAffine.Equation (residue A x) (residue A y) := by
  have hA : W.toAffine.Equation x y := (W.toAffine.map_equation A.subtype_injective x y).mp h
  exact hA.map (residue A)

p2m_open_scoped "WeierstrassCurve.Affine" in

theorem Affine.nonsingular_residue (hΔ : (W.map (residue A)).Δ ≠ 0) {x y : A}
    (h : (W.map A.subtype).toAffine.Equation (x : L) (y : L)) :
    (W.map (residue A)).toAffine.Nonsingular (residue A x) (residue A y) :=
  (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp (Affine.equation_residue W h)

variable {W}

open Classical in

noncomputable def reducePoint (hΔ : (W.map (residue A)).Δ ≠ 0) :
    (W.map A.subtype).toAffine.Point → (W.map (residue A)).toAffine.Point
  | .zero => .zero
  | .some x y h =>
    if hx : x ∈ A then
      .some (residue A ⟨x, hx⟩) (residue A ⟨y, Affine.Y_mem_of_X_mem W h.1 hx⟩)
        (Affine.nonsingular_residue W hΔ h.1)
    else
      .zero

variable (hΔ : (W.map (residue A)).Δ ≠ 0)

@[scoped simp]
lemma reducePoint_zero : reducePoint hΔ (0 : (W.map A.subtype).toAffine.Point) = 0 :=
  rfl

lemma reducePoint_some_of_mem {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y)
    (hx : x ∈ A) :
    reducePoint hΔ (.some x y h) =
      .some (residue A ⟨x, hx⟩) (residue A ⟨y, Affine.Y_mem_of_X_mem W h.1 hx⟩)
        (Affine.nonsingular_residue W hΔ h.1) := by
  simp only [reducePoint]
  exact dif_pos hx

lemma reducePoint_some_of_notMem {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y)
    (hx : x ∉ A) : reducePoint hΔ (.some x y h) = 0 := by
  simp only [reducePoint]
  exact dif_neg hx

theorem reducePoint_neg (P : (W.map A.subtype).toAffine.Point) :
    reducePoint hΔ (-P) = -reducePoint hΔ P := by
  cases P with
  | zero => rfl
  | some x y h =>
    rw [Affine.Point.neg_some]
    by_cases hx : x ∈ A
    · have hy : y ∈ A := Affine.Y_mem_of_X_mem W h.1 hx
      rw [reducePoint_some_of_mem _ _ hx, reducePoint_some_of_mem _ _ hx,
        Affine.Point.neg_some]
      refine some_congr rfl ?_ _ _

      show residue A (W.toAffine.negY ⟨x, hx⟩ ⟨y, hy⟩) = _
      exact (Affine.map_negY (residue A) (⟨x, hx⟩ : A) (⟨y, hy⟩ : A)).symm
    · rw [reducePoint_some_of_notMem _ _ hx, reducePoint_some_of_notMem _ _ hx]
      rfl

section Inertia

open scoped Pointwise

variable (K : Type*) [Field K] [Algebra K L]

private theorem _root_.ValuationSubring.smul_mem_of_mem_decompositionSubgroup {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.decompositionSubgroup K) {z : L} (hz : z ∈ A) : σ z ∈ A := by
  have h1 : σ • z ∈ σ • A := ValuationSubring.smul_mem_pointwise_smul σ z A hz
  rwa [MulAction.mem_stabilizer_iff.mp hσ, AlgEquiv.smul_def] at h1

p2m_alias "P2MW.S_WeierstrassCurve_exists_reductionKernel_absorbing_inertia.ValuationSubring.smul_mem_of_mem_decompositionSubgroup" "ValuationSubring.smul_mem_of_mem_decompositionSubgroup"
variable {K}

private theorem _root_.ValuationSubring.residue_smul_eq_of_mem_inertiaSubgroup
    {σ : L ≃ₐ[K] L} (hσ : σ ∈ A.decompositionSubgroup K)
    (hσI : (⟨σ, hσ⟩ : A.decompositionSubgroup K) ∈ A.inertiaSubgroup K) (a : A) :
    residue A ((⟨σ, hσ⟩ : A.decompositionSubgroup K) • a) = residue A a := by
  have h1 : MulSemiringAction.toRingAut (A.decompositionSubgroup K) (ResidueField A)
      ⟨σ, hσ⟩ = 1 := hσI
  calc residue A ((⟨σ, hσ⟩ : A.decompositionSubgroup K) • a)
      = (⟨σ, hσ⟩ : A.decompositionSubgroup K) • residue A a := rfl
    _ = MulSemiringAction.toRingAut (A.decompositionSubgroup K) (ResidueField A)
          ⟨σ, hσ⟩ (residue A a) := rfl
    _ = residue A a := by rw [h1]; rfl

p2m_alias "P2MW.S_WeierstrassCurve_exists_reductionKernel_absorbing_inertia.ValuationSubring.residue_smul_eq_of_mem_inertiaSubgroup" "ValuationSubring.residue_smul_eq_of_mem_inertiaSubgroup"

theorem reducePoint_some_apply_of_mem_inertia {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.decompositionSubgroup K)
    (hσI : (⟨σ, hσ⟩ : A.decompositionSubgroup K) ∈ A.inertiaSubgroup K)
    {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y)
    (h' : (W.map A.subtype).toAffine.Nonsingular (σ x) (σ y)) :
    reducePoint hΔ (.some (σ x) (σ y) h') = reducePoint hΔ (.some x y h) := by
  by_cases hx : x ∈ A
  · have hy : y ∈ A := Affine.Y_mem_of_X_mem W h.1 hx
    have hσx : σ x ∈ A := A.smul_mem_of_mem_decompositionSubgroup K hσ hx
    have hσy : σ y ∈ A := A.smul_mem_of_mem_decompositionSubgroup K hσ hy
    rw [reducePoint_some_of_mem _ _ hσx, reducePoint_some_of_mem _ _ hx]

    refine some_congr ?_ ?_ _ _
    · calc residue A (⟨σ x, hσx⟩ : A)
          = residue A ((⟨σ, hσ⟩ : A.decompositionSubgroup K) • (⟨x, hx⟩ : A)) := rfl
        _ = residue A (⟨x, hx⟩ : A) := A.residue_smul_eq_of_mem_inertiaSubgroup hσ hσI _
    · calc residue A (⟨σ y, hσy⟩ : A)
          = residue A ((⟨σ, hσ⟩ : A.decompositionSubgroup K) • (⟨y, hy⟩ : A)) := rfl
        _ = residue A (⟨y, hy⟩ : A) := A.residue_smul_eq_of_mem_inertiaSubgroup hσ hσI _
  · have hσx : σ x ∉ A := fun hmem => hx (by
      simpa using A.smul_mem_of_mem_decompositionSubgroup K (inv_mem hσ) hmem)
    rw [reducePoint_some_of_notMem _ _ hσx, reducePoint_some_of_notMem _ _ hx]

end Inertia

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_reductionKernel_absorbing_inertia.WeierstrassCurve"

open IsLocalRing

namespace ValuationSubring
p2m_export "ValuationSubring" "subtype coe_mem_nonunits_iff neg_mem inertiaSubgroup toSubring ext mem_nonunits_iff_or zero_mem nonunits mem_nonunits_iff smul_mem_pointwise_smul inv_mem_nonunits_iff mul_mem one_mem mem_or_inv_mem nonunits_subset add_mem decompositionSubgroup valuation_le_one_iff algebra valuation subtype_injective inertiaSubgroupIn smul_mem_of_mem_decompositionSubgroup residue_smul_eq_of_mem_inertiaSubgroup"
p2m_open "ValuationSubring"

variable {L : Type*} [Field L] (A : ValuationSubring L)

private theorem _root_.ValuationSubring.add_notMem {x a : L} (hx : x ∉ A) (ha : a ∈ A) : x + a ∉ A := fun h =>
  hx (by simpa using A.toSubring.sub_mem h ha)

p2m_export "ValuationSubring" "add_notMem"

private theorem _root_.ValuationSubring.mul_notMem {x y : L} (hx : x ∉ A) (hy : y ∉ A) : x * y ∉ A := fun h => by
  rcases A.mem_or_inv_mem x with hx' | hx'
  · exact hx hx'
  · have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ A.zero_mem)
    exact hy (by simpa [inv_mul_cancel_left₀ hx0] using A.toSubring.mul_mem hx' h)

p2m_export "ValuationSubring" "mul_notMem"

private theorem _root_.ValuationSubring.div_notMem {a b : L} (ha' : a ∉ A.nonunits) (hb : b ∈ A.nonunits) (hb0 : b ≠ 0) :
    a / b ∉ A := fun h => by
  refine ha' ?_
  rw [show a = a / b * b from (div_mul_cancel₀ a hb0).symm]
  exact A.mul_mem_nonunits h hb

p2m_export "ValuationSubring" "div_notMem"

private theorem _root_.ValuationSubring.coe_mem_nonunits_iff_residue_eq_zero (e : A) :
    (e : L) ∈ A.nonunits ↔ residue A e = 0 := by
  rw [A.coe_mem_nonunits_iff, residue_eq_zero_iff]

p2m_export "ValuationSubring" "coe_mem_nonunits_iff_residue_eq_zero"
end ValuationSubring
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_reductionKernel_absorbing_inertia.WeierstrassCurve"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.negY Affine.slope_of_X_ne Affine.equation_neg a₃ Affine.Point.add_of_Y_eq Affine.addPolynomial_slope a₁ map Affine.equation_iff_nonsingular_of_Δ_ne_zero Affine.nonsingular_iff a₄ a₂ a₆ Affine.Point.some Affine.Point.some.inj Affine.negAddY reduction Affine.negY_negY toAffine Affine.slope_of_Y_ne Affine.Point Affine.addX Affine.Point.add_some Affine.nonsingular_neg map_Δ Affine.addPolynomial_eq Affine.Point.map Affine.Point.some_ne_zero Δ Affine.map_negY Affine.Y_eq_of_X_eq Affine.equation_iff Affine.Point.neg_some"
p2m_open "WeierstrassCurve"

namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation negY Y_eq_of_Y_ne slope_of_X_ne equation_neg Point.add_of_Y_eq addPolynomial_slope equation_iff_nonsingular_of_Δ_ne_zero slope nonsingular_iff map map_equation Point.some Nonsingular Point.some.inj negAddY negY_negY equation_negAdd slope_of_Y_ne Point addX Point.add_some nonsingular_neg addPolynomial_eq Point.map Point.some_ne_zero map_negY addY Y_eq_of_X_eq equation_iff polynomial Point.neg_some"
p2m_open "WeierstrassCurve.Affine"

theorem sub_mul_sub_negY {R : Type*} [CommRing R] {V : Affine R} {x₁ x₂ y₁ y₂ : R}
    (h₁ : V.Equation x₁ y₁) (h₂ : V.Equation x₂ y₂) :
    (y₁ - y₂) * (y₁ - V.negY x₂ y₂) =
      (x₁ - x₂) * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + V.a₂ * (x₁ + x₂) + V.a₄ - V.a₁ * y₁) := by
  rw [equation_iff] at h₁ h₂
  rw [negY]
  linear_combination h₁ - h₂

end Affine
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_reductionKernel_absorbing_inertia.WeierstrassCurve"

variable {L : Type*} [Field L] {A : ValuationSubring L} (W : WeierstrassCurve A)

p2m_open_scoped "WeierstrassCurve.Affine" in

theorem Affine.notMem_nonunits_of_sub_negY_mem_nonunits (hΔ : (W.map (residue A)).Δ ≠ 0)
    {x y : L} (h : (W.map A.subtype).toAffine.Equation x y) (hx : x ∈ A)
    (hY : y - (W.map A.subtype).toAffine.negY x y ∈ A.nonunits) :
    3 * x ^ 2 + 2 * (W.map A.subtype).toAffine.a₂ * x + (W.map A.subtype).toAffine.a₄ -
      (W.map A.subtype).toAffine.a₁ * y ∉ A.nonunits := by
  have hy : y ∈ A := Affine.Y_mem_of_X_mem W h hx

  set eX : A := 3 * ⟨x, hx⟩ ^ 2 + 2 * W.a₂ * ⟨x, hx⟩ + W.a₄ - W.a₁ * ⟨y, hy⟩ with heX
  set eY : A := ⟨y, hy⟩ - W.toAffine.negY ⟨x, hx⟩ ⟨y, hy⟩ with heY

  have hcoeX : (eX : L) = 3 * x ^ 2 + 2 * (W.map A.subtype).toAffine.a₂ * x +
      (W.map A.subtype).toAffine.a₄ - (W.map A.subtype).toAffine.a₁ * y := by
    push_cast [heX]
    rfl
  have hcoeY : (eY : L) = y - (W.map A.subtype).toAffine.negY x y := by
    have h1 : ((W.toAffine.negY ⟨x, hx⟩ ⟨y, hy⟩ : A) : L) = (W.map A.subtype).toAffine.negY x y :=
      (Affine.map_negY A.subtype (⟨x, hx⟩ : A) (⟨y, hy⟩ : A)).symm
    rw [heY]
    push_cast
    rw [h1]

  have hns := Affine.nonsingular_residue W hΔ (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) h
  rw [Affine.nonsingular_iff] at hns

  have hY0 : residue A eY = 0 := by
    rw [← A.coe_mem_nonunits_iff_residue_eq_zero, hcoeY]
    exact hY

  have hX0 : residue A eX ≠ 0 := by
    rcases hns.2 with hX | hY'
    · intro h0
      apply hX
      rw [heX] at h0
      simp only [map_sub, map_add, map_mul, map_pow, map_ofNat] at h0
      show residue A W.a₁ * residue A ⟨y, hy⟩ = 3 * residue A ⟨x, hx⟩ ^ 2 +
        2 * residue A W.a₂ * residue A ⟨x, hx⟩ + residue A W.a₄
      linear_combination -h0
    · exact absurd (by
        show residue A ⟨y, hy⟩ = -residue A ⟨y, hy⟩ - residue A W.a₁ * residue A ⟨x, hx⟩ -
          residue A W.a₃
        rw [heY] at hY0
        simp only [Affine.negY, map_sub, map_neg, map_mul] at hY0
        linear_combination hY0) hY'

  rw [← hcoeX, A.coe_mem_nonunits_iff_residue_eq_zero]
  exact hX0

section Slope

variable [DecidableEq L]

p2m_open_scoped "WeierstrassCurve.Affine" in

theorem Affine.slope_notMem_of_sub_mem_nonunits (hΔ : (W.map (residue A)).Δ ≠ 0)
    {x₁ x₂ y₁ y₂ : L} (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hPQ : ¬(x₁ = x₂ ∧ y₁ = (W.map A.subtype).toAffine.negY x₂ y₂))
    (hxx : x₁ - x₂ ∈ A.nonunits)
    (hyy : y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A.nonunits) :
    (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ ∉ A := by
  have hy₁ : y₁ ∈ A := Affine.Y_mem_of_X_mem W h₁ hx₁
  have hy₂ : y₂ ∈ A := Affine.Y_mem_of_X_mem W h₂ hx₂

  have ha₁ : (W.map A.subtype).toAffine.a₁ ∈ A := SetLike.coe_mem W.a₁
  have ha₂ : (W.map A.subtype).toAffine.a₂ ∈ A := SetLike.coe_mem W.a₂
  have ha₃ : (W.map A.subtype).toAffine.a₃ ∈ A := SetLike.coe_mem W.a₃
  have ha₄ : (W.map A.subtype).toAffine.a₄ ∈ A := SetLike.coe_mem W.a₄

  have hnegY : (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A := by
    rw [Affine.negY]
    exact A.toSubring.sub_mem (A.toSubring.sub_mem (A.toSubring.neg_mem hy₂)
      (A.toSubring.mul_mem ha₁ hx₂)) ha₃
  by_cases hx : x₁ = x₂
  ·

    have hy : y₁ ≠ (W.map A.subtype).toAffine.negY x₂ y₂ := fun h => hPQ ⟨hx, h⟩
    have hy12 : y₁ = y₂ := (Affine.Y_eq_of_X_eq h₁ h₂ hx).resolve_right hy
    rw [Affine.slope_of_Y_ne hx hy]

    have hden : y₁ - (W.map A.subtype).toAffine.negY x₁ y₁ ∈ A.nonunits := by
      rwa [← hx, ← hy12] at hyy
    have hden0 : y₁ - (W.map A.subtype).toAffine.negY x₁ y₁ ≠ 0 := by
      rw [sub_ne_zero]
      intro hcon
      exact hy (by rw [← hx, ← hy12]; exact hcon)

    have hnum := Affine.notMem_nonunits_of_sub_negY_mem_nonunits W hΔ h₁ hx₁ hden
    exact A.div_notMem hnum hden hden0
  ·
    by_cases hyy' : y₁ - y₂ ∈ A.nonunits
    ·

      rw [Affine.slope_of_X_ne hx]

      have hden : y₁ - (W.map A.subtype).toAffine.negY x₁ y₁ ∈ A.nonunits := by
        have key : y₁ - (W.map A.subtype).toAffine.negY x₁ y₁ =
            (y₁ - (W.map A.subtype).toAffine.negY x₂ y₂) + (y₁ - y₂) +
              (W.map A.subtype).toAffine.a₁ * (x₁ - x₂) := by
          simp only [Affine.negY]
          ring
        rw [key]
        exact add_mem (add_mem hyy hyy') (A.mul_mem_nonunits ha₁ hxx)

      have hnum := Affine.notMem_nonunits_of_sub_negY_mem_nonunits W hΔ h₁ hx₁ hden

      set N : L := x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (W.map A.subtype).toAffine.a₂ * (x₁ + x₂) +
        (W.map A.subtype).toAffine.a₄ - (W.map A.subtype).toAffine.a₁ * y₁ with hN
      have hNunit : N ∉ A.nonunits := by
        intro hmem
        apply hnum
        have key : 3 * x₁ ^ 2 + 2 * (W.map A.subtype).toAffine.a₂ * x₁ +
            (W.map A.subtype).toAffine.a₄ - (W.map A.subtype).toAffine.a₁ * y₁ =
            N - (x₁ + x₁ + x₂ + (W.map A.subtype).toAffine.a₂) * -(x₁ - x₂) := by
          rw [hN]; ring
        rw [key]
        exact sub_mem hmem (A.mul_mem_nonunits
          (add_mem (add_mem (add_mem hx₁ hx₁) hx₂) ha₂) (neg_mem hxx))

      have hd0 : y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ≠ 0 := by
        intro hd
        apply hNunit
        rw [hN]
        have hid := Affine.sub_mul_sub_negY h₁ h₂
        rw [hd, mul_zero] at hid
        rcases mul_eq_zero.mp hid.symm with h | h
        · exact absurd (sub_eq_zero.mp h) hx
        · rw [h]
          exact zero_mem _

      have hslope : (y₁ - y₂) / (x₁ - x₂) = N / (y₁ - (W.map A.subtype).toAffine.negY x₂ y₂) := by
        rw [div_eq_div_iff (sub_ne_zero.mpr hx) hd0, hN]
        linear_combination Affine.sub_mul_sub_negY h₁ h₂
      rw [hslope]
      exact A.div_notMem hNunit hyy hd0
    ·

      rw [Affine.slope_of_X_ne hx]
      exact A.div_notMem hyy' hxx (sub_ne_zero.mpr hx)

p2m_open_scoped "WeierstrassCurve.Affine" in

theorem Affine.addX_notMem_of_sub_mem_nonunits (hΔ : (W.map (residue A)).Δ ≠ 0)
    {x₁ x₂ y₁ y₂ : L} (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hPQ : ¬(x₁ = x₂ ∧ y₁ = (W.map A.subtype).toAffine.negY x₂ y₂))
    (hxx : x₁ - x₂ ∈ A.nonunits)
    (hyy : y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A.nonunits) :
    (W.map A.subtype).toAffine.addX x₁ x₂ ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) ∉ A := by
  have hℓ := Affine.slope_notMem_of_sub_mem_nonunits W hΔ h₁ h₂ hx₁ hx₂ hPQ hxx hyy
  set ℓ : L := (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂
  have ha₁ : (W.map A.subtype).toAffine.a₁ ∈ A := SetLike.coe_mem W.a₁
  have ha₂ : (W.map A.subtype).toAffine.a₂ ∈ A := SetLike.coe_mem W.a₂

  rw [show (W.map A.subtype).toAffine.addX x₁ x₂ ℓ =
    ℓ * (ℓ + (W.map A.subtype).toAffine.a₁) +
      (-(W.map A.subtype).toAffine.a₂ - x₁ - x₂) from by rw [Affine.addX]; ring]
  exact A.add_notMem (A.mul_notMem hℓ (by simpa [add_comm] using A.add_notMem hℓ ha₁))
    (A.toSubring.sub_mem (A.toSubring.sub_mem (A.toSubring.neg_mem ha₂) hx₁) hx₂)

end Slope
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_reductionKernel_absorbing_inertia.WeierstrassCurve"

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_reductionKernel_absorbing_inertia.WeierstrassCurve"

open IsLocalRing

namespace ValuationSubring
p2m_export "ValuationSubring" "subtype coe_mem_nonunits_iff neg_mem inertiaSubgroup toSubring ext mem_nonunits_iff_or zero_mem nonunits mem_nonunits_iff smul_mem_pointwise_smul inv_mem_nonunits_iff mul_mem one_mem mem_or_inv_mem nonunits_subset add_mem decompositionSubgroup valuation_le_one_iff algebra valuation subtype_injective inertiaSubgroupIn smul_mem_of_mem_decompositionSubgroup residue_smul_eq_of_mem_inertiaSubgroup"
p2m_open "ValuationSubring"

variable {L : Type*} [Field L] (A : ValuationSubring L)

private theorem _root_.ValuationSubring.ne_zero_of_notMem_nonunits {a : L} (ha : a ∉ A.nonunits) : a ≠ 0 := fun h =>
  ha (h ▸ A.nonunits.zero_mem)

p2m_export "ValuationSubring" "ne_zero_of_notMem_nonunits"

private theorem _root_.ValuationSubring.inv_mem_of_notMem_nonunits {a : L} (ha : a ∉ A.nonunits) : a⁻¹ ∈ A := by
  rw [mem_nonunits_iff_or] at ha
  push Not at ha
  exact ha.2

p2m_export "ValuationSubring" "inv_mem_of_notMem_nonunits"

private theorem _root_.ValuationSubring.inv_mem_nonunits_of_notMem {a : L} (ha : a ∉ A) : a⁻¹ ∈ A.nonunits :=
  A.inv_mem_nonunits_iff.mpr (Or.inr ha)

p2m_export "ValuationSubring" "inv_mem_nonunits_of_notMem"

private theorem _root_.ValuationSubring.inv_mem_of_notMem {a : L} (ha : a ∉ A) : a⁻¹ ∈ A :=
  A.nonunits_subset (A.inv_mem_nonunits_of_notMem ha)

p2m_export "ValuationSubring" "inv_mem_of_notMem"

private theorem _root_.ValuationSubring.add_notMem_nonunits {a b : L} (ha : a ∉ A.nonunits) (hb : b ∈ A.nonunits) :
    a + b ∉ A.nonunits := fun h => ha (by simpa using A.nonunits.sub_mem h hb)

p2m_export "ValuationSubring" "add_notMem_nonunits"

private theorem _root_.ValuationSubring.mul_notMem_nonunits {a b : L} (ha : a ∉ A.nonunits) (hb : b ∉ A.nonunits) :
    a * b ∉ A.nonunits := by
  intro h
  have ha0 := A.ne_zero_of_notMem_nonunits ha
  have hb0 := A.ne_zero_of_notMem_nonunits hb
  rw [mem_nonunits_iff_or] at h
  rcases h with h | h
  · exact (mul_ne_zero ha0 hb0) h
  · exact h (mul_inv_rev a b ▸ A.toSubring.mul_mem (A.inv_mem_of_notMem_nonunits hb)
      (A.inv_mem_of_notMem_nonunits ha))

p2m_export "ValuationSubring" "mul_notMem_nonunits"

private theorem _root_.ValuationSubring.inv_notMem_nonunits_of_notMem_nonunits {a : L} (ha : a ∈ A) (ha' : a ∉ A.nonunits) :
    a⁻¹ ∉ A.nonunits := by
  rw [mem_nonunits_iff_or]
  push Not
  exact ⟨inv_ne_zero (A.ne_zero_of_notMem_nonunits ha'), by rwa [inv_inv]⟩

p2m_export "ValuationSubring" "inv_notMem_nonunits_of_notMem_nonunits"

private theorem _root_.ValuationSubring.one_add_notMem_nonunits {a : L} (ha : a ∈ A.nonunits) : 1 + a ∉ A.nonunits :=
  A.add_notMem_nonunits A.one_notMem_nonunits ha

p2m_export "ValuationSubring" "one_add_notMem_nonunits"

theorem natCast_mem_nonunits_iff_residue_eq_zero (n : ℕ) :
    (n : L) ∈ A.nonunits ↔ (n : ResidueField A) = 0 := by
  have h1 : ((n : A) : L) = (n : L) := by push_cast; rfl
  have h2 : residue A (n : A) = (n : ResidueField A) := map_natCast (residue A) n
  rw [← h1, A.coe_mem_nonunits_iff_residue_eq_zero, h2]

end ValuationSubring
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_reductionKernel_absorbing_inertia.WeierstrassCurve"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.negY Affine.slope_of_X_ne Affine.equation_neg a₃ Affine.Point.add_of_Y_eq Affine.addPolynomial_slope a₁ map Affine.equation_iff_nonsingular_of_Δ_ne_zero Affine.nonsingular_iff a₄ a₂ a₆ Affine.Point.some Affine.Point.some.inj Affine.negAddY reduction Affine.negY_negY toAffine Affine.slope_of_Y_ne Affine.Point Affine.addX Affine.Point.add_some Affine.nonsingular_neg map_Δ Affine.addPolynomial_eq Affine.Point.map Affine.Point.some_ne_zero Δ Affine.map_negY Affine.Y_eq_of_X_eq Affine.equation_iff Affine.Point.neg_some"
p2m_open "WeierstrassCurve"

p2m_open "ValuationSubring P2MW.S_WeierstrassCurve_exists_reductionKernel_absorbing_inertia.ValuationSubring"

variable {L : Type*} [Field L] {A : ValuationSubring L}

variable (W : WeierstrassCurve A)

namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation negY Y_eq_of_Y_ne slope_of_X_ne equation_neg Point.add_of_Y_eq addPolynomial_slope equation_iff_nonsingular_of_Δ_ne_zero slope nonsingular_iff map map_equation Point.some Nonsingular Point.some.inj negAddY negY_negY equation_negAdd slope_of_Y_ne Point addX Point.add_some nonsingular_neg addPolynomial_eq Point.map Point.some_ne_zero map_negY addY Y_eq_of_X_eq equation_iff polynomial Point.neg_some"
p2m_open "WeierstrassCurve.Affine"

theorem cubic_inv_notMem_nonunits {x : L} (hx : x ∉ A) :
    1 + (W.map A.subtype).toAffine.a₂ * x⁻¹ + (W.map A.subtype).toAffine.a₄ * (x⁻¹ * x⁻¹)
      + (W.map A.subtype).toAffine.a₆ * (x⁻¹ * x⁻¹ * x⁻¹) ∉ A.nonunits := by
  have hxinv : x⁻¹ ∈ A.nonunits := A.inv_mem_nonunits_of_notMem hx
  have ha₂ : (W.map A.subtype).toAffine.a₂ ∈ A := SetLike.coe_mem W.a₂
  have ha₄ : (W.map A.subtype).toAffine.a₄ ∈ A := SetLike.coe_mem W.a₄
  have ha₆ : (W.map A.subtype).toAffine.a₆ ∈ A := SetLike.coe_mem W.a₆
  rw [add_assoc, add_assoc]
  refine A.one_add_notMem_nonunits (add_mem (A.mul_mem_nonunits ha₂ hxinv) (add_mem ?_ ?_))
  · exact A.mul_mem_nonunits ha₄ (A.nonunits.mul_mem hxinv hxinv)
  · exact A.mul_mem_nonunits ha₆ (A.nonunits.mul_mem (A.nonunits.mul_mem hxinv hxinv) hxinv)

theorem rhs_eq_cubic_mul {x : L} (hx : x ∉ A) :
    x ^ 3 + (W.map A.subtype).toAffine.a₂ * x ^ 2 + (W.map A.subtype).toAffine.a₄ * x
        + (W.map A.subtype).toAffine.a₆ =
      x ^ 3 * (1 + (W.map A.subtype).toAffine.a₂ * x⁻¹
        + (W.map A.subtype).toAffine.a₄ * (x⁻¹ * x⁻¹)
        + (W.map A.subtype).toAffine.a₆ * (x⁻¹ * x⁻¹ * x⁻¹)) := by
  have hx0 : x ≠ 0 := fun h => hx (h ▸ A.zero_mem)
  field_simp

theorem Y_ne_zero_of_X_notMem {x y : L} (h : (W.map A.subtype).toAffine.Equation x y)
    (hx : x ∉ A) : y ≠ 0 := by
  rintro rfl
  rw [equation_iff] at h
  have h0 : x ^ 3 + (W.map A.subtype).toAffine.a₂ * x ^ 2 + (W.map A.subtype).toAffine.a₄ * x
      + (W.map A.subtype).toAffine.a₆ = 0 := by linear_combination -h
  rw [rhs_eq_cubic_mul W hx] at h0
  rcases mul_eq_zero.mp h0 with h0 | h0
  · exact hx (pow_eq_zero_iff (n := 3) (by norm_num) |>.mp h0 ▸ A.zero_mem)
  · exact A.ne_zero_of_notMem_nonunits (cubic_inv_notMem_nonunits W hx) h0

theorem X_div_Y_mem_nonunits {x y : L} (h : (W.map A.subtype).toAffine.Equation x y)
    (hx : x ∉ A) : x / y ∈ A.nonunits := by
  have hy0 : y ≠ 0 := Y_ne_zero_of_X_notMem W h hx
  have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ A.zero_mem)

  by_contra hxy
  have hyx : y / x ∈ A := by
    have := A.inv_mem_of_notMem_nonunits hxy
    rwa [inv_div] at this
  have hxinv : x⁻¹ ∈ A := A.inv_mem_of_notMem hx
  rw [equation_iff] at h
  have key : x * (1 + (W.map A.subtype).toAffine.a₂ * x⁻¹
      + (W.map A.subtype).toAffine.a₄ * (x⁻¹ * x⁻¹)
      + (W.map A.subtype).toAffine.a₆ * (x⁻¹ * x⁻¹ * x⁻¹)) =
      (y / x) * (y / x) + (W.map A.subtype).toAffine.a₁ * (y / x)
        + (W.map A.subtype).toAffine.a₃ * (y / x) * x⁻¹ := by
    field_simp
    linear_combination -h
  refine hx ?_
  have hmem : x * (1 + (W.map A.subtype).toAffine.a₂ * x⁻¹
      + (W.map A.subtype).toAffine.a₄ * (x⁻¹ * x⁻¹)
      + (W.map A.subtype).toAffine.a₆ * (x⁻¹ * x⁻¹ * x⁻¹)) ∈ A := by
    rw [key]
    exact add_mem (add_mem (mul_mem hyx hyx) (mul_mem (SetLike.coe_mem W.a₁) hyx))
      (mul_mem (mul_mem (SetLike.coe_mem W.a₃) hyx) hxinv)
  have hcu := cubic_inv_notMem_nonunits W hx
  have := mul_mem hmem (A.inv_mem_of_notMem_nonunits hcu)
  rwa [mul_assoc, mul_inv_cancel₀ (A.ne_zero_of_notMem_nonunits hcu), mul_one] at this

theorem Y_notMem_of_X_notMem {x y : L} (h : (W.map A.subtype).toAffine.Equation x y)
    (hx : x ∉ A) : y ∉ A := by
  intro hy
  refine hx ?_
  have hmem : y * (x / y) ∈ A.nonunits := A.mul_mem_nonunits hy (X_div_Y_mem_nonunits W h hx)
  rw [mul_div_cancel₀ _ (Y_ne_zero_of_X_notMem W h hx)] at hmem
  exact A.nonunits_subset hmem

theorem X_cubed_div_Y_sq_notMem_nonunits {x y : L}
    (h : (W.map A.subtype).toAffine.Equation x y) (hx : x ∉ A) :
    x ^ 3 / y ^ 2 ∈ A ∧ x ^ 3 / y ^ 2 ∉ A.nonunits := by
  have hy0 : y ≠ 0 := Y_ne_zero_of_X_notMem W h hx
  have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ A.zero_mem)
  have hxy : x / y ∈ A.nonunits := X_div_Y_mem_nonunits W h hx
  have hyinv : y⁻¹ ∈ A.nonunits := A.inv_mem_nonunits_of_notMem (Y_notMem_of_X_notMem W h hx)
  have ha₁ : (W.map A.subtype).toAffine.a₁ ∈ A := SetLike.coe_mem W.a₁
  have ha₃ : (W.map A.subtype).toAffine.a₃ ∈ A := SetLike.coe_mem W.a₃

  rw [equation_iff] at h
  have hu : (1 + (W.map A.subtype).toAffine.a₁ * (x / y) + (W.map A.subtype).toAffine.a₃ * y⁻¹)
      ∉ A.nonunits := by
    rw [add_assoc]
    exact A.one_add_notMem_nonunits
      (add_mem (A.mul_mem_nonunits ha₁ hxy) (A.mul_mem_nonunits ha₃ hyinv))
  have hu' : (1 + (W.map A.subtype).toAffine.a₁ * (x / y) + (W.map A.subtype).toAffine.a₃ * y⁻¹)
      ∈ A := by
    refine add_mem (add_mem A.one_mem ?_) ?_
    · exact mul_mem ha₁ (A.nonunits_subset hxy)
    · exact mul_mem ha₃ (A.nonunits_subset hyinv)
  have hc := cubic_inv_notMem_nonunits W hx
  have hc' : (1 + (W.map A.subtype).toAffine.a₂ * x⁻¹
      + (W.map A.subtype).toAffine.a₄ * (x⁻¹ * x⁻¹)
      + (W.map A.subtype).toAffine.a₆ * (x⁻¹ * x⁻¹ * x⁻¹)) ∈ A := by
    have hxinv : x⁻¹ ∈ A := A.inv_mem_of_notMem hx
    refine add_mem (add_mem (add_mem A.one_mem ?_) ?_) ?_
    · exact mul_mem (SetLike.coe_mem W.a₂) hxinv
    · exact mul_mem (SetLike.coe_mem W.a₄) (mul_mem hxinv hxinv)
    · exact mul_mem (SetLike.coe_mem W.a₆) (mul_mem (mul_mem hxinv hxinv) hxinv)

  have key' : x ^ 3 / y ^ 2 = (1 + (W.map A.subtype).toAffine.a₁ * (x / y)
      + (W.map A.subtype).toAffine.a₃ * y⁻¹) * (1 + (W.map A.subtype).toAffine.a₂ * x⁻¹
        + (W.map A.subtype).toAffine.a₄ * (x⁻¹ * x⁻¹)
        + (W.map A.subtype).toAffine.a₆ * (x⁻¹ * x⁻¹ * x⁻¹))⁻¹ := by
    rw [eq_comm, mul_inv_eq_iff_eq_mul₀ (A.ne_zero_of_notMem_nonunits hc), div_mul_eq_mul_div,
      eq_div_iff (pow_ne_zero 2 hy0)]
    field_simp
    linear_combination h
  constructor
  · rw [key']
    exact mul_mem hu' (A.inv_mem_of_notMem_nonunits hc)
  · rw [key']
    exact A.mul_notMem_nonunits hu (A.inv_notMem_nonunits_of_notMem_nonunits hc' hc)

variable {W}

theorem inv_Y_div_mem_nonunits {x y τ : L} (h : (W.map A.subtype).toAffine.Equation x y)
    (hx : x ∉ A) (ht : (x / y) / τ ∈ A) : (1 / y) / τ ∈ A.nonunits := by
  have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ A.zero_mem)
  have hy0 : y ≠ 0 := Y_ne_zero_of_X_notMem W h hx
  have key : (1 / y) / τ = ((x / y) / τ) * x⁻¹ := by
    field_simp
  rw [key]
  exact A.mul_mem_nonunits ht (A.inv_mem_nonunits_of_notMem hx)

theorem inv_X_mul_div_mem_nonunits {x y τ : L} (h : (W.map A.subtype).toAffine.Equation x y)
    (hx : x ∉ A) (hτ0 : τ ≠ 0) (ht : (x / y) / τ ∈ A) : x⁻¹ / τ ∈ A.nonunits := by
  have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ A.zero_mem)
  have hy0 : y ≠ 0 := Y_ne_zero_of_X_notMem W h hx
  have key : x⁻¹ / τ = (y ^ 2 / x ^ 3) * ((x / y) / τ) * (x / y) := by
    field_simp
  rw [key]
  refine A.mul_mem_nonunits (mul_mem ?_ ht) (X_div_Y_mem_nonunits W h hx)
  rw [show y ^ 2 / x ^ 3 = (x ^ 3 / y ^ 2)⁻¹ by rw [inv_div]]
  exact A.inv_mem_of_notMem_nonunits (X_cubed_div_Y_sq_notMem_nonunits W h hx).2

theorem neg_formal_param_add {x y : L} (hy0 : y ≠ 0)
    (hy'0 : (W.map A.subtype).toAffine.negY x y ≠ 0) :
    (-(x / y)) + (-(x / (W.map A.subtype).toAffine.negY x y)) =
      (W.map A.subtype).toAffine.a₁ * (x / y) * (x / (W.map A.subtype).toAffine.negY x y)
        + (W.map A.subtype).toAffine.a₃ * (x / y)
            * (1 / (W.map A.subtype).toAffine.negY x y) := by
  have hsum : (W.map A.subtype).toAffine.negY x y
      = -y - (W.map A.subtype).toAffine.a₁ * x - (W.map A.subtype).toAffine.a₃ := rfl
  generalize hgen : (W.map A.subtype).toAffine.negY x y = y' at *
  rw [← sub_eq_zero]
  have key : (-(x / y)) + (-(x / y')) - ((W.map A.subtype).toAffine.a₁ * (x / y) * (x / y')
        + (W.map A.subtype).toAffine.a₃ * (x / y) * (1 / y'))
      = (-(x * y') - x * y - (W.map A.subtype).toAffine.a₁ * x * x
          - (W.map A.subtype).toAffine.a₃ * x) / (y * y') := by
    field_simp
    ring1
  rw [key, div_eq_zero_iff]
  left
  linear_combination (-x) * hsum

theorem neg_formal_param_estimate {x y τ : L}
    (h : (W.map A.subtype).toAffine.Equation x y) (hx : x ∉ A) (_hτ0 : τ ≠ 0)
    (ht : (x / y) / τ ∈ A) :
    ((-(x / y)) + (-(x / (W.map A.subtype).toAffine.negY x y))) / τ ∈ A.nonunits := by
  have h' : (W.map A.subtype).toAffine.Equation x ((W.map A.subtype).toAffine.negY x y) :=
    (Affine.equation_neg x y).mpr h
  have hy0 : y ≠ 0 := Y_ne_zero_of_X_notMem W h hx
  have hy'0 : (W.map A.subtype).toAffine.negY x y ≠ 0 := Y_ne_zero_of_X_notMem W h' hx
  rw [neg_formal_param_add hy0 hy'0, add_div]
  refine add_mem ?_ ?_
  · rw [show (W.map A.subtype).toAffine.a₁ * (x / y)
        * (x / (W.map A.subtype).toAffine.negY x y) / τ =
      (W.map A.subtype).toAffine.a₁ * ((x / y) / τ)
        * (x / (W.map A.subtype).toAffine.negY x y) by ring]
    exact A.mul_mem_nonunits (mul_mem (SetLike.coe_mem W.a₁) ht)
      (X_div_Y_mem_nonunits W h' hx)
  · rw [show (W.map A.subtype).toAffine.a₃ * (x / y)
        * (1 / (W.map A.subtype).toAffine.negY x y) / τ =
      (W.map A.subtype).toAffine.a₃ * (x / y)
        * ((1 / (W.map A.subtype).toAffine.negY x y) / τ) by ring]
    rw [show (W.map A.subtype).toAffine.a₃ * (x / y)
        * ((1 / (W.map A.subtype).toAffine.negY x y) / τ) =
      (W.map A.subtype).toAffine.a₃ * ((x / y) / τ)
        * (1 / (W.map A.subtype).toAffine.negY x y) by ring]
    rw [one_div]
    exact A.mul_mem_nonunits (mul_mem (SetLike.coe_mem W.a₃) ht)
      (A.inv_mem_nonunits_of_notMem (Y_notMem_of_X_notMem W h' hx))

section AdditionEstimate

variable [DecidableEq L]

theorem sub_eq_slope_mul_sub {x₁ y₁ x₂ y₂ : L}
    (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (W.map A.subtype).toAffine.negY x₂ y₂)) :
    y₁ - y₂ = (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ * (x₁ - x₂) := by
  by_cases hx : x₁ = x₂
  · have hy : y₁ = y₂ := Y_eq_of_Y_ne h₁ h₂ hx (fun h => hxy ⟨hx, h⟩)
    rw [hx, hy, sub_self, sub_self, mul_zero]
  · rw [slope_of_X_ne hx, div_mul_cancel₀ _ (sub_ne_zero.mpr hx)]

theorem vieta_addX {x₁ y₁ x₂ y₂ : L}
    (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (W.map A.subtype).toAffine.negY x₂ y₂)) :
    x₁ * x₂ + x₁ * ((W.map A.subtype).toAffine.addX x₁ x₂
        ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂))
      + x₂ * ((W.map A.subtype).toAffine.addX x₁ x₂
        ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂)) =
      2 * x₁ * ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) ^ 2
        + ((W.map A.subtype).toAffine.a₁ * x₁ - 2 * y₁ - (W.map A.subtype).toAffine.a₃)
            * ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂)
        + (-(W.map A.subtype).toAffine.a₁ * y₁ + (W.map A.subtype).toAffine.a₄) ∧
    x₁ * x₂ * ((W.map A.subtype).toAffine.addX x₁ x₂
        ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂)) =
      x₁ ^ 2 * ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) ^ 2
        - (2 * x₁ * y₁ + (W.map A.subtype).toAffine.a₃ * x₁)
            * ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂)
        + (y₁ ^ 2 + (W.map A.subtype).toAffine.a₃ * y₁ - (W.map A.subtype).toAffine.a₆) := by
  have key := (Affine.addPolynomial_eq (W' := (W.map A.subtype).toAffine) x₁ y₁
    ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂)).symm.trans
    (Affine.addPolynomial_slope h₁ h₂ hxy)
  rw [Cubic.prod_X_sub_C_eq, neg_inj, Cubic.toPoly_injective] at key
  have hc := congrArg Cubic.c key
  have hd := congrArg Cubic.d key
  simp only at hc hd
  exact ⟨by linear_combination -hc, by linear_combination hd⟩

omit [DecidableEq L] in

theorem secant_slope_identity {x₁ y₁ x₂ y₂ : L}
    (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂) :
    (y₁ - y₂) * (y₁^2*y₂^2 + (W.map A.subtype).toAffine.a₁*x₁*y₁*y₂^2
        - (W.map A.subtype).toAffine.a₂*x₁^2*y₂^2
        + (W.map A.subtype).toAffine.a₃*(y₁*y₂^2 + y₁^2*y₂)
        - (W.map A.subtype).toAffine.a₄*x₁*(y₂^2 + y₁*y₂)
        - (W.map A.subtype).toAffine.a₆*(y₂^2 + y₁*y₂ + y₁^2)) =
    (x₂*y₁ - x₁*y₂) * (-(W.map A.subtype).toAffine.a₁*y₁^2*y₂
        + (W.map A.subtype).toAffine.a₂*x₁*y₁*y₂ + (W.map A.subtype).toAffine.a₂*x₂*y₁^2
        + (W.map A.subtype).toAffine.a₄*y₁^2 + x₁^2*y₂^2 + x₁*x₂*y₁*y₂ + x₂^2*y₁^2) := by
  rw [Affine.equation_iff] at h₁ h₂
  set a1 := (W.map A.subtype).toAffine.a₁
  set a2 := (W.map A.subtype).toAffine.a₂
  set a3 := (W.map A.subtype).toAffine.a₃
  set a4 := (W.map A.subtype).toAffine.a₄
  set a6 := (W.map A.subtype).toAffine.a₆
  linear_combination (-a1^2*x₁*x₂*y₂ + a1*a2*x₁*x₂^2 - a1*a3*x₁*y₂ - a1*a3*x₂*y₂ + a1*a4*x₁*x₂
      + a1*a6*x₁ + a1*x₁*x₂^3 - a1*x₁*y₂^2 + a1*x₂*y₁*y₂ + a2*a3*x₂^2 - a2*x₂^2*y₁ - a3^2*y₂
      + a3*a4*x₂ + a3*a6 + a3*x₂^3 + a3*y₁*y₂ - a3*y₂^2 - a4*x₂*y₁ - a6*y₁ - x₂^3*y₁
      + y₁*y₂^2 - y₂^3) * h₁
    + (a1^2*x₁^2*y₁ - a1*a2*x₁^3 + 2*a1*a3*x₁*y₁ - a1*a4*x₁^2 - a1*a6*x₁ - a1*x₁^4
      - a2*a3*x₁^2 + a2*x₁^2*y₁ + a3^2*y₁ - a3*a4*x₁ - a3*a6 - a3*x₁^3 + a4*x₁*y₁ + a6*y₁
      + x₁^3*y₁) * h₂

omit [DecidableEq L] in

theorem tangent_slope_identity {x₁ y₁ : L}
    (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁) :
    -(3*x₁^2 + 2*(W.map A.subtype).toAffine.a₂*x₁ + (W.map A.subtype).toAffine.a₄
        - (W.map A.subtype).toAffine.a₁*y₁)
      * ((W.map A.subtype).toAffine.a₁*x₁*y₁ - (W.map A.subtype).toAffine.a₂*x₁^2
        + 2*(W.map A.subtype).toAffine.a₃*y₁ - 2*(W.map A.subtype).toAffine.a₄*x₁
        - 3*(W.map A.subtype).toAffine.a₆ + y₁^2) =
    (y₁*(2*y₁ + (W.map A.subtype).toAffine.a₁*x₁ + (W.map A.subtype).toAffine.a₃)
        - x₁*(3*x₁^2 + 2*(W.map A.subtype).toAffine.a₂*x₁ + (W.map A.subtype).toAffine.a₄
            - (W.map A.subtype).toAffine.a₁*y₁))
      * (3*x₁^2 + 2*(W.map A.subtype).toAffine.a₂*x₁ + (W.map A.subtype).toAffine.a₄
        - (W.map A.subtype).toAffine.a₁*y₁) := by
  rw [Affine.equation_iff] at h₁
  linear_combination (3*(W.map A.subtype).toAffine.a₁*y₁ - 6*(W.map A.subtype).toAffine.a₂*x₁
    - 3*(W.map A.subtype).toAffine.a₄ - 9*x₁^2) * h₁

omit [DecidableEq L] in

theorem tangent_intercept_identity {x₁ y₁ : L}
    (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁) :
    y₁*(2*y₁ + (W.map A.subtype).toAffine.a₁*x₁ + (W.map A.subtype).toAffine.a₃)
        - x₁*(3*x₁^2 + 2*(W.map A.subtype).toAffine.a₂*x₁ + (W.map A.subtype).toAffine.a₄
            - (W.map A.subtype).toAffine.a₁*y₁) =
      -(x₁^3 - (W.map A.subtype).toAffine.a₄*x₁ - 2*(W.map A.subtype).toAffine.a₆
        + (W.map A.subtype).toAffine.a₃*y₁) := by
  rw [Affine.equation_iff] at h₁
  linear_combination 2 * h₁

theorem slope_div_intercept_estimate {x₁ y₁ x₂ y₂ τ : L}
    (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂)
    (hx₁ : x₁ ∉ A) (hx₂ : x₂ ∉ A)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (W.map A.subtype).toAffine.negY x₂ y₂))
    (hτ : τ ∈ A.nonunits) (hτ0 : τ ≠ 0)
    (ht₁ : (x₁ / y₁) / τ ∈ A) (ht₂ : (x₂ / y₂) / τ ∈ A) :
    y₁ - (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ * x₁ ≠ 0 ∧
      ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂
          / (y₁ - (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ * x₁)) / τ ∈ A.nonunits ∧
      ((1 : L) / (y₁ - (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ * x₁)) / τ
        ∈ A.nonunits := by
  have ha1A : (W.map A.subtype).toAffine.a₁ ∈ A := SetLike.coe_mem W.a₁
  have ha2A : (W.map A.subtype).toAffine.a₂ ∈ A := SetLike.coe_mem W.a₂
  have ha3A : (W.map A.subtype).toAffine.a₃ ∈ A := SetLike.coe_mem W.a₃
  have ha4A : (W.map A.subtype).toAffine.a₄ ∈ A := SetLike.coe_mem W.a₄
  have ha6A : (W.map A.subtype).toAffine.a₆ ∈ A := SetLike.coe_mem W.a₆
  have hy₁0 : y₁ ≠ 0 := Y_ne_zero_of_X_notMem W h₁ hx₁
  have hy₂0 : y₂ ≠ 0 := Y_ne_zero_of_X_notMem W h₂ hx₂
  have hx₁0 : x₁ ≠ 0 := fun h0 => hx₁ (h0 ▸ A.zero_mem)
  have hT₁ : x₁ / y₁ ∈ A.nonunits := X_div_Y_mem_nonunits W h₁ hx₁
  have hT₂ : x₂ / y₂ ∈ A.nonunits := X_div_Y_mem_nonunits W h₂ hx₂
  have hT₁A : x₁ / y₁ ∈ A := A.nonunits_subset hT₁
  have hT₂A : x₂ / y₂ ∈ A := A.nonunits_subset hT₂
  have hs₁ : (1 / y₁) / τ ∈ A.nonunits := inv_Y_div_mem_nonunits h₁ hx₁ ht₁
  have hs₂ : (1 / y₂) / τ ∈ A.nonunits := inv_Y_div_mem_nonunits h₂ hx₂ ht₂
  have hs₁' : (1 : L) / y₁ ∈ A.nonunits := by
    rw [one_div]
    exact A.inv_mem_nonunits_of_notMem (Y_notMem_of_X_notMem W h₁ hx₁)
  have hs₂' : (1 : L) / y₂ ∈ A.nonunits := by
    rw [one_div]
    exact A.inv_mem_nonunits_of_notMem (Y_notMem_of_X_notMem W h₂ hx₂)
  have hs₁A : (1 : L) / y₁ ∈ A := A.nonunits_subset hs₁'
  have hs₂A : (1 : L) / y₂ ∈ A := A.nonunits_subset hs₂'

  have main : y₁ - (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ * x₁ ≠ 0 ∧
      ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂
        / (y₁ - (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ * x₁)) / τ ∈ A.nonunits := by
    by_cases hx : x₁ = x₂
    ·
      have hy : y₁ ≠ (W.map A.subtype).toAffine.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
      have hyy : y₁ = y₂ := Y_eq_of_Y_ne h₁ h₂ hx hy
      subst hx
      subst hyy
      have hψ0 : y₁ - (W.map A.subtype).toAffine.negY x₁ y₁ ≠ 0 := sub_ne_zero_of_ne hy
      have hxinv : x₁⁻¹ ∈ A.nonunits := A.inv_mem_nonunits_of_notMem hx₁
      have hxinvA : x₁⁻¹ ∈ A := A.nonunits_subset hxinv
      have hxτ : x₁⁻¹ / τ ∈ A.nonunits := inv_X_mul_div_mem_nonunits h₁ hx₁ hτ0 ht₁
      have hcube := X_cubed_div_Y_sq_notMem_nonunits W h₁ hx₁
      have hcubeinvA : (x₁ ^ 3 / y₁ ^ 2)⁻¹ ∈ A := A.inv_mem_of_notMem_nonunits hcube.2

      have hI_eq : (x₁ ^ 3 - (W.map A.subtype).toAffine.a₄ * x₁
            - 2 * (W.map A.subtype).toAffine.a₆ + (W.map A.subtype).toAffine.a₃ * y₁) / x₁ ^ 3
          = 1 + ((-((W.map A.subtype).toAffine.a₄ * x₁⁻¹)
              - ((W.map A.subtype).toAffine.a₆ + (W.map A.subtype).toAffine.a₆)
                * (x₁⁻¹ * x₁⁻¹)) * x₁⁻¹
            + ((W.map A.subtype).toAffine.a₃ * (x₁ ^ 3 / y₁ ^ 2)⁻¹) * (1 / y₁)) := by
        field_simp
        ring
      have hIm : ((-((W.map A.subtype).toAffine.a₄ * x₁⁻¹)
            - ((W.map A.subtype).toAffine.a₆ + (W.map A.subtype).toAffine.a₆)
              * (x₁⁻¹ * x₁⁻¹)) * x₁⁻¹
          + ((W.map A.subtype).toAffine.a₃ * (x₁ ^ 3 / y₁ ^ 2)⁻¹) * (1 / y₁)) ∈ A.nonunits :=
        add_mem
          (A.mul_mem_nonunits (sub_mem (neg_mem (mul_mem ha4A hxinvA))
            (mul_mem (add_mem ha6A ha6A) (mul_mem hxinvA hxinvA))) hxinv)
          (A.mul_mem_nonunits (mul_mem ha3A hcubeinvA) hs₁')
      have hInot : (x₁ ^ 3 - (W.map A.subtype).toAffine.a₄ * x₁
            - 2 * (W.map A.subtype).toAffine.a₆ + (W.map A.subtype).toAffine.a₃ * y₁) / x₁ ^ 3
          ∉ A.nonunits := by
        rw [hI_eq]
        exact A.one_add_notMem_nonunits hIm
      have hI0 : x₁ ^ 3 - (W.map A.subtype).toAffine.a₄ * x₁
          - 2 * (W.map A.subtype).toAffine.a₆ + (W.map A.subtype).toAffine.a₃ * y₁ ≠ 0 := by
        intro h0
        exact hInot (by rw [h0, zero_div]; exact A.nonunits.zero_mem)
      have hIinvA : ((x₁ ^ 3 - (W.map A.subtype).toAffine.a₄ * x₁
            - 2 * (W.map A.subtype).toAffine.a₆
            + (W.map A.subtype).toAffine.a₃ * y₁) / x₁ ^ 3)⁻¹ ∈ A :=
        A.inv_mem_of_notMem_nonunits hInot

      have hψ_eq : y₁ - (W.map A.subtype).toAffine.negY x₁ y₁
          = y₁ + y₁ + (W.map A.subtype).toAffine.a₁ * x₁ + (W.map A.subtype).toAffine.a₃ := by
        simp only [negY]
        ring
      have h₁' := h₁
      rw [Affine.equation_iff] at h₁'
      have hkey : (y₁ - (W.map A.subtype).toAffine.slope x₁ x₁ y₁ y₁ * x₁)
            * (y₁ - (W.map A.subtype).toAffine.negY x₁ y₁)
          = -(x₁ ^ 3 - (W.map A.subtype).toAffine.a₄ * x₁
            - 2 * (W.map A.subtype).toAffine.a₆ + (W.map A.subtype).toAffine.a₃ * y₁) := by
        rw [Affine.slope_of_Y_ne rfl hy, sub_mul, div_mul_eq_mul_div, div_mul_cancel₀ _ hψ0,
          hψ_eq]
        linear_combination (2 : L) * h₁'
      have hν0 : y₁ - (W.map A.subtype).toAffine.slope x₁ x₁ y₁ y₁ * x₁ ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hkey
        exact hI0 (by linear_combination hkey)
      refine ⟨hν0, ?_⟩

      have hslope_mul : (W.map A.subtype).toAffine.slope x₁ x₁ y₁ y₁
            * (y₁ - (W.map A.subtype).toAffine.negY x₁ y₁)
          = 3 * x₁ ^ 2 + 2 * (W.map A.subtype).toAffine.a₂ * x₁
            + (W.map A.subtype).toAffine.a₄ - (W.map A.subtype).toAffine.a₁ * y₁ := by
        rw [Affine.slope_of_Y_ne rfl hy, div_mul_cancel₀ _ hψ0]
      have hℓν : (W.map A.subtype).toAffine.slope x₁ x₁ y₁ y₁
            / (y₁ - (W.map A.subtype).toAffine.slope x₁ x₁ y₁ y₁ * x₁)
          = -(3 * x₁ ^ 2 + 2 * (W.map A.subtype).toAffine.a₂ * x₁
              + (W.map A.subtype).toAffine.a₄ - (W.map A.subtype).toAffine.a₁ * y₁)
            / (x₁ ^ 3 - (W.map A.subtype).toAffine.a₄ * x₁
              - 2 * (W.map A.subtype).toAffine.a₆ + (W.map A.subtype).toAffine.a₃ * y₁) := by
        rw [div_eq_div_iff hν0 hI0]
        linear_combination (-(y₁ - (W.map A.subtype).toAffine.slope x₁ x₁ y₁ y₁ * x₁))
          * hslope_mul + (W.map A.subtype).toAffine.slope x₁ x₁ y₁ y₁ * hkey
      rw [hℓν]

      have hsplit : (-(3 * x₁ ^ 2 + 2 * (W.map A.subtype).toAffine.a₂ * x₁
              + (W.map A.subtype).toAffine.a₄ - (W.map A.subtype).toAffine.a₁ * y₁)
            / (x₁ ^ 3 - (W.map A.subtype).toAffine.a₄ * x₁
              - 2 * (W.map A.subtype).toAffine.a₆
              + (W.map A.subtype).toAffine.a₃ * y₁)) / τ
          = ((x₁ ^ 3 - (W.map A.subtype).toAffine.a₄ * x₁
              - 2 * (W.map A.subtype).toAffine.a₆
              + (W.map A.subtype).toAffine.a₃ * y₁) / x₁ ^ 3)⁻¹
            * (-(((1 + 1 + 1) + ((W.map A.subtype).toAffine.a₂
                  + (W.map A.subtype).toAffine.a₂) * x₁⁻¹
                + (W.map A.subtype).toAffine.a₄ * (x₁⁻¹ * x₁⁻¹)) * (x₁⁻¹ / τ)
              - ((W.map A.subtype).toAffine.a₁ * (x₁ ^ 3 / y₁ ^ 2)⁻¹) * ((1 / y₁) / τ))) := by
        field_simp
        ring
      rw [hsplit]
      refine A.mul_mem_nonunits hIinvA (A.nonunits.neg_mem (sub_mem ?_ ?_))
      · exact A.mul_mem_nonunits
          (add_mem (add_mem (add_mem (add_mem A.one_mem A.one_mem) A.one_mem)
            (mul_mem (add_mem ha2A ha2A) hxinvA)) (mul_mem ha4A (mul_mem hxinvA hxinvA))) hxτ
      · exact A.mul_mem_nonunits (mul_mem ha1A hcubeinvA) hs₁
    ·
      have hxx0 : x₁ - x₂ ≠ 0 := sub_ne_zero_of_ne hx
      have hsec := secant_slope_identity (W := W) h₁ h₂

      have hU_eq : (y₁ ^ 2 * y₂ ^ 2 + (W.map A.subtype).toAffine.a₁ * x₁ * y₁ * y₂ ^ 2
            - (W.map A.subtype).toAffine.a₂ * x₁ ^ 2 * y₂ ^ 2
            + (W.map A.subtype).toAffine.a₃ * (y₁ * y₂ ^ 2 + y₁ ^ 2 * y₂)
            - (W.map A.subtype).toAffine.a₄ * x₁ * (y₂ ^ 2 + y₁ * y₂)
            - (W.map A.subtype).toAffine.a₆ * (y₂ ^ 2 + y₁ * y₂ + y₁ ^ 2)) / (y₁ ^ 2 * y₂ ^ 2)
          = 1 + (((W.map A.subtype).toAffine.a₁
                - (W.map A.subtype).toAffine.a₂ * (x₁ / y₁)
                - (W.map A.subtype).toAffine.a₄ * (1 / y₁)
                - (W.map A.subtype).toAffine.a₄ * (1 / y₂)) * (x₁ / y₁)
              + ((W.map A.subtype).toAffine.a₃ - (W.map A.subtype).toAffine.a₆ * (1 / y₁)
                - (W.map A.subtype).toAffine.a₆ * (1 / y₂)) * (1 / y₁)
              + ((W.map A.subtype).toAffine.a₃
                - (W.map A.subtype).toAffine.a₆ * (1 / y₂)) * (1 / y₂)) := by
        field_simp
        ring
      have hUm : (((W.map A.subtype).toAffine.a₁
              - (W.map A.subtype).toAffine.a₂ * (x₁ / y₁)
              - (W.map A.subtype).toAffine.a₄ * (1 / y₁)
              - (W.map A.subtype).toAffine.a₄ * (1 / y₂)) * (x₁ / y₁)
            + ((W.map A.subtype).toAffine.a₃ - (W.map A.subtype).toAffine.a₆ * (1 / y₁)
              - (W.map A.subtype).toAffine.a₆ * (1 / y₂)) * (1 / y₁)
            + ((W.map A.subtype).toAffine.a₃
              - (W.map A.subtype).toAffine.a₆ * (1 / y₂)) * (1 / y₂)) ∈ A.nonunits := by
        refine add_mem (add_mem (A.mul_mem_nonunits ?_ hT₁) (A.mul_mem_nonunits ?_ hs₁'))
          (A.mul_mem_nonunits ?_ hs₂')
        · exact sub_mem (sub_mem (sub_mem ha1A (mul_mem ha2A hT₁A)) (mul_mem ha4A hs₁A))
            (mul_mem ha4A hs₂A)
        · exact sub_mem (sub_mem ha3A (mul_mem ha6A hs₁A)) (mul_mem ha6A hs₂A)
        · exact sub_mem ha3A (mul_mem ha6A hs₂A)
      have hUnot : (y₁ ^ 2 * y₂ ^ 2 + (W.map A.subtype).toAffine.a₁ * x₁ * y₁ * y₂ ^ 2
            - (W.map A.subtype).toAffine.a₂ * x₁ ^ 2 * y₂ ^ 2
            + (W.map A.subtype).toAffine.a₃ * (y₁ * y₂ ^ 2 + y₁ ^ 2 * y₂)
            - (W.map A.subtype).toAffine.a₄ * x₁ * (y₂ ^ 2 + y₁ * y₂)
            - (W.map A.subtype).toAffine.a₆ * (y₂ ^ 2 + y₁ * y₂ + y₁ ^ 2)) / (y₁ ^ 2 * y₂ ^ 2)
          ∉ A.nonunits := by
        rw [hU_eq]
        exact A.one_add_notMem_nonunits hUm
      have hUA : (y₁ ^ 2 * y₂ ^ 2 + (W.map A.subtype).toAffine.a₁ * x₁ * y₁ * y₂ ^ 2
            - (W.map A.subtype).toAffine.a₂ * x₁ ^ 2 * y₂ ^ 2
            + (W.map A.subtype).toAffine.a₃ * (y₁ * y₂ ^ 2 + y₁ ^ 2 * y₂)
            - (W.map A.subtype).toAffine.a₄ * x₁ * (y₂ ^ 2 + y₁ * y₂)
            - (W.map A.subtype).toAffine.a₆ * (y₂ ^ 2 + y₁ * y₂ + y₁ ^ 2)) / (y₁ ^ 2 * y₂ ^ 2)
          ∈ A := by
        rw [hU_eq]
        exact add_mem A.one_mem (A.nonunits_subset hUm)
      have hUinvA : ((y₁ ^ 2 * y₂ ^ 2 + (W.map A.subtype).toAffine.a₁ * x₁ * y₁ * y₂ ^ 2
            - (W.map A.subtype).toAffine.a₂ * x₁ ^ 2 * y₂ ^ 2
            + (W.map A.subtype).toAffine.a₃ * (y₁ * y₂ ^ 2 + y₁ ^ 2 * y₂)
            - (W.map A.subtype).toAffine.a₄ * x₁ * (y₂ ^ 2 + y₁ * y₂)
            - (W.map A.subtype).toAffine.a₆ * (y₂ ^ 2 + y₁ * y₂ + y₁ ^ 2))
              / (y₁ ^ 2 * y₂ ^ 2))⁻¹ ∈ A :=
        A.inv_mem_of_notMem_nonunits hUnot
      have hU0 : y₁ ^ 2 * y₂ ^ 2 + (W.map A.subtype).toAffine.a₁ * x₁ * y₁ * y₂ ^ 2
            - (W.map A.subtype).toAffine.a₂ * x₁ ^ 2 * y₂ ^ 2
            + (W.map A.subtype).toAffine.a₃ * (y₁ * y₂ ^ 2 + y₁ ^ 2 * y₂)
            - (W.map A.subtype).toAffine.a₄ * x₁ * (y₂ ^ 2 + y₁ * y₂)
            - (W.map A.subtype).toAffine.a₆ * (y₂ ^ 2 + y₁ * y₂ + y₁ ^ 2) ≠ 0 := by
        intro h0
        exact hUnot (by rw [h0, zero_div]; exact A.nonunits.zero_mem)

      have hxy21 : x₁ * y₂ - x₂ * y₁ ≠ 0 := by
        intro h0
        have hUV : (y₁ - y₂) * (y₁ ^ 2 * y₂ ^ 2
              + (W.map A.subtype).toAffine.a₁ * x₁ * y₁ * y₂ ^ 2
              - (W.map A.subtype).toAffine.a₂ * x₁ ^ 2 * y₂ ^ 2
              + (W.map A.subtype).toAffine.a₃ * (y₁ * y₂ ^ 2 + y₁ ^ 2 * y₂)
              - (W.map A.subtype).toAffine.a₄ * x₁ * (y₂ ^ 2 + y₁ * y₂)
              - (W.map A.subtype).toAffine.a₆ * (y₂ ^ 2 + y₁ * y₂ + y₁ ^ 2)) = 0 := by
          rw [hsec]
          linear_combination (-(-((W.map A.subtype).toAffine.a₁ * y₁ ^ 2 * y₂)
            + (W.map A.subtype).toAffine.a₂ * x₁ * y₁ * y₂
            + (W.map A.subtype).toAffine.a₂ * x₂ * y₁ ^ 2
            + (W.map A.subtype).toAffine.a₄ * y₁ ^ 2 + x₁ ^ 2 * y₂ ^ 2
            + x₁ * x₂ * y₁ * y₂ + x₂ ^ 2 * y₁ ^ 2)) * h0
        rcases mul_eq_zero.mp hUV with h | h
        · refine hx ?_
          have hy12 : y₁ = y₂ := by linear_combination h
          have hxx : (x₁ - x₂) * y₁ = 0 := by linear_combination h0 + x₁ * hy12
          rcases mul_eq_zero.mp hxx with h' | h'
          · exact sub_eq_zero.mp h'
          · exact absurd h' hy₁0
        · exact hU0 h

      have hkey : (y₁ - (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ * x₁) * (x₁ - x₂)
          = x₁ * y₂ - x₂ * y₁ := by
        rw [Affine.slope_of_X_ne hx]
        field_simp
        ring
      have hν0 : y₁ - (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ * x₁ ≠ 0 := by
        intro h0
        exact hxy21 (by rw [← hkey, h0, zero_mul])
      refine ⟨hν0, ?_⟩

      have hℓν : (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂
            / (y₁ - (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ * x₁)
          = (y₁ - y₂) / (x₁ * y₂ - x₂ * y₁) := by
        rw [div_eq_div_iff hν0 hxy21, Affine.slope_of_X_ne hx]
        field_simp
        ring
      have hVU : (y₁ - y₂) / (x₁ * y₂ - x₂ * y₁)
          = -((-((W.map A.subtype).toAffine.a₁ * y₁ ^ 2 * y₂)
              + (W.map A.subtype).toAffine.a₂ * x₁ * y₁ * y₂
              + (W.map A.subtype).toAffine.a₂ * x₂ * y₁ ^ 2
              + (W.map A.subtype).toAffine.a₄ * y₁ ^ 2 + x₁ ^ 2 * y₂ ^ 2
              + x₁ * x₂ * y₁ * y₂ + x₂ ^ 2 * y₁ ^ 2)
            / (y₁ ^ 2 * y₂ ^ 2 + (W.map A.subtype).toAffine.a₁ * x₁ * y₁ * y₂ ^ 2
              - (W.map A.subtype).toAffine.a₂ * x₁ ^ 2 * y₂ ^ 2
              + (W.map A.subtype).toAffine.a₃ * (y₁ * y₂ ^ 2 + y₁ ^ 2 * y₂)
              - (W.map A.subtype).toAffine.a₄ * x₁ * (y₂ ^ 2 + y₁ * y₂)
              - (W.map A.subtype).toAffine.a₆ * (y₂ ^ 2 + y₁ * y₂ + y₁ ^ 2))) := by
        rw [← neg_div, div_eq_div_iff hxy21 hU0]
        linear_combination hsec

      have hVsplit : ((y₁ - y₂) / (x₁ * y₂ - x₂ * y₁)) / τ
          = ((y₁ ^ 2 * y₂ ^ 2 + (W.map A.subtype).toAffine.a₁ * x₁ * y₁ * y₂ ^ 2
              - (W.map A.subtype).toAffine.a₂ * x₁ ^ 2 * y₂ ^ 2
              + (W.map A.subtype).toAffine.a₃ * (y₁ * y₂ ^ 2 + y₁ ^ 2 * y₂)
              - (W.map A.subtype).toAffine.a₄ * x₁ * (y₂ ^ 2 + y₁ * y₂)
              - (W.map A.subtype).toAffine.a₆ * (y₂ ^ 2 + y₁ * y₂ + y₁ ^ 2))
                / (y₁ ^ 2 * y₂ ^ 2))⁻¹
            * (-((-(W.map A.subtype).toAffine.a₁
                  + (W.map A.subtype).toAffine.a₂ * (x₁ / y₁)
                  + (W.map A.subtype).toAffine.a₂ * (x₂ / y₂)
                  + (W.map A.subtype).toAffine.a₄ * (1 / y₂)) * ((1 / y₂) / τ)
                + ((x₁ / y₁) / τ) * (x₁ / y₁)
                + ((x₂ / y₂) / τ) * (x₁ / y₁ + x₂ / y₂))) := by
        rw [hVU]
        field_simp
        ring1
      rw [hℓν, hVsplit]
      refine A.mul_mem_nonunits hUinvA (A.nonunits.neg_mem
        (add_mem (add_mem (A.mul_mem_nonunits ?_ hs₂) (A.mul_mem_nonunits ht₁ hT₁))
          (A.mul_mem_nonunits ht₂ (add_mem hT₁ hT₂))))
      exact add_mem (add_mem (add_mem (neg_mem ha1A) (mul_mem ha2A hT₁A))
        (mul_mem ha2A hT₂A)) (mul_mem ha4A hs₂A)
  obtain ⟨hν0, hℓν⟩ := main
  refine ⟨hν0, hℓν, ?_⟩

  have hℓν' : (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂
      / (y₁ - (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ * x₁) ∈ A.nonunits := by
    rw [show (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂
        / (y₁ - (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ * x₁)
      = ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂
        / (y₁ - (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ * x₁)) / τ * τ from
      (div_mul_cancel₀ _ hτ0).symm]
    exact A.mul_mem_nonunits (A.nonunits_subset hℓν) hτ
  have hy₁0 : y₁ ≠ 0 := Y_ne_zero_of_X_notMem W h₁ hx₁
  have hline : ((1 : L) / (y₁ - (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ * x₁)) / τ
      = (1 / y₁) / τ + ((x₁ / y₁) / τ)
          * ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂
            / (y₁ - (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ * x₁)) := by
    field_simp
    ring1
  rw [hline]
  exact add_mem (inv_Y_div_mem_nonunits h₁ hx₁ ht₁) (A.mul_mem_nonunits ht₁ hℓν')

omit [DecidableEq L] in

theorem collinear_prod_sum {x₁ y₁ x₂ y₂ x₃ y₃ ℓ ν : L}
    (he₁ : x₁ + x₂ + x₃ = ℓ ^ 2 + (W.map A.subtype).toAffine.a₁ * ℓ
      - (W.map A.subtype).toAffine.a₂)
    (he₂ : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = 2 * x₁ * ℓ ^ 2
      + ((W.map A.subtype).toAffine.a₁ * x₁ - 2 * y₁ - (W.map A.subtype).toAffine.a₃) * ℓ
      + (-(W.map A.subtype).toAffine.a₁ * y₁ + (W.map A.subtype).toAffine.a₄))
    (he₃ : x₁ * x₂ * x₃ = x₁ ^ 2 * ℓ ^ 2
      - (2 * x₁ * y₁ + (W.map A.subtype).toAffine.a₃ * x₁) * ℓ
      + (y₁ ^ 2 + (W.map A.subtype).toAffine.a₃ * y₁ - (W.map A.subtype).toAffine.a₆))
    (hν : ν = y₁ - ℓ * x₁) (hy₂ : y₂ = ℓ * x₂ + ν) (hy₃ : y₃ = ℓ * x₃ + ν) :
    y₁ * y₂ * y₃ = ν ^ 3 - (W.map A.subtype).toAffine.a₂ * ℓ * ν ^ 2
        + (W.map A.subtype).toAffine.a₄ * ℓ ^ 2 * ν - (W.map A.subtype).toAffine.a₆ * ℓ ^ 3 ∧
      x₁ * y₂ * y₃ + x₂ * y₁ * y₃ + x₃ * y₁ * y₂
        = -((W.map A.subtype).toAffine.a₁ * ℓ * ν ^ 2)
          - (W.map A.subtype).toAffine.a₂ * ν ^ 2 + (W.map A.subtype).toAffine.a₃ * ℓ ^ 2 * ν
          + ((W.map A.subtype).toAffine.a₄ + (W.map A.subtype).toAffine.a₄) * ℓ * ν
          - ((W.map A.subtype).toAffine.a₆ + (W.map A.subtype).toAffine.a₆
            + (W.map A.subtype).toAffine.a₆) * ℓ ^ 2 := by
  subst hy₂ hy₃ hν
  constructor
  · linear_combination (ℓ * (y₁ - ℓ * x₁) ^ 2) * he₁ + (ℓ ^ 2 * (y₁ - ℓ * x₁)) * he₂
      + ℓ ^ 3 * he₃
  · linear_combination ((y₁ - ℓ * x₁) ^ 2) * he₁ + (2 * ℓ * (y₁ - ℓ * x₁)) * he₂
      + (3 * ℓ ^ 2) * he₃

theorem add_formal_param_estimate {x₁ y₁ x₂ y₂ τ : L}
    (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂)
    (hx₁ : x₁ ∉ A) (hx₂ : x₂ ∉ A)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (W.map A.subtype).toAffine.negY x₂ y₂))
    (hτ : τ ∈ A.nonunits) (hτ0 : τ ≠ 0)
    (ht₁ : (x₁ / y₁) / τ ∈ A) (ht₂ : (x₂ / y₂) / τ ∈ A) :
    (W.map A.subtype).toAffine.addX x₁ x₂ ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) ∉ A ∧
      ((-((W.map A.subtype).toAffine.addX x₁ x₂
            ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂)
          / (W.map A.subtype).toAffine.addY x₁ x₂ y₁
            ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂)))
        - (-(x₁ / y₁)) - (-(x₂ / y₂))) / τ ∈ A.nonunits := by
  have ha1A : (W.map A.subtype).toAffine.a₁ ∈ A := SetLike.coe_mem W.a₁
  have ha2A : (W.map A.subtype).toAffine.a₂ ∈ A := SetLike.coe_mem W.a₂
  have ha3A : (W.map A.subtype).toAffine.a₃ ∈ A := SetLike.coe_mem W.a₃
  have ha4A : (W.map A.subtype).toAffine.a₄ ∈ A := SetLike.coe_mem W.a₄
  have ha6A : (W.map A.subtype).toAffine.a₆ ∈ A := SetLike.coe_mem W.a₆
  have hy₁0 : y₁ ≠ 0 := Y_ne_zero_of_X_notMem W h₁ hx₁
  have hy₂0 : y₂ ≠ 0 := Y_ne_zero_of_X_notMem W h₂ hx₂

  obtain ⟨hν0, hℓντ, hsντ⟩ := slope_div_intercept_estimate h₁ h₂ hx₁ hx₂ hxy hτ hτ0 ht₁ ht₂

  obtain ⟨hv₂, hv₃⟩ := vieta_addX (W := W) h₁ h₂ hxy
  have hS := sub_eq_slope_mul_sub (W := W) h₁ h₂ hxy
  have hR : (W.map A.subtype).toAffine.Equation
      ((W.map A.subtype).toAffine.addX x₁ x₂ ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂))
      ((W.map A.subtype).toAffine.negAddY x₁ x₂ y₁
        ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂)) :=
    equation_negAdd h₁ h₂ hxy
  have he₁ : x₁ + x₂ + (W.map A.subtype).toAffine.addX x₁ x₂
        ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂)
      = ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) ^ 2
        + (W.map A.subtype).toAffine.a₁ * ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂)
        - (W.map A.subtype).toAffine.a₂ := by
    simp only [Affine.addX]
    ring
  have hy₃_line : (W.map A.subtype).toAffine.negAddY x₁ x₂ y₁
        ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂)
      = ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂)
          * ((W.map A.subtype).toAffine.addX x₁ x₂
            ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂))
        + (y₁ - (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ * x₁) := by
    simp only [Affine.negAddY]
    ring
  have hy₂_line : y₂ = ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) * x₂
      + (y₁ - (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ * x₁) := by
    linear_combination -hS
  obtain ⟨hD, hN⟩ := collinear_prod_sum he₁ hv₂ hv₃ rfl hy₂_line hy₃_line

  rw [show (W.map A.subtype).toAffine.addY x₁ x₂ y₁
        ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂)
      = (W.map A.subtype).toAffine.negY
          ((W.map A.subtype).toAffine.addX x₁ x₂
            ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂))
          ((W.map A.subtype).toAffine.negAddY x₁ x₂ y₁
            ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂)) from rfl]

  set ℓ := (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ with hℓ_def
  set x₃ := (W.map A.subtype).toAffine.addX x₁ x₂ ℓ with hx₃_def
  set y₃ := (W.map A.subtype).toAffine.negAddY x₁ x₂ y₁ ℓ with hy₃_def
  set ν := y₁ - ℓ * x₁ with hν_def

  have hℓν_m : ℓ / ν ∈ A.nonunits := by
    rw [show ℓ / ν = ℓ / ν / τ * τ from (div_mul_cancel₀ _ hτ0).symm]
    exact A.mul_mem_nonunits (A.nonunits_subset hℓντ) hτ
  have hℓν_A : ℓ / ν ∈ A := A.nonunits_subset hℓν_m
  have hsν_m : (1 : L) / ν ∈ A.nonunits := by
    rw [show (1 : L) / ν = (1 : L) / ν / τ * τ from (div_mul_cancel₀ _ hτ0).symm]
    exact A.mul_mem_nonunits (A.nonunits_subset hsντ) hτ

  have hu_eq : (ν ^ 3 - (W.map A.subtype).toAffine.a₂ * ℓ * ν ^ 2
        + (W.map A.subtype).toAffine.a₄ * ℓ ^ 2 * ν
        - (W.map A.subtype).toAffine.a₆ * ℓ ^ 3) / ν ^ 3
      = 1 + (-((W.map A.subtype).toAffine.a₂ * (ℓ / ν))
        + ((W.map A.subtype).toAffine.a₄ * (ℓ / ν)) * (ℓ / ν)
        - (((W.map A.subtype).toAffine.a₆ * (ℓ / ν)) * (ℓ / ν)) * (ℓ / ν)) := by
    field_simp
    ring
  have hum : (-((W.map A.subtype).toAffine.a₂ * (ℓ / ν))
      + ((W.map A.subtype).toAffine.a₄ * (ℓ / ν)) * (ℓ / ν)
      - (((W.map A.subtype).toAffine.a₆ * (ℓ / ν)) * (ℓ / ν)) * (ℓ / ν)) ∈ A.nonunits :=
    sub_mem (add_mem (A.nonunits.neg_mem (A.mul_mem_nonunits ha2A hℓν_m))
      (A.mul_mem_nonunits (mul_mem ha4A hℓν_A) hℓν_m))
      (A.mul_mem_nonunits (mul_mem (mul_mem ha6A hℓν_A) hℓν_A) hℓν_m)
  have hu_not : (ν ^ 3 - (W.map A.subtype).toAffine.a₂ * ℓ * ν ^ 2
        + (W.map A.subtype).toAffine.a₄ * ℓ ^ 2 * ν
        - (W.map A.subtype).toAffine.a₆ * ℓ ^ 3) / ν ^ 3 ∉ A.nonunits := by
    rw [hu_eq]
    exact A.one_add_notMem_nonunits hum
  have hu_invA : ((ν ^ 3 - (W.map A.subtype).toAffine.a₂ * ℓ * ν ^ 2
        + (W.map A.subtype).toAffine.a₄ * ℓ ^ 2 * ν
        - (W.map A.subtype).toAffine.a₆ * ℓ ^ 3) / ν ^ 3)⁻¹ ∈ A :=
    A.inv_mem_of_notMem_nonunits hu_not
  have hD0 : ν ^ 3 - (W.map A.subtype).toAffine.a₂ * ℓ * ν ^ 2
      + (W.map A.subtype).toAffine.a₄ * ℓ ^ 2 * ν
      - (W.map A.subtype).toAffine.a₆ * ℓ ^ 3 ≠ 0 := by
    intro h0
    exact hu_not (by rw [h0, zero_div]; exact A.nonunits.zero_mem)
  have hy₃0 : y₃ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hD
    exact hD0 hD.symm

  have hsum_frac : -(x₃ / y₃) + -(x₁ / y₁) + -(x₂ / y₂)
      = -((x₁ * y₂ * y₃ + x₂ * y₁ * y₃ + x₃ * y₁ * y₂) / (y₁ * y₂ * y₃)) := by
    field_simp
    ring
  have hsum_split : (-(x₃ / y₃) + -(x₁ / y₁) + -(x₂ / y₂)) / τ
      = ((ν ^ 3 - (W.map A.subtype).toAffine.a₂ * ℓ * ν ^ 2
          + (W.map A.subtype).toAffine.a₄ * ℓ ^ 2 * ν
          - (W.map A.subtype).toAffine.a₆ * ℓ ^ 3) / ν ^ 3)⁻¹
        * (((W.map A.subtype).toAffine.a₁ - (W.map A.subtype).toAffine.a₃ * (ℓ / ν))
            * (ℓ / ν / τ)
          + ((W.map A.subtype).toAffine.a₂
              - ((W.map A.subtype).toAffine.a₄ + (W.map A.subtype).toAffine.a₄) * (ℓ / ν)
              + (((W.map A.subtype).toAffine.a₆ + (W.map A.subtype).toAffine.a₆
                + (W.map A.subtype).toAffine.a₆) * (ℓ / ν)) * (ℓ / ν))
            * ((1 : L) / ν / τ)) := by
    rw [hsum_frac, hN, hD]
    field_simp
    ring
  have hsum_mem : (-(x₃ / y₃) + -(x₁ / y₁) + -(x₂ / y₂)) / τ ∈ A.nonunits := by
    rw [hsum_split]
    refine A.mul_mem_nonunits hu_invA (add_mem (A.mul_mem_nonunits ?_ hℓντ)
      (A.mul_mem_nonunits ?_ hsντ))
    · exact sub_mem ha1A (mul_mem ha3A hℓν_A)
    · exact add_mem (sub_mem ha2A (mul_mem (add_mem ha4A ha4A) hℓν_A))
        (mul_mem (mul_mem (add_mem (add_mem ha6A ha6A) ha6A) hℓν_A) hℓν_A)

  have hT₃τ : (x₃ / y₃) / τ ∈ A := by
    have key : (x₃ / y₃) / τ = -((-(x₃ / y₃) + -(x₁ / y₁) + -(x₂ / y₂)) / τ)
        + (-((x₁ / y₁) / τ)) + (-((x₂ / y₂) / τ)) := by
      ring
    rw [key]
    exact add_mem (add_mem (neg_mem (A.nonunits_subset hsum_mem)) (neg_mem ht₁)) (neg_mem ht₂)
  have hT₃ : x₃ / y₃ ∈ A.nonunits := by
    rw [show x₃ / y₃ = x₃ / y₃ / τ * τ from (div_mul_cancel₀ _ hτ0).symm]
    exact A.mul_mem_nonunits hT₃τ hτ

  have hy₃inv : y₃⁻¹ ∈ A.nonunits := by
    have hν_alt : ν = y₃ - ℓ * x₃ := by linear_combination -hy₃_line
    have expand : (1 : L) / ν - ℓ / ν * (x₃ / y₃) = (y₃ - ℓ * x₃) / (ν * y₃) := by
      field_simp
    have key : y₃⁻¹ = (1 : L) / ν - ℓ / ν * (x₃ / y₃) := by
      rw [expand, ← hν_alt, eq_div_iff (mul_ne_zero hν0 hy₃0), mul_comm ν y₃, ← mul_assoc,
        inv_mul_cancel₀ hy₃0, one_mul]
    rw [key]
    exact sub_mem hsν_m (A.mul_mem_nonunits hℓν_A hT₃)
  have hy₃notA : y₃ ∉ A := (A.inv_mem_nonunits_iff.mp hy₃inv).resolve_left hy₃0
  have hx₃notA : x₃ ∉ A := fun hmem => hy₃notA (Y_mem_of_X_mem W hR hmem)
  refine ⟨hx₃notA, ?_⟩

  have hneg := neg_formal_param_estimate (W := W) hR hx₃notA hτ0 hT₃τ

  have key : (-(x₃ / (W.map A.subtype).toAffine.negY x₃ y₃) - -(x₁ / y₁) - -(x₂ / y₂)) / τ
      = (-(x₃ / y₃) + -(x₃ / (W.map A.subtype).toAffine.negY x₃ y₃)) / τ
        - (-(x₃ / y₃) + -(x₁ / y₁) + -(x₂ / y₂)) / τ := by
    ring
  rw [key]
  exact sub_mem hneg hsum_mem

end AdditionEstimate
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_reductionKernel_absorbing_inertia.WeierstrassCurve"

end Affine
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_reductionKernel_absorbing_inertia.WeierstrassCurve"

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_reductionKernel_absorbing_inertia.WeierstrassCurve"

namespace ValuationSubring
p2m_export "ValuationSubring" "subtype coe_mem_nonunits_iff neg_mem inertiaSubgroup toSubring ext mem_nonunits_iff_or zero_mem nonunits mem_nonunits_iff smul_mem_pointwise_smul inv_mem_nonunits_iff mul_mem one_mem mem_or_inv_mem nonunits_subset add_mem decompositionSubgroup valuation_le_one_iff algebra valuation subtype_injective inertiaSubgroupIn smul_mem_of_mem_decompositionSubgroup residue_smul_eq_of_mem_inertiaSubgroup"
p2m_open "ValuationSubring"

variable {L : Type*} [Field L] (A : ValuationSubring L)

private theorem _root_.ValuationSubring.mem_inertiaSubgroupIn_iff (K : Type*) [Field K] [Algebra K L] (σ : L ≃ₐ[K] L) :
    σ ∈ A.inertiaSubgroupIn K ↔
      ∃ hσ : σ ∈ A.decompositionSubgroup K,
        (⟨σ, hσ⟩ : A.decompositionSubgroup K) ∈ A.inertiaSubgroup K := by
  constructor
  · intro h
    obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.mp h
    exact ⟨τ.2, hτ⟩
  · rintro ⟨hσ, hI⟩
    exact Subgroup.mem_map.mpr ⟨⟨σ, hσ⟩, hI, rfl⟩

p2m_export "ValuationSubring" "mem_inertiaSubgroupIn_iff"

private theorem _root_.ValuationSubring.smul_sub_mem_nonunits_of_mem_inertiaSubgroup {K : Type*} [Field K] [Algebra K L]
    {σ : L ≃ₐ[K] L} (hσ : σ ∈ A.decompositionSubgroup K)
    (hσI : (⟨σ, hσ⟩ : A.decompositionSubgroup K) ∈ A.inertiaSubgroup K) {a : L} (ha : a ∈ A) :
    σ a - a ∈ A.nonunits := by
  have hσa : σ a ∈ A := A.smul_mem_of_mem_decompositionSubgroup K hσ ha
  have hres := A.residue_smul_eq_of_mem_inertiaSubgroup hσ hσI ⟨a, ha⟩
  have hres' : IsLocalRing.residue A ⟨σ a, hσa⟩ = IsLocalRing.residue A ⟨a, ha⟩ := hres
  have h0 : IsLocalRing.residue A (⟨σ a, hσa⟩ - ⟨a, ha⟩) = 0 := by
    rw [map_sub, hres', sub_self]
  have := (A.coe_mem_nonunits_iff_residue_eq_zero _).mpr h0
  simpa using this

p2m_export "ValuationSubring" "smul_sub_mem_nonunits_of_mem_inertiaSubgroup"
end ValuationSubring
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_reductionKernel_absorbing_inertia.WeierstrassCurve"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.negY Affine.slope_of_X_ne Affine.equation_neg a₃ Affine.Point.add_of_Y_eq Affine.addPolynomial_slope a₁ map Affine.equation_iff_nonsingular_of_Δ_ne_zero Affine.nonsingular_iff a₄ a₂ a₆ Affine.Point.some Affine.Point.some.inj Affine.negAddY reduction Affine.negY_negY toAffine Affine.slope_of_Y_ne Affine.Point Affine.addX Affine.Point.add_some Affine.nonsingular_neg map_Δ Affine.addPolynomial_eq Affine.Point.map Affine.Point.some_ne_zero Δ Affine.map_negY Affine.Y_eq_of_X_eq Affine.equation_iff Affine.Point.neg_some"
p2m_open "WeierstrassCurve"

p2m_open "ValuationSubring P2MW.S_WeierstrassCurve_exists_reductionKernel_absorbing_inertia.ValuationSubring"

variable {L : Type*} [Field L] {A : ValuationSubring L} (W : WeierstrassCurve A)

section ReductionKernel

variable [DecidableEq L]

p2m_open_scoped "WeierstrassCurve.Affine" in

theorem Affine.addX_notMem_of_notMem_of_notMem {x₁ y₁ x₂ y₂ : L}
    (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂) (hx₁ : x₁ ∉ A) (hx₂ : x₂ ∉ A)
    (hPQ : ¬(x₁ = x₂ ∧ y₁ = (W.map A.subtype).toAffine.negY x₂ y₂)) :
    (W.map A.subtype).toAffine.addX x₁ x₂ ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) ∉ A := by
  have hy₁0 : y₁ ≠ 0 := Affine.Y_ne_zero_of_X_notMem W h₁ hx₁
  have hy₂0 : y₂ ≠ 0 := Affine.Y_ne_zero_of_X_notMem W h₂ hx₂
  have hx₁0 : x₁ ≠ 0 := fun h => hx₁ (h ▸ A.zero_mem)
  have hx₂0 : x₂ ≠ 0 := fun h => hx₂ (h ▸ A.zero_mem)
  have ht₁m : x₁ / y₁ ∈ A.nonunits := Affine.X_div_Y_mem_nonunits W h₁ hx₁
  have ht₂m : x₂ / y₂ ∈ A.nonunits := Affine.X_div_Y_mem_nonunits W h₂ hx₂
  have ht₁0 : x₁ / y₁ ≠ 0 := div_ne_zero hx₁0 hy₁0
  have ht₂0 : x₂ / y₂ ≠ 0 := div_ne_zero hx₂0 hy₂0
  rcases A.mem_or_inv_mem ((x₁ / y₁) / (x₂ / y₂)) with hcase | hcase
  ·
    refine (Affine.add_formal_param_estimate h₁ h₂ hx₁ hx₂ hPQ ht₂m ht₂0 hcase ?_).1
    rw [div_self ht₂0]
    exact A.one_mem
  ·
    rw [show ((x₁ / y₁) / (x₂ / y₂))⁻¹ = (x₂ / y₂) / (x₁ / y₁) by rw [inv_div]] at hcase
    refine (Affine.add_formal_param_estimate h₁ h₂ hx₁ hx₂ hPQ ht₁m ht₁0 ?_ hcase).1
    rw [div_self ht₁0]
    exact A.one_mem

def reductionKernel : AddSubgroup (W.map A.subtype).toAffine.Point where
  carrier := {Q | ∀ (x y : L) (h : (W.map A.subtype).toAffine.Nonsingular x y),
    Q = .some x y h → x ∉ A}
  zero_mem' := by
    intro x y h h0
    exact absurd h0.symm (Affine.Point.some_ne_zero h)
  add_mem' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) hP hQ
    · intro x y h hsum
      exact absurd (by rw [← hsum]; rfl) (Affine.Point.some_ne_zero h)
    · intro x y h hsum
      exact hQ x y h hsum
    · intro x y h hsum
      exact hP x y h hsum
    · have hx₁ : x₁ ∉ A := hP x₁ y₁ h₁ rfl
      have hx₂ : x₂ ∉ A := hQ x₂ y₂ h₂ rfl
      by_cases hPQ : x₁ = x₂ ∧ y₁ = (W.map A.subtype).toAffine.negY x₂ y₂
      · intro x y h hsum
        rw [Affine.Point.add_of_Y_eq hPQ.1 hPQ.2] at hsum
        exact absurd hsum (Affine.Point.some_ne_zero h).symm
      · intro x y h hsum
        rw [Affine.Point.add_some hPQ] at hsum
        obtain ⟨rfl, -⟩ := Affine.Point.some.inj hsum
        exact Affine.addX_notMem_of_notMem_of_notMem W h₁.1 h₂.1 hx₁ hx₂ hPQ
  neg_mem' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) hP
    · intro x y h hneg
      exact absurd (by rw [← hneg]; rfl) (Affine.Point.some_ne_zero h)
    · intro x y h hneg
      rw [Affine.Point.neg_some] at hneg
      obtain ⟨rfl, -⟩ := Affine.Point.some.inj hneg
      exact hP x₁ y₁ h₁ rfl

variable {W}

theorem mem_reductionKernel_iff (Q : (W.map A.subtype).toAffine.Point) :
    Q ∈ reductionKernel W ↔ ∀ (x y : L) (h : (W.map A.subtype).toAffine.Nonsingular x y),
      Q = .some x y h → x ∉ A :=
  Iff.rfl

theorem zero_mem_reductionKernel : (0 : (W.map A.subtype).toAffine.Point) ∈ reductionKernel W :=
  (reductionKernel W).zero_mem

theorem some_mem_reductionKernel_iff {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y) :
    (.some x y h : (W.map A.subtype).toAffine.Point) ∈ reductionKernel W ↔ x ∉ A := by
  constructor
  · intro hQ
    exact hQ x y h rfl
  · intro hx x' y' h' heq
    obtain ⟨rfl, -⟩ := Affine.Point.some.inj heq
    exact hx

theorem some_smul_add_neg_some_mem_reductionKernel (hΔ : (W.map (IsLocalRing.residue A)).Δ ≠ 0)
    {K : Type*} [Field K] [Algebra K L] {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.decompositionSubgroup K)
    (hσI : (⟨σ, hσ⟩ : A.decompositionSubgroup K) ∈ A.inertiaSubgroup K)
    {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y)
    (h' : (W.map A.subtype).toAffine.Nonsingular (σ x) (σ y)) :
    (.some (σ x) (σ y) h' : (W.map A.subtype).toAffine.Point) + -(.some x y h) ∈
      reductionKernel W := by
  by_cases hx : x ∈ A
  ·
    have hy : y ∈ A := Affine.Y_mem_of_X_mem W h.1 hx
    have hσx : σ x ∈ A := A.smul_mem_of_mem_decompositionSubgroup K hσ hx
    have hxx : σ x - x ∈ A.nonunits := A.smul_sub_mem_nonunits_of_mem_inertiaSubgroup hσ hσI hx
    have hyy : σ y - y ∈ A.nonunits := A.smul_sub_mem_nonunits_of_mem_inertiaSubgroup hσ hσI hy
    rw [Affine.Point.neg_some]
    have hneg : (W.map A.subtype).toAffine.Nonsingular x ((W.map A.subtype).toAffine.negY x y) :=
      (Affine.nonsingular_neg x y).mpr h
    by_cases hPQ : σ x = x ∧ σ y = (W.map A.subtype).toAffine.negY x
        ((W.map A.subtype).toAffine.negY x y)
    · rw [Affine.Point.add_of_Y_eq (h₂ := hneg) hPQ.1 hPQ.2]
      exact zero_mem_reductionKernel
    · rw [Affine.Point.add_some (h₁ := h') (h₂ := hneg) hPQ, some_mem_reductionKernel_iff]
      refine Affine.addX_notMem_of_sub_mem_nonunits W hΔ h'.1 hneg.1 hσx hx hPQ hxx ?_
      rwa [Affine.negY_negY]
  ·
    have hσx : σ x ∉ A := fun hmem => hx (by
      simpa using A.smul_mem_of_mem_decompositionSubgroup K (inv_mem hσ) hmem)
    exact (reductionKernel W).add_mem ((some_mem_reductionKernel_iff h').mpr hσx)
      ((reductionKernel W).neg_mem ((some_mem_reductionKernel_iff h).mpr hx))

end ReductionKernel
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_reductionKernel_absorbing_inertia.WeierstrassCurve"

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_reductionKernel_absorbing_inertia.WeierstrassCurve"

section Bridge

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_exists_reductionKernel_absorbing_inertia.WeierstrassCurve WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_exists_reductionKernel_absorbing_inertia.WeierstrassCurve.Affine WeierstrassCurve.Affine.Point"

namespace WeierstrassCurve p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.negY Affine.slope_of_X_ne Affine.equation_neg a₃ Affine.Point.add_of_Y_eq Affine.addPolynomial_slope a₁ map Affine.equation_iff_nonsingular_of_Δ_ne_zero Affine.nonsingular_iff a₄ a₂ a₆ Affine.Point.some Affine.Point.some.inj Affine.negAddY reduction Affine.negY_negY toAffine Affine.slope_of_Y_ne Affine.Point Affine.addX Affine.Point.add_some Affine.nonsingular_neg map_Δ Affine.addPolynomial_eq Affine.Point.map Affine.Point.some_ne_zero Δ Affine.map_negY Affine.Y_eq_of_X_eq Affine.equation_iff Affine.Point.neg_some" end WeierstrassCurve
namespace WeierstrassCurve
p2m_open_scoped "WeierstrassCurve" in

private noncomputable def _root_.WeierstrassCurve.integralModelAt (W : WeierstrassCurve ℚ)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (h₁ : algebraMap ℚ (AlgebraicClosure ℚ) W.a₁ ∈ A)
    (h₂ : algebraMap ℚ (AlgebraicClosure ℚ) W.a₂ ∈ A)
    (h₃ : algebraMap ℚ (AlgebraicClosure ℚ) W.a₃ ∈ A)
    (h₄ : algebraMap ℚ (AlgebraicClosure ℚ) W.a₄ ∈ A)
    (h₆ : algebraMap ℚ (AlgebraicClosure ℚ) W.a₆ ∈ A) : WeierstrassCurve A :=
  ⟨⟨_, h₁⟩, ⟨_, h₂⟩, ⟨_, h₃⟩, ⟨_, h₄⟩, ⟨_, h₆⟩⟩

end WeierstrassCurve
p2m_export "" "WeierstrassCurve.integralModelAt"
namespace WeierstrassCurve
p2m_open_scoped "WeierstrassCurve" in
private theorem _root_.WeierstrassCurve.integralModelAt_map_subtype (W : WeierstrassCurve ℚ)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (h₁ : algebraMap ℚ (AlgebraicClosure ℚ) W.a₁ ∈ A)
    (h₂ : algebraMap ℚ (AlgebraicClosure ℚ) W.a₂ ∈ A)
    (h₃ : algebraMap ℚ (AlgebraicClosure ℚ) W.a₃ ∈ A)
    (h₄ : algebraMap ℚ (AlgebraicClosure ℚ) W.a₄ ∈ A)
    (h₆ : algebraMap ℚ (AlgebraicClosure ℚ) W.a₆ ∈ A) :
    (W.integralModelAt A h₁ h₂ h₃ h₄ h₆).map A.subtype = W⁄(AlgebraicClosure ℚ) :=
  rfl

end WeierstrassCurve
p2m_export "" "WeierstrassCurve.integralModelAt_map_subtype"

theorem solution (W : WeierstrassCurve ℚ) [W.IsElliptic] (A : ValuationSubring (AlgebraicClosure ℚ)) (h₁ : algebraMap ℚ (AlgebraicClosure ℚ) W.a₁ ∈ A) (h₂ : algebraMap ℚ (AlgebraicClosure ℚ) W.a₂ ∈ A) (h₃ : algebraMap ℚ (AlgebraicClosure ℚ) W.a₃ ∈ A) (h₄ : algebraMap ℚ (AlgebraicClosure ℚ) W.a₄ ∈ A) (h₆ : algebraMap ℚ (AlgebraicClosure ℚ) W.a₆ ∈ A) (hΔ : (algebraMap ℚ (AlgebraicClosure ℚ) W.Δ)⁻¹ ∈ A) : ∃ H : AddSubgroup (W⁄(AlgebraicClosure ℚ)).Point, (∀ Q : (W⁄(AlgebraicClosure ℚ)).Point, Q ∈ H ↔ ∀ (x y : AlgebraicClosure ℚ) (h : (W⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y), Q = Point.some x y h → x ∉ A) ∧ ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ Q : (W⁄(AlgebraicClosure ℚ)).Point, σ • Q - Q ∈ H := by
  set WA := W.integralModelAt A h₁ h₂ h₃ h₄ h₆ with hWA

  have hΔL : (WA.Δ : AlgebraicClosure ℚ) = algebraMap ℚ (AlgebraicClosure ℚ) W.Δ := by
    rw [show (WA.Δ : AlgebraicClosure ℚ) = (WA.map A.subtype).Δ from (WA.map_Δ A.subtype).symm,
      W.integralModelAt_map_subtype A h₁ h₂ h₃ h₄ h₆]
    exact W.map_Δ (algebraMap ℚ (AlgebraicClosure ℚ))
  have hΔ0 : algebraMap ℚ (AlgebraicClosure ℚ) W.Δ ≠ 0 := by
    rw [map_ne_zero_iff _ (algebraMap ℚ (AlgebraicClosure ℚ)).injective]
    exact W.isUnit_Δ.ne_zero
  have hunit : IsUnit WA.Δ := by
    refine ⟨⟨WA.Δ, ⟨(algebraMap ℚ (AlgebraicClosure ℚ) W.Δ)⁻¹, hΔ⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      push_cast
      rw [hΔL]
      exact mul_inv_cancel₀ hΔ0
    · apply Subtype.ext
      push_cast
      rw [hΔL]
      exact inv_mul_cancel₀ hΔ0
  have hΔ' : (WA.map (IsLocalRing.residue A)).Δ ≠ 0 := (map_residue_Δ_ne_zero_iff WA).mpr hunit
  refine ⟨reductionKernel WA, fun Q => Iff.rfl, ?_⟩
  intro σ hσmem Q
  obtain ⟨hσ, hσI⟩ := (A.mem_inertiaSubgroupIn_iff ℚ σ).mp hσmem
  rw [sub_eq_add_neg]
  rcases Q with _ | ⟨x, y, h⟩
  · exact zero_mem_reductionKernel
  · exact some_smul_add_neg_some_mem_reductionKernel hΔ' hσ hσI h _

end Bridge
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_reductionKernel_absorbing_inertia.WeierstrassCurve"

end S_WeierstrassCurve_exists_reductionKernel_absorbing_inertia
end P2MW
export P2MW.S_WeierstrassCurve_exists_reductionKernel_absorbing_inertia (solution)
