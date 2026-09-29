-- Prove2me | solution 1 for WeierstrassCurve.inZeroComponentAt_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/a7096ee9-efe9-5c48-8245-ab9bd120ab2d

import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.CharP.Basic
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_inZeroComponentAt_smul

set_option autoImplicit false

open IsLocalRing

namespace ValuationSubring
p2m_export "ValuationSubring" "subtype coe_mem_nonunits_iff neg_mem inertiaSubgroup toSubring ext mem_nonunits_iff_or zero_mem nonunits mem_nonunits_iff smul_mem_pointwise_smul inv_mem_nonunits_iff mem_top mul_mem one_mem mem_or_inv_mem nonunits_subset add_mem decompositionSubgroup valuation_le_one_iff algebra valuation subtype_injective LiesOverPrime smul_mem_of_mem_decompositionSubgroup residue_smul_eq_of_mem_inertiaSubgroup"
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
p2m_export "WeierstrassCurve" "Affine Affine.negY Affine.Y_eq_of_Y_ne Affine.slope_of_X_ne Affine.equation_neg a₃ Affine.Point.add_of_Y_eq Affine.addPolynomial_slope a₁ map Affine.equation_iff_nonsingular_of_Δ_ne_zero Affine.nonsingular_iff a₄ a₂ a₆ Affine.Point.some Affine.Point.some.injEq Affine.Point.neg_zero Affine.negAddY Affine.Point.zero_def reduction Affine.map_addY Affine.negY_negY Affine.map_addX Affine.nonsingular_add toAffine Affine.slope_of_Y_ne Affine.Point Affine.addX Affine.Point.add_some Affine.nonsingular_neg map_Δ Affine.addPolynomial_eq Affine.Point.map Affine.Point.some_ne_zero Δ Affine.map_negY Affine.Y_eq_of_X_eq Affine.equation_iff Affine.map_nonsingular Affine.Point.neg_some j InZeroComponentAt"
p2m_open "WeierstrassCurve"

variable {L : Type*} [Field L] {A : ValuationSubring L}

private lemma some_congr {R : Type*} [CommRing R] {V : Affine R} {x₁ x₂ y₁ y₂ : R}
    (hx : x₁ = x₂) (hy : y₁ = y₂) (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

variable (W : WeierstrassCurve A)

namespace Affine p2m_export "WeierstrassCurve.Affine" "Equation negY Y_eq_of_Y_ne slope_of_X_ne equation_neg Point.add_of_Y_eq addPolynomial_slope equation_iff_nonsingular_of_Δ_ne_zero slope nonsingular_iff map map_equation Point.some Point.some.injEq Point.neg_zero Nonsingular negAddY Point.zero_def map_addY negY_negY map_addX nonsingular_add equation_negAdd slope_of_Y_ne Point addX Point.add_some nonsingular_neg addPolynomial_eq Point.map Point.some_ne_zero map_negY addY Y_eq_of_X_eq equation_iff map_nonsingular polynomial Point.neg_some" end Affine
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

noncomputable def reducePointVS (hΔ : (W.map (residue A)).Δ ≠ 0) :
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
lemma reducePointVS_zero : reducePointVS hΔ (0 : (W.map A.subtype).toAffine.Point) = 0 :=
  rfl

lemma reducePointVS_some_of_mem {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y)
    (hx : x ∈ A) :
    reducePointVS hΔ (.some x y h) =
      .some (residue A ⟨x, hx⟩) (residue A ⟨y, Affine.Y_mem_of_X_mem W h.1 hx⟩)
        (Affine.nonsingular_residue W hΔ h.1) := by
  simp only [reducePointVS]
  exact dif_pos hx

lemma reducePointVS_some_of_notMem {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y)
    (hx : x ∉ A) : reducePointVS hΔ (.some x y h) = 0 := by
  simp only [reducePointVS]
  exact dif_neg hx

theorem reducePointVS_neg (P : (W.map A.subtype).toAffine.Point) :
    reducePointVS hΔ (-P) = -reducePointVS hΔ P := by
  cases P with
  | zero => rfl
  | some x y h =>
    rw [Affine.Point.neg_some]
    by_cases hx : x ∈ A
    · have hy : y ∈ A := Affine.Y_mem_of_X_mem W h.1 hx
      rw [reducePointVS_some_of_mem _ _ hx, reducePointVS_some_of_mem _ _ hx,
        Affine.Point.neg_some]
      refine some_congr rfl ?_ _ _

      show residue A (W.toAffine.negY ⟨x, hx⟩ ⟨y, hy⟩) = _
      exact (Affine.map_negY (residue A) (⟨x, hx⟩ : A) (⟨y, hy⟩ : A)).symm
    · rw [reducePointVS_some_of_notMem _ _ hx, reducePointVS_some_of_notMem _ _ hx]
      rfl

section Inertia

open scoped Pointwise

variable (K : Type*) [Field K] [Algebra K L]

private theorem _root_.ValuationSubring.smul_mem_of_mem_decompositionSubgroup {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.decompositionSubgroup K) {z : L} (hz : z ∈ A) : σ z ∈ A := by
  have h1 : σ • z ∈ σ • A := ValuationSubring.smul_mem_pointwise_smul σ z A hz
  rwa [MulAction.mem_stabilizer_iff.mp hσ, AlgEquiv.smul_def] at h1

p2m_alias "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.ValuationSubring.smul_mem_of_mem_decompositionSubgroup" "ValuationSubring.smul_mem_of_mem_decompositionSubgroup"
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

p2m_alias "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.ValuationSubring.residue_smul_eq_of_mem_inertiaSubgroup" "ValuationSubring.residue_smul_eq_of_mem_inertiaSubgroup"

theorem reducePointVS_some_apply_of_mem_inertia {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.decompositionSubgroup K)
    (hσI : (⟨σ, hσ⟩ : A.decompositionSubgroup K) ∈ A.inertiaSubgroup K)
    {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y)
    (h' : (W.map A.subtype).toAffine.Nonsingular (σ x) (σ y)) :
    reducePointVS hΔ (.some (σ x) (σ y) h') = reducePointVS hΔ (.some x y h) := by
  by_cases hx : x ∈ A
  · have hy : y ∈ A := Affine.Y_mem_of_X_mem W h.1 hx
    have hσx : σ x ∈ A := A.smul_mem_of_mem_decompositionSubgroup K hσ hx
    have hσy : σ y ∈ A := A.smul_mem_of_mem_decompositionSubgroup K hσ hy
    rw [reducePointVS_some_of_mem _ _ hσx, reducePointVS_some_of_mem _ _ hx]

    refine some_congr ?_ ?_ _ _
    · calc residue A (⟨σ x, hσx⟩ : A)
          = residue A ((⟨σ, hσ⟩ : A.decompositionSubgroup K) • (⟨x, hx⟩ : A)) := rfl
        _ = residue A (⟨x, hx⟩ : A) := A.residue_smul_eq_of_mem_inertiaSubgroup hσ hσI _
    · calc residue A (⟨σ y, hσy⟩ : A)
          = residue A ((⟨σ, hσ⟩ : A.decompositionSubgroup K) • (⟨y, hy⟩ : A)) := rfl
        _ = residue A (⟨y, hy⟩ : A) := A.residue_smul_eq_of_mem_inertiaSubgroup hσ hσI _
  · have hσx : σ x ∉ A := fun hmem => hx (by
      simpa using A.smul_mem_of_mem_decompositionSubgroup K (inv_mem hσ) hmem)
    rw [reducePointVS_some_of_notMem _ _ hσx, reducePointVS_some_of_notMem _ _ hx]

end Inertia

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

open IsLocalRing

namespace ValuationSubring
p2m_export "ValuationSubring" "subtype coe_mem_nonunits_iff neg_mem inertiaSubgroup toSubring ext mem_nonunits_iff_or zero_mem nonunits mem_nonunits_iff smul_mem_pointwise_smul inv_mem_nonunits_iff mem_top mul_mem one_mem mem_or_inv_mem nonunits_subset add_mem decompositionSubgroup valuation_le_one_iff algebra valuation subtype_injective LiesOverPrime smul_mem_of_mem_decompositionSubgroup residue_smul_eq_of_mem_inertiaSubgroup"
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
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY Affine.Y_eq_of_Y_ne Affine.slope_of_X_ne Affine.equation_neg a₃ Affine.Point.add_of_Y_eq Affine.addPolynomial_slope a₁ map Affine.equation_iff_nonsingular_of_Δ_ne_zero Affine.nonsingular_iff a₄ a₂ a₆ Affine.Point.some Affine.Point.some.injEq Affine.Point.neg_zero Affine.negAddY Affine.Point.zero_def reduction Affine.map_addY Affine.negY_negY Affine.map_addX Affine.nonsingular_add toAffine Affine.slope_of_Y_ne Affine.Point Affine.addX Affine.Point.add_some Affine.nonsingular_neg map_Δ Affine.addPolynomial_eq Affine.Point.map Affine.Point.some_ne_zero Δ Affine.map_negY Affine.Y_eq_of_X_eq Affine.equation_iff Affine.map_nonsingular Affine.Point.neg_some j InZeroComponentAt"
p2m_open "WeierstrassCurve"

namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation negY Y_eq_of_Y_ne slope_of_X_ne equation_neg Point.add_of_Y_eq addPolynomial_slope equation_iff_nonsingular_of_Δ_ne_zero slope nonsingular_iff map map_equation Point.some Point.some.injEq Point.neg_zero Nonsingular negAddY Point.zero_def map_addY negY_negY map_addX nonsingular_add equation_negAdd slope_of_Y_ne Point addX Point.add_some nonsingular_neg addPolynomial_eq Point.map Point.some_ne_zero map_negY addY Y_eq_of_X_eq equation_iff map_nonsingular polynomial Point.neg_some"
p2m_open "WeierstrassCurve.Affine"

theorem sub_mul_sub_negY {R : Type*} [CommRing R] {V : Affine R} {x₁ x₂ y₁ y₂ : R}
    (h₁ : V.Equation x₁ y₁) (h₂ : V.Equation x₂ y₂) :
    (y₁ - y₂) * (y₁ - V.negY x₂ y₂) =
      (x₁ - x₂) * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + V.a₂ * (x₁ + x₂) + V.a₄ - V.a₁ * y₁) := by
  rw [equation_iff] at h₁ h₂
  rw [negY]
  linear_combination h₁ - h₂

end Affine
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

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
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

open IsLocalRing

namespace ValuationSubring
p2m_export "ValuationSubring" "subtype coe_mem_nonunits_iff neg_mem inertiaSubgroup toSubring ext mem_nonunits_iff_or zero_mem nonunits mem_nonunits_iff smul_mem_pointwise_smul inv_mem_nonunits_iff mem_top mul_mem one_mem mem_or_inv_mem nonunits_subset add_mem decompositionSubgroup valuation_le_one_iff algebra valuation subtype_injective LiesOverPrime smul_mem_of_mem_decompositionSubgroup residue_smul_eq_of_mem_inertiaSubgroup"
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

private theorem _root_.ValuationSubring.natCast_mem_nonunits_iff_residue_eq_zero (n : ℕ) :
    (n : L) ∈ A.nonunits ↔ (n : ResidueField A) = 0 := by
  have h1 : ((n : A) : L) = (n : L) := by push_cast; rfl
  have h2 : residue A (n : A) = (n : ResidueField A) := map_natCast (residue A) n
  rw [← h1, A.coe_mem_nonunits_iff_residue_eq_zero, h2]

p2m_export "ValuationSubring" "natCast_mem_nonunits_iff_residue_eq_zero"
end ValuationSubring
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY Affine.Y_eq_of_Y_ne Affine.slope_of_X_ne Affine.equation_neg a₃ Affine.Point.add_of_Y_eq Affine.addPolynomial_slope a₁ map Affine.equation_iff_nonsingular_of_Δ_ne_zero Affine.nonsingular_iff a₄ a₂ a₆ Affine.Point.some Affine.Point.some.injEq Affine.Point.neg_zero Affine.negAddY Affine.Point.zero_def reduction Affine.map_addY Affine.negY_negY Affine.map_addX Affine.nonsingular_add toAffine Affine.slope_of_Y_ne Affine.Point Affine.addX Affine.Point.add_some Affine.nonsingular_neg map_Δ Affine.addPolynomial_eq Affine.Point.map Affine.Point.some_ne_zero Δ Affine.map_negY Affine.Y_eq_of_X_eq Affine.equation_iff Affine.map_nonsingular Affine.Point.neg_some j InZeroComponentAt"
p2m_open "WeierstrassCurve"

p2m_open "ValuationSubring P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.ValuationSubring"

variable {L : Type*} [Field L] {A : ValuationSubring L}

variable (W : WeierstrassCurve A)

namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation negY Y_eq_of_Y_ne slope_of_X_ne equation_neg Point.add_of_Y_eq addPolynomial_slope equation_iff_nonsingular_of_Δ_ne_zero slope nonsingular_iff map map_equation Point.some Point.some.injEq Point.neg_zero Nonsingular negAddY Point.zero_def map_addY negY_negY map_addX nonsingular_add equation_negAdd slope_of_Y_ne Point addX Point.add_some nonsingular_neg addPolynomial_eq Point.map Point.some_ne_zero map_negY addY Y_eq_of_X_eq equation_iff map_nonsingular polynomial Point.neg_some"
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
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

section Assembly

variable [DecidableEq L]

open _root_.WeierstrassCurve.Affine.Point in

theorem formal_param_nsmul {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y)
    (hx : x ∉ A) (j : ℕ) :
    (j • (some x y h : (W.map A.subtype).toAffine.Point) = 0 → (j : L) ∈ A.nonunits) ∧
    (∀ x' y' (h' : (W.map A.subtype).toAffine.Nonsingular x' y'),
      j • (some x y h : (W.map A.subtype).toAffine.Point) = some x' y' h' →
        x' ∉ A ∧ (-(x' / y')) / (-(x / y)) - (j : L) ∈ A.nonunits) := by

  have hy0 : y ≠ 0 := Affine.Y_ne_zero_of_X_notMem W h.1 hx
  have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ A.zero_mem)
  have hτ : -(x / y) ∈ A.nonunits := A.nonunits.neg_mem (Affine.X_div_Y_mem_nonunits W h.1 hx)
  have hτ0 : -(x / y) ≠ 0 := neg_ne_zero.mpr (div_ne_zero hx0 hy0)
  have hself : (x / y) / -(x / y) ∈ A := by
    rw [div_neg, div_self (div_ne_zero hx0 hy0)]
    exact A.toSubring.neg_mem A.one_mem
  induction j with
  | zero =>
    refine ⟨fun _ => by simp, fun x' y' h' heq => ?_⟩
    rw [zero_smul] at heq
    exact absurd heq.symm (some_ne_zero h')
  | succ j ih =>
    rw [succ_nsmul]

    rcases hP : (j • (some x y h : (W.map A.subtype).toAffine.Point)) with _ | @⟨xj, yj, hj⟩
    ·
      have hj0 : (j : L) ∈ A.nonunits := (ih.1) hP
      rw [← Affine.Point.zero_def, zero_add]
      refine ⟨fun h0 => absurd h0 (some_ne_zero h), fun x' y' h' heq => ?_⟩
      obtain ⟨rfl, rfl⟩ : x = x' ∧ y = y' := by
        rwa [Affine.Point.some.injEq] at heq
      refine ⟨hx, ?_⟩
      rw [div_self hτ0, Nat.cast_succ]
      have : (1 : L) - (j + 1) = -j := by ring
      rw [this]
      exact A.nonunits.neg_mem hj0
    ·
      have hIH := (ih.2) xj yj hj hP
      obtain ⟨hxj, hcong⟩ := hIH
      have htj : (xj / yj) / -(x / y) ∈ A := by
        have h1 : -(xj / yj) / -(x / y) ∈ A := by
          have := add_mem (A.nonunits_subset hcong) (show ((j : L)) ∈ A from by
            simp)
          simpa using this
        simpa [neg_div] using A.toSubring.neg_mem h1
      by_cases hcond : xj = x ∧ yj = (W.map A.subtype).toAffine.negY x y
      ·
        rw [add_of_Y_eq hcond.1 hcond.2]
        refine ⟨fun _ => ?_, fun x' y' h' heq => absurd heq.symm (some_ne_zero h')⟩

        have hneg := Affine.neg_formal_param_estimate (W := W) h.1 hx hτ0 hself
        rw [hcond.1, hcond.2] at hcong
        have key : ((j : L) + 1) =
            ((-(x / y)) + (-(x / (W.map A.subtype).toAffine.negY x y))) / -(x / y)
              - (-(x / (W.map A.subtype).toAffine.negY x y)) / -(x / y) + (j : L)
              + (1 - (-(x / y)) / -(x / y)) := by
          field_simp
          ring1
        rw [Nat.cast_succ, key]
        have h1 : (1 : L) - (-(x / y)) / -(x / y) = 0 := by
          rw [div_self hτ0]; ring
        rw [h1, add_zero]
        have h2 : -(x / (W.map A.subtype).toAffine.negY x y) / -(x / y) - (j : L)
            ∈ A.nonunits := hcong
        have h3 := A.nonunits.sub_mem hneg h2
        have heq : ((-(x / y)) + (-(x / (W.map A.subtype).toAffine.negY x y))) / -(x / y)
              - (-(x / (W.map A.subtype).toAffine.negY x y)) / -(x / y) + (j : L)
            = ((-(x / y)) + (-(x / (W.map A.subtype).toAffine.negY x y))) / -(x / y)
              - ((-(x / (W.map A.subtype).toAffine.negY x y)) / -(x / y) - (j : L)) := by
          ring
        rw [heq]
        exact h3
      ·
        rw [add_some hcond]
        refine ⟨fun h0 => absurd h0 (some_ne_zero _), fun x' y' h' heq => ?_⟩
        obtain ⟨hx', hy'⟩ : (W.map A.subtype).toAffine.addX xj x
            ((W.map A.subtype).toAffine.slope xj x yj y) = x' ∧
            (W.map A.subtype).toAffine.addY xj x yj
              ((W.map A.subtype).toAffine.slope xj x yj y) = y' := by
          rwa [Affine.Point.some.injEq] at heq
        subst hx'
        subst hy'
        obtain ⟨hadd1, hadd2⟩ := add_formal_param_estimate (W := W) hj.1 h.1 hxj hx hcond hτ hτ0
          htj hself
        refine ⟨hadd1, ?_⟩

        have key : (-((W.map A.subtype).toAffine.addX xj x
              ((W.map A.subtype).toAffine.slope xj x yj y)
            / (W.map A.subtype).toAffine.addY xj x yj
              ((W.map A.subtype).toAffine.slope xj x yj y))) / -(x / y) - ((j : ℕ) + 1 : L) =
            ((-((W.map A.subtype).toAffine.addX xj x
                ((W.map A.subtype).toAffine.slope xj x yj y)
              / (W.map A.subtype).toAffine.addY xj x yj
                ((W.map A.subtype).toAffine.slope xj x yj y)))
              - (-(xj / yj)) - (-(x / y))) / -(x / y)
            + ((-(xj / yj)) / -(x / y) - (j : L))
            + ((-(x / y)) / -(x / y) - 1) := by
          field_simp
          ring1
        rw [Nat.cast_succ, key]
        refine add_mem (add_mem hadd2 ?_) ?_
        · exact hcong
        · rw [div_self hτ0, sub_self]
          exact A.nonunits.zero_mem

end Assembly
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

end Affine
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

open _root_.WeierstrassCurve.Affine _root_.P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve.Affine _root_.WeierstrassCurve.Affine.Point in

theorem X_mem_of_nsmul_eq_zero' [DecidableEq L] {n : ℕ}
    (hn : (n : ResidueField A) ≠ 0) {x y : L}
    (h : (W.map A.subtype).toAffine.Nonsingular x y)
    (hP : n • (some x y h : (W.map A.subtype).toAffine.Point) = 0) : x ∈ A := by
  by_contra hx
  refine hn ?_
  rw [← A.natCast_mem_nonunits_iff_residue_eq_zero]
  exact (formal_param_nsmul (W := W) h hx n).1 hP

theorem X_mem_of_nsmul_eq_zero'' [DecidableEq L] (_hΔ : (W.map (residue A)).Δ ≠ 0) {n : ℕ}
    (hn : (n : ResidueField A) ≠ 0) {x y : L}
    (h : (W.map A.subtype).toAffine.Nonsingular x y)
    (hP : n • (Affine.Point.some x y h : (W.map A.subtype).toAffine.Point) = 0) : x ∈ A :=
  X_mem_of_nsmul_eq_zero' W hn h hP

open _root_.WeierstrassCurve.Affine.Point in

theorem some_eq_of_mem_inertia_of_nsmul_eq_zero' [DecidableEq L]
    (hΔ : (W.map (residue A)).Δ ≠ 0)
    {K : Type*} [Field K] [Algebra K L] {σ : L ≃ₐ[K] L} (hσ : σ ∈ A.decompositionSubgroup K)
    (hσI : (⟨σ, hσ⟩ : A.decompositionSubgroup K) ∈ A.inertiaSubgroup K)
    {n : ℕ} (hn : (n : ResidueField A) ≠ 0) {x y : L}
    (h : (W.map A.subtype).toAffine.Nonsingular x y)
    (h' : (W.map A.subtype).toAffine.Nonsingular (σ x) (σ y))
    (hP : n • (some x y h : (W.map A.subtype).toAffine.Point) = 0)
    (hP' : n • (some (σ x) (σ y) h' : (W.map A.subtype).toAffine.Point) = 0) :
    (some (σ x) (σ y) h' : (W.map A.subtype).toAffine.Point) = some x y h := by

  have hx : x ∈ A := X_mem_of_nsmul_eq_zero' W hn h hP
  have hy : y ∈ A := Affine.Y_mem_of_X_mem W h.1 hx
  have hσx : σ x ∈ A := A.smul_mem_of_mem_decompositionSubgroup K hσ hx
  have hσy : σ y ∈ A := A.smul_mem_of_mem_decompositionSubgroup K hσ hy

  have hresx : σ x - x ∈ A.nonunits := by
    rw [show σ x - x = (((⟨σ x, hσx⟩ : A) - ⟨x, hx⟩ : A) : L) from rfl,
      A.coe_mem_nonunits_iff_residue_eq_zero, map_sub, sub_eq_zero]
    exact A.residue_smul_eq_of_mem_inertiaSubgroup hσ hσI ⟨x, hx⟩
  have hresy : σ y - y ∈ A.nonunits := by
    rw [show σ y - y = (((⟨σ y, hσy⟩ : A) - ⟨y, hy⟩ : A) : L) from rfl,
      A.coe_mem_nonunits_iff_residue_eq_zero, map_sub, sub_eq_zero]
    exact A.residue_smul_eq_of_mem_inertiaSubgroup hσ hσI ⟨y, hy⟩

  by_contra hne
  have hnegns : (W.map A.subtype).toAffine.Nonsingular x ((W.map A.subtype).toAffine.negY x y) :=
    (Affine.nonsingular_neg ..).mpr h
  have hPQ : ¬(σ x = x ∧ σ y = (W.map A.subtype).toAffine.negY x
      ((W.map A.subtype).toAffine.negY x y)) := by
    rw [Affine.negY_negY]
    exact fun ⟨hx', hy'⟩ => hne (by simp only [Affine.Point.some.injEq]; exact ⟨hx', hy'⟩)
  have hQdef : (some (σ x) (σ y) h' : (W.map A.subtype).toAffine.Point) - some x y h =
      some _ _ (Affine.nonsingular_add h' hnegns hPQ) := by
    rw [sub_eq_add_neg, neg_some, add_some hPQ]
  have hQtor : n • ((some (σ x) (σ y) h' : (W.map A.subtype).toAffine.Point) - some x y h)
      = 0 := by
    rw [smul_sub, hP, hP', sub_zero]
  have hQX : (W.map A.subtype).toAffine.addX (σ x) x
      ((W.map A.subtype).toAffine.slope (σ x) x (σ y)
        ((W.map A.subtype).toAffine.negY x y)) ∈ A := by
    refine X_mem_of_nsmul_eq_zero' W hn (Affine.nonsingular_add h' hnegns hPQ) ?_
    rw [← hQdef]
    exact hQtor
  refine Affine.addX_notMem_of_sub_mem_nonunits W hΔ h'.1 hnegns.1 hσx hx hPQ hresx ?_ hQX
  rw [Affine.negY_negY]
  exact hresy

open _root_.WeierstrassCurve.Affine.Point in

theorem fixed_of_mem_inertia_of_nsmul_eq_zero [DecidableEq L] {V : WeierstrassCurve L}
    (W : WeierstrassCurve A) (hVW : W.map A.subtype = V)
    (hΔ : (W.map (residue A)).Δ ≠ 0)
    {K : Type*} [Field K] [Algebra K L] {σ : L ≃ₐ[K] L} (hσ : σ ∈ A.decompositionSubgroup K)
    (hσI : (⟨σ, hσ⟩ : A.decompositionSubgroup K) ∈ A.inertiaSubgroup K)
    {n : ℕ} (hn : (n : ResidueField A) ≠ 0) {x y : L}
    (h : V.toAffine.Nonsingular x y)
    (h' : V.toAffine.Nonsingular (σ x) (σ y))
    (hP : n • (some x y h : V.toAffine.Point) = 0)
    (hP' : n • (some (σ x) (σ y) h' : V.toAffine.Point) = 0) :
    σ x = x ∧ σ y = y := by
  subst hVW
  have key := some_eq_of_mem_inertia_of_nsmul_eq_zero' W hΔ hσ hσI hn h h' hP hP'
  rwa [Affine.Point.some.injEq] at key

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

open IsLocalRing

namespace ValuationSubring
p2m_export "ValuationSubring" "subtype coe_mem_nonunits_iff neg_mem inertiaSubgroup toSubring ext mem_nonunits_iff_or zero_mem nonunits mem_nonunits_iff smul_mem_pointwise_smul inv_mem_nonunits_iff mem_top mul_mem one_mem mem_or_inv_mem nonunits_subset add_mem decompositionSubgroup valuation_le_one_iff algebra valuation subtype_injective LiesOverPrime smul_mem_of_mem_decompositionSubgroup residue_smul_eq_of_mem_inertiaSubgroup"
p2m_open "ValuationSubring"

variable {L : Type*} [Field L] (A : ValuationSubring L)

private theorem _root_.ValuationSubring.div_mem_of_mem_of_notMem_nonunits {a b : L} (ha : a ∈ A) (hb : b ∉ A.nonunits) :
    a / b ∈ A := by
  rw [div_eq_mul_inv]
  exact A.toSubring.mul_mem ha (A.inv_mem_of_notMem_nonunits hb)

p2m_export "ValuationSubring" "div_mem_of_mem_of_notMem_nonunits"

private theorem _root_.ValuationSubring.residue_ne_zero_of_notMem_nonunits {b : L} (hb : b ∈ A) (hb' : b ∉ A.nonunits) :
    residue A ⟨b, hb⟩ ≠ 0 := fun h =>
  hb' ((A.coe_mem_nonunits_iff_residue_eq_zero ⟨b, hb⟩).mpr h)

p2m_export "ValuationSubring" "residue_ne_zero_of_notMem_nonunits"

private theorem _root_.ValuationSubring.residue_eq_of_coe_eq {a : L} (ha : a ∈ A) {v : A} (hav : a = (v : L)) :
    residue A ⟨a, ha⟩ = residue A v :=
  congrArg (residue A) (Subtype.ext hav)

p2m_export "ValuationSubring" "residue_eq_of_coe_eq"

private theorem _root_.ValuationSubring.residue_div {a b : L} (ha : a ∈ A) (hb : b ∈ A) (hb' : b ∉ A.nonunits)
    (hq : a / b ∈ A) :
    residue A ⟨a / b, hq⟩ = residue A ⟨a, ha⟩ / residue A ⟨b, hb⟩ := by
  have hb0 : b ≠ 0 := A.ne_zero_of_notMem_nonunits hb'
  have hbres : residue A ⟨b, hb⟩ ≠ 0 := A.residue_ne_zero_of_notMem_nonunits hb hb'
  rw [eq_div_iff hbres, ← map_mul]
  refine congrArg (residue A) (Subtype.ext ?_)
  push_cast
  exact div_mul_cancel₀ a hb0

p2m_export "ValuationSubring" "residue_div"

private theorem _root_.ValuationSubring.residue_eq_div_of_eq_div {a c d : L} (ha : a ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hd' : d ∉ A.nonunits) (hacd : a = c / d) :
    residue A ⟨a, ha⟩ = residue A ⟨c, hc⟩ / residue A ⟨d, hd⟩ := by
  rw [A.residue_eq_of_coe_eq ha
    (v := ⟨c / d, A.div_mem_of_mem_of_notMem_nonunits hc hd'⟩) hacd]
  exact A.residue_div hc hd hd' _

p2m_export "ValuationSubring" "residue_eq_div_of_eq_div"

private theorem _root_.ValuationSubring.residue_eq_residue_iff_sub_mem_nonunits {a b : L} (ha : a ∈ A) (hb : b ∈ A) :
    residue A ⟨a, ha⟩ = residue A ⟨b, hb⟩ ↔ a - b ∈ A.nonunits := by
  constructor
  · intro h
    have h0 : residue A (⟨a, ha⟩ - ⟨b, hb⟩) = 0 := by rw [map_sub, h, sub_self]
    have := (A.coe_mem_nonunits_iff_residue_eq_zero _).mpr h0
    simpa using this
  · intro h
    have h0 : residue A (⟨a, ha⟩ - ⟨b, hb⟩) = 0 :=
      (A.coe_mem_nonunits_iff_residue_eq_zero _).mp (by simpa using h)
    rw [map_sub, sub_eq_zero] at h0
    exact h0

p2m_export "ValuationSubring" "residue_eq_residue_iff_sub_mem_nonunits"
end ValuationSubring
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY Affine.Y_eq_of_Y_ne Affine.slope_of_X_ne Affine.equation_neg a₃ Affine.Point.add_of_Y_eq Affine.addPolynomial_slope a₁ map Affine.equation_iff_nonsingular_of_Δ_ne_zero Affine.nonsingular_iff a₄ a₂ a₆ Affine.Point.some Affine.Point.some.injEq Affine.Point.neg_zero Affine.negAddY Affine.Point.zero_def reduction Affine.map_addY Affine.negY_negY Affine.map_addX Affine.nonsingular_add toAffine Affine.slope_of_Y_ne Affine.Point Affine.addX Affine.Point.add_some Affine.nonsingular_neg map_Δ Affine.addPolynomial_eq Affine.Point.map Affine.Point.some_ne_zero Δ Affine.map_negY Affine.Y_eq_of_X_eq Affine.equation_iff Affine.map_nonsingular Affine.Point.neg_some j InZeroComponentAt"
p2m_open "WeierstrassCurve"

variable {L : Type*} [Field L] {A : ValuationSubring L} (W : WeierstrassCurve A)

private lemma some_congr' {R : Type*} [CommRing R] {V : Affine R} {x₁ x₂ y₁ y₂ : R}
    (hx : x₁ = x₂) (hy : y₁ = y₂) (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

section Coercion

variable {W}

lemma coe_negY {x y : L} (hx : x ∈ A) (hy : y ∈ A) :
    ((W.toAffine.negY ⟨x, hx⟩ ⟨y, hy⟩ : A) : L) = (W.map A.subtype).toAffine.negY x y :=
  (Affine.map_negY A.subtype (⟨x, hx⟩ : A) (⟨y, hy⟩ : A)).symm

lemma negY_mem {x y : L} (hx : x ∈ A) (hy : y ∈ A) :
    (W.map A.subtype).toAffine.negY x y ∈ A := by
  rw [← coe_negY hx hy]
  exact SetLike.coe_mem _

lemma residue_negY {x y : L} (hx : x ∈ A) (hy : y ∈ A) :
    residue A (W.toAffine.negY ⟨x, hx⟩ ⟨y, hy⟩) =
      (W.map (residue A)).toAffine.negY (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩) :=
  (Affine.map_negY (residue A) (⟨x, hx⟩ : A) (⟨y, hy⟩ : A)).symm

lemma residue_sub_negY {x₂ y₁ y₂ : L} (hy₁ : y₁ ∈ A) (hx₂ : x₂ ∈ A) (hy₂ : y₂ ∈ A)
    (hmem : y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A) :
    residue A ⟨y₁ - (W.map A.subtype).toAffine.negY x₂ y₂, hmem⟩ =
      residue A ⟨y₁, hy₁⟩ -
        (W.map (residue A)).toAffine.negY (residue A ⟨x₂, hx₂⟩) (residue A ⟨y₂, hy₂⟩) := by
  rw [A.residue_eq_of_coe_eq hmem (v := ⟨y₁, hy₁⟩ - W.toAffine.negY ⟨x₂, hx₂⟩ ⟨y₂, hy₂⟩)
    (by push_cast; rw [coe_negY hx₂ hy₂]), map_sub, residue_negY hx₂ hy₂]

lemma residue_inverse_iff {x₁ y₁ x₂ y₂ : L} (hx₁ : x₁ ∈ A) (hy₁ : y₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hy₂ : y₂ ∈ A) :
    (residue A ⟨x₁, hx₁⟩ = residue A ⟨x₂, hx₂⟩ ∧
        residue A ⟨y₁, hy₁⟩ =
          (W.map (residue A)).toAffine.negY (residue A ⟨x₂, hx₂⟩) (residue A ⟨y₂, hy₂⟩)) ↔
      (x₁ - x₂ ∈ A.nonunits ∧
        y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A.nonunits) := by
  have hnegA : (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A := negY_mem hx₂ hy₂
  have h1 := A.residue_eq_residue_iff_sub_mem_nonunits hx₁ hx₂
  have h2 := A.residue_eq_residue_iff_sub_mem_nonunits hy₁ hnegA
  have h3 : residue A ⟨(W.map A.subtype).toAffine.negY x₂ y₂, hnegA⟩ =
      (W.map (residue A)).toAffine.negY (residue A ⟨x₂, hx₂⟩) (residue A ⟨y₂, hy₂⟩) := by
    rw [A.residue_eq_of_coe_eq hnegA (v := W.toAffine.negY ⟨x₂, hx₂⟩ ⟨y₂, hy₂⟩)
      (coe_negY hx₂ hy₂).symm]
    exact residue_negY hx₂ hy₂
  rw [← h3]
  exact and_congr h1 h2

end Coercion
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

section Slope

variable [DecidableEq L] [DecidableEq (ResidueField A)]
variable {W}

theorem slope_mem_residue_of_not_inverse
    {x₁ y₁ x₂ y₂ : L} (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hred : ¬(x₁ - x₂ ∈ A.nonunits ∧
      y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A.nonunits)) :
    ∃ hs : (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ ∈ A,
      residue A ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hs⟩ =
        (W.map (residue A)).toAffine.slope (residue A ⟨x₁, hx₁⟩) (residue A ⟨x₂, hx₂⟩)
          (residue A ⟨y₁, Affine.Y_mem_of_X_mem W h₁ hx₁⟩)
          (residue A ⟨y₂, Affine.Y_mem_of_X_mem W h₂ hx₂⟩) := by
  have hy₁ : y₁ ∈ A := Affine.Y_mem_of_X_mem W h₁ hx₁
  have hy₂ : y₂ ∈ A := Affine.Y_mem_of_X_mem W h₂ hx₂
  have ha₁ : (W.map A.subtype).toAffine.a₁ ∈ A := SetLike.coe_mem W.a₁
  have ha₂ : (W.map A.subtype).toAffine.a₂ ∈ A := SetLike.coe_mem W.a₂
  have ha₄ : (W.map A.subtype).toAffine.a₄ ∈ A := SetLike.coe_mem W.a₄

  have hk₁ : (W.map (residue A)).toAffine.Equation (residue A ⟨x₁, hx₁⟩) (residue A ⟨y₁, hy₁⟩) :=
    Affine.equation_residue W (x := ⟨x₁, hx₁⟩) (y := ⟨y₁, hy₁⟩) h₁
  have hk₂ : (W.map (residue A)).toAffine.Equation (residue A ⟨x₂, hx₂⟩) (residue A ⟨y₂, hy₂⟩) :=
    Affine.equation_residue W (x := ⟨x₂, hx₂⟩) (y := ⟨y₂, hy₂⟩) h₂

  have ha₁k : (W.map (residue A)).toAffine.a₁ = residue A W.a₁ := rfl
  have ha₂k : (W.map (residue A)).toAffine.a₂ = residue A W.a₂ := rfl
  have ha₄k : (W.map (residue A)).toAffine.a₄ = residue A W.a₄ := rfl
  by_cases hxx : x₁ - x₂ ∈ A.nonunits
  ·

    have hyy : y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∉ A.nonunits := fun h => hred ⟨hxx, h⟩
    have hyyA : y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A :=
      A.toSubring.sub_mem hy₁ (negY_mem hx₂ hy₂)
    have hyy0 : y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ≠ 0 :=
      A.ne_zero_of_notMem_nonunits hyy

    have hxk : residue A ⟨x₁, hx₁⟩ = residue A ⟨x₂, hx₂⟩ :=
      (A.residue_eq_residue_iff_sub_mem_nonunits hx₁ hx₂).mpr hxx
    have hyk : residue A ⟨y₁, hy₁⟩ ≠
        (W.map (residue A)).toAffine.negY (residue A ⟨x₂, hx₂⟩) (residue A ⟨y₂, hy₂⟩) := by
      intro h
      exact hyy (((residue_inverse_iff hx₁ hy₁ hx₂ hy₂).mp ⟨hxk, h⟩).2)

    have hyk' : residue A ⟨y₁, hy₁⟩ = residue A ⟨y₂, hy₂⟩ :=
      Affine.Y_eq_of_Y_ne hk₁ hk₂ hxk hyk
    have hslope_k : (W.map (residue A)).toAffine.slope (residue A ⟨x₁, hx₁⟩)
        (residue A ⟨x₂, hx₂⟩) (residue A ⟨y₁, hy₁⟩) (residue A ⟨y₂, hy₂⟩) =
        (3 * residue A ⟨x₁, hx₁⟩ ^ 2 + 2 * (W.map (residue A)).toAffine.a₂ *
            residue A ⟨x₁, hx₁⟩ + (W.map (residue A)).toAffine.a₄ -
            (W.map (residue A)).toAffine.a₁ * residue A ⟨y₁, hy₁⟩) /
          (residue A ⟨y₁, hy₁⟩ -
            (W.map (residue A)).toAffine.negY (residue A ⟨x₁, hx₁⟩) (residue A ⟨y₁, hy₁⟩)) :=
      Affine.slope_of_Y_ne hxk hyk

    have hden_res : residue A ⟨y₁ - (W.map A.subtype).toAffine.negY x₂ y₂, hyyA⟩ =
        residue A ⟨y₁, hy₁⟩ -
          (W.map (residue A)).toAffine.negY (residue A ⟨x₁, hx₁⟩) (residue A ⟨y₁, hy₁⟩) := by
      rw [residue_sub_negY hy₁ hx₂ hy₂ hyyA, hxk, hyk']

    have hnum_mem : 3 * x₁ ^ 2 + 2 * (W.map A.subtype).toAffine.a₂ * x₁ +
        (W.map A.subtype).toAffine.a₄ - (W.map A.subtype).toAffine.a₁ * y₁ ∈ A := by
      refine A.toSubring.sub_mem (A.toSubring.add_mem (A.toSubring.add_mem ?_ ?_) ha₄)
        (A.toSubring.mul_mem ha₁ hy₁)
      · exact A.toSubring.mul_mem (by norm_num : (3 : L) ∈ A) (pow_mem hx₁ 2)
      · exact A.toSubring.mul_mem (A.toSubring.mul_mem (by norm_num : (2 : L) ∈ A) ha₂) hx₁
    have hnum_res : residue A ⟨3 * x₁ ^ 2 + 2 * (W.map A.subtype).toAffine.a₂ * x₁ +
        (W.map A.subtype).toAffine.a₄ - (W.map A.subtype).toAffine.a₁ * y₁, hnum_mem⟩ =
        3 * residue A ⟨x₁, hx₁⟩ ^ 2 + 2 * (W.map (residue A)).toAffine.a₂ *
          residue A ⟨x₁, hx₁⟩ + (W.map (residue A)).toAffine.a₄ -
          (W.map (residue A)).toAffine.a₁ * residue A ⟨y₁, hy₁⟩ := by
      rw [A.residue_eq_of_coe_eq hnum_mem
        (v := 3 * ⟨x₁, hx₁⟩ ^ 2 + 2 * W.a₂ * ⟨x₁, hx₁⟩ + W.a₄ - W.a₁ * ⟨y₁, hy₁⟩)
        (by push_cast; rfl)]
      simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
      rw [ha₁k, ha₂k, ha₄k]
    by_cases hx : x₁ = x₂
    ·
      have hyL : y₁ ≠ (W.map A.subtype).toAffine.negY x₂ y₂ := fun h => hyy0 (by rw [h, sub_self])
      have hyL' : y₁ = y₂ := Affine.Y_eq_of_Y_ne h₁ h₂ hx hyL
      have hslope_L : (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ =
          (3 * x₁ ^ 2 + 2 * (W.map A.subtype).toAffine.a₂ * x₁ +
              (W.map A.subtype).toAffine.a₄ - (W.map A.subtype).toAffine.a₁ * y₁) /
            (y₁ - (W.map A.subtype).toAffine.negY x₁ y₁) :=
        Affine.slope_of_Y_ne hx hyL
      have hden_eq : y₁ - (W.map A.subtype).toAffine.negY x₁ y₁ =
          y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ := by
        rw [hx, hyL']
      have hslope_L' : (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ =
          (3 * x₁ ^ 2 + 2 * (W.map A.subtype).toAffine.a₂ * x₁ +
              (W.map A.subtype).toAffine.a₄ - (W.map A.subtype).toAffine.a₁ * y₁) /
            (y₁ - (W.map A.subtype).toAffine.negY x₂ y₂) := by
        rw [hslope_L, hden_eq]
      have hsmem : (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ ∈ A := by
        rw [hslope_L']
        exact A.div_mem_of_mem_of_notMem_nonunits hnum_mem hyy
      refine ⟨hsmem, ?_⟩
      rw [A.residue_eq_div_of_eq_div hsmem hnum_mem hyyA hyy hslope_L', hslope_k, hnum_res,
        hden_res]
    ·

      have hslope_L : (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ = (y₁ - y₂) / (x₁ - x₂) :=
        Affine.slope_of_X_ne hx
      have hN_mem : x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (W.map A.subtype).toAffine.a₂ * (x₁ + x₂) +
          (W.map A.subtype).toAffine.a₄ - (W.map A.subtype).toAffine.a₁ * y₁ ∈ A := by
        refine A.toSubring.sub_mem (A.toSubring.add_mem (A.toSubring.add_mem (A.toSubring.add_mem
          (A.toSubring.add_mem (pow_mem hx₁ 2) (A.toSubring.mul_mem hx₁ hx₂)) (pow_mem hx₂ 2))
          (A.toSubring.mul_mem ha₂ (A.toSubring.add_mem hx₁ hx₂))) ha₄)
          (A.toSubring.mul_mem ha₁ hy₁)

      have hslope_N : (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ =
          (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (W.map A.subtype).toAffine.a₂ * (x₁ + x₂) +
              (W.map A.subtype).toAffine.a₄ - (W.map A.subtype).toAffine.a₁ * y₁) /
            (y₁ - (W.map A.subtype).toAffine.negY x₂ y₂) := by
        rw [hslope_L, div_eq_div_iff (sub_ne_zero.mpr hx) hyy0]
        linear_combination Affine.sub_mul_sub_negY h₁ h₂
      have hsmem : (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ ∈ A := by
        rw [hslope_N]
        exact A.div_mem_of_mem_of_notMem_nonunits hN_mem hyy
      refine ⟨hsmem, ?_⟩

      have hN_res : residue A ⟨x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 +
          (W.map A.subtype).toAffine.a₂ * (x₁ + x₂) + (W.map A.subtype).toAffine.a₄ -
          (W.map A.subtype).toAffine.a₁ * y₁, hN_mem⟩ =
          3 * residue A ⟨x₁, hx₁⟩ ^ 2 + 2 * (W.map (residue A)).toAffine.a₂ *
            residue A ⟨x₁, hx₁⟩ + (W.map (residue A)).toAffine.a₄ -
            (W.map (residue A)).toAffine.a₁ * residue A ⟨y₁, hy₁⟩ := by
        rw [A.residue_eq_of_coe_eq hN_mem
          (v := ⟨x₁, hx₁⟩ ^ 2 + ⟨x₁, hx₁⟩ * ⟨x₂, hx₂⟩ + ⟨x₂, hx₂⟩ ^ 2 +
            W.a₂ * (⟨x₁, hx₁⟩ + ⟨x₂, hx₂⟩) + W.a₄ - W.a₁ * ⟨y₁, hy₁⟩)
          (by push_cast; rfl)]
        simp only [map_sub, map_add, map_mul, map_pow]
        rw [ha₁k, ha₂k, ha₄k, ← hxk]
        ring
      rw [A.residue_eq_div_of_eq_div hsmem hN_mem hyyA hyy hslope_N, hslope_k, hN_res, hden_res]
  ·
    have hxL : x₁ ≠ x₂ := fun h => hxx (by rw [h, sub_self]; exact A.nonunits.zero_mem)
    have hxxA : x₁ - x₂ ∈ A := A.toSubring.sub_mem hx₁ hx₂
    have hslope_L : (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ = (y₁ - y₂) / (x₁ - x₂) :=
      Affine.slope_of_X_ne hxL
    have hyyA : y₁ - y₂ ∈ A := A.toSubring.sub_mem hy₁ hy₂
    have hsmem : (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ ∈ A := by
      rw [hslope_L]
      exact A.div_mem_of_mem_of_notMem_nonunits hyyA hxx
    refine ⟨hsmem, ?_⟩

    have hxk : residue A ⟨x₁, hx₁⟩ ≠ residue A ⟨x₂, hx₂⟩ := fun h =>
      hxx ((A.residue_eq_residue_iff_sub_mem_nonunits hx₁ hx₂).mp h)
    have hslope_k : (W.map (residue A)).toAffine.slope (residue A ⟨x₁, hx₁⟩)
        (residue A ⟨x₂, hx₂⟩) (residue A ⟨y₁, hy₁⟩) (residue A ⟨y₂, hy₂⟩) =
        (residue A ⟨y₁, hy₁⟩ - residue A ⟨y₂, hy₂⟩) /
          (residue A ⟨x₁, hx₁⟩ - residue A ⟨x₂, hx₂⟩) := Affine.slope_of_X_ne hxk
    have hnum_eq : residue A ⟨y₁ - y₂, hyyA⟩ = residue A ⟨y₁, hy₁⟩ - residue A ⟨y₂, hy₂⟩ := by
      rw [A.residue_eq_of_coe_eq hyyA (v := ⟨y₁, hy₁⟩ - ⟨y₂, hy₂⟩) (by push_cast; ring), map_sub]
    have hden_eq : residue A ⟨x₁ - x₂, hxxA⟩ = residue A ⟨x₁, hx₁⟩ - residue A ⟨x₂, hx₂⟩ := by
      rw [A.residue_eq_of_coe_eq hxxA (v := ⟨x₁, hx₁⟩ - ⟨x₂, hx₂⟩) (by push_cast; ring), map_sub]
    rw [A.residue_eq_div_of_eq_div hsmem hyyA hxxA hxx hslope_L, hslope_k, hnum_eq, hden_eq]

end Slope
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

section IntegralCase

variable [DecidableEq L] [DecidableEq (ResidueField A)]
variable {W} (hΔ : (W.map (residue A)).Δ ≠ 0)

set_option maxHeartbeats 6400000 in

theorem reducePointVS_add_of_mem {x₁ y₁ x₂ y₂ : L}
    (h₁ : (W.map A.subtype).toAffine.Nonsingular x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Nonsingular x₂ y₂) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A) :
    reducePointVS hΔ (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) =
      reducePointVS hΔ (.some x₁ y₁ h₁) + reducePointVS hΔ (.some x₂ y₂ h₂) := by
  have hy₁ : y₁ ∈ A := Affine.Y_mem_of_X_mem W h₁.1 hx₁
  have hy₂ : y₂ ∈ A := Affine.Y_mem_of_X_mem W h₂.1 hx₂

  rw [reducePointVS_some_of_mem _ _ hx₁, reducePointVS_some_of_mem _ _ hx₂]
  by_cases hred : x₁ - x₂ ∈ A.nonunits ∧
      y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A.nonunits
  ·
    obtain ⟨hredx, hredy⟩ := (residue_inverse_iff hx₁ hy₁ hx₂ hy₂).mpr hred
    rw [Affine.Point.add_of_Y_eq hredx hredy]
    by_cases hPQ : x₁ = x₂ ∧ y₁ = (W.map A.subtype).toAffine.negY x₂ y₂
    ·
      rw [Affine.Point.add_of_Y_eq hPQ.1 hPQ.2, reducePointVS_zero]
    ·

      rw [Affine.Point.add_some hPQ]
      exact reducePointVS_some_of_notMem _ _
        (Affine.addX_notMem_of_sub_mem_nonunits W hΔ h₁.1 h₂.1 hx₁ hx₂ hPQ hred.1 hred.2)
  ·

    obtain ⟨hsmem, hsres⟩ := slope_mem_residue_of_not_inverse h₁.1 h₂.1 hx₁ hx₂ hred

    have hPQ : ¬(x₁ = x₂ ∧ y₁ = (W.map A.subtype).toAffine.negY x₂ y₂) := by
      rintro ⟨hxe, hye⟩
      exact hred ⟨by rw [hxe, sub_self]; exact A.nonunits.zero_mem,
        by rw [hye, sub_self]; exact A.nonunits.zero_mem⟩

    have hredk : ¬(residue A ⟨x₁, hx₁⟩ = residue A ⟨x₂, hx₂⟩ ∧
        residue A ⟨y₁, hy₁⟩ =
          (W.map (residue A)).toAffine.negY (residue A ⟨x₂, hx₂⟩) (residue A ⟨y₂, hy₂⟩)) :=
      fun h => hred ((residue_inverse_iff hx₁ hy₁ hx₂ hy₂).mp h)
    rw [Affine.Point.add_some hPQ, Affine.Point.add_some hredk]

    have hX_coe : (W.map A.subtype).toAffine.addX x₁ x₂
        ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) =
        ((W.toAffine.addX ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩
          ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩ : A) : L) :=
      Affine.map_addX (W' := W) A.subtype (⟨x₁, hx₁⟩ : A) (⟨x₂, hx₂⟩ : A)
        ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩
    have hY_coe : (W.map A.subtype).toAffine.addY x₁ x₂ y₁
        ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) =
        ((W.toAffine.addY ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ ⟨y₁, hy₁⟩
          ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩ : A) : L) :=
      Affine.map_addY (W' := W) A.subtype (⟨x₁, hx₁⟩ : A) (⟨y₁, hy₁⟩ : A) (⟨x₂, hx₂⟩ : A)
        ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩
    have hX_mem : (W.map A.subtype).toAffine.addX x₁ x₂
        ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) ∈ A := by
      rw [hX_coe]; exact SetLike.coe_mem _
    rw [reducePointVS_some_of_mem _ _ hX_mem]
    refine some_congr' ?_ ?_ _ _
    ·
      calc residue A ⟨(W.map A.subtype).toAffine.addX x₁ x₂
              ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂), hX_mem⟩
          = residue A (W.toAffine.addX ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩
              ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩) :=
            A.residue_eq_of_coe_eq hX_mem hX_coe
        _ = (W.map (residue A)).toAffine.addX (residue A ⟨x₁, hx₁⟩) (residue A ⟨x₂, hx₂⟩)
              (residue A ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩) :=
            (Affine.map_addX (W' := W) (residue A) (⟨x₁, hx₁⟩ : A) (⟨x₂, hx₂⟩ : A)
              ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩).symm
        _ = _ := by rw [hsres]
    ·
      calc residue A ⟨(W.map A.subtype).toAffine.addY x₁ x₂ y₁
              ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂),
              Affine.Y_mem_of_X_mem W (Affine.nonsingular_add h₁ h₂ hPQ).1 hX_mem⟩
          = residue A (W.toAffine.addY ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ ⟨y₁, hy₁⟩
              ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩) :=
            A.residue_eq_of_coe_eq _ hY_coe
        _ = (W.map (residue A)).toAffine.addY (residue A ⟨x₁, hx₁⟩) (residue A ⟨x₂, hx₂⟩)
              (residue A ⟨y₁, hy₁⟩)
              (residue A ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩) :=
            (Affine.map_addY (W' := W) (residue A) (⟨x₁, hx₁⟩ : A) (⟨y₁, hy₁⟩ : A)
              (⟨x₂, hx₂⟩ : A)
              ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩).symm
        _ = _ := by rw [hsres]

end IntegralCase
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

section KernelCase

variable [DecidableEq L] [DecidableEq (ResidueField A)]
variable {W} (hΔ : (W.map (residue A)).Δ ≠ 0)

theorem reducePointVS_add_of_notMem_of_notMem {x₁ y₁ x₂ y₂ : L}
    (h₁ : (W.map A.subtype).toAffine.Nonsingular x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Nonsingular x₂ y₂) (hx₁ : x₁ ∉ A) (hx₂ : x₂ ∉ A) :
    reducePointVS hΔ (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) =
      reducePointVS hΔ (.some x₁ y₁ h₁) + reducePointVS hΔ (.some x₂ y₂ h₂) := by

  rw [reducePointVS_some_of_notMem _ _ hx₁, reducePointVS_some_of_notMem _ _ hx₂, add_zero]
  by_cases hPQ : x₁ = x₂ ∧ y₁ = (W.map A.subtype).toAffine.negY x₂ y₂
  · rw [Affine.Point.add_of_Y_eq hPQ.1 hPQ.2, reducePointVS_zero]
  ·

    have hy₁0 : y₁ ≠ 0 := Affine.Y_ne_zero_of_X_notMem W h₁.1 hx₁
    have hy₂0 : y₂ ≠ 0 := Affine.Y_ne_zero_of_X_notMem W h₂.1 hx₂
    have hx₁0 : x₁ ≠ 0 := fun h => hx₁ (h ▸ A.zero_mem)
    have hx₂0 : x₂ ≠ 0 := fun h => hx₂ (h ▸ A.zero_mem)
    have ht₁m : x₁ / y₁ ∈ A.nonunits := Affine.X_div_Y_mem_nonunits W h₁.1 hx₁
    have ht₂m : x₂ / y₂ ∈ A.nonunits := Affine.X_div_Y_mem_nonunits W h₂.1 hx₂
    have ht₁0 : x₁ / y₁ ≠ 0 := div_ne_zero hx₁0 hy₁0
    have ht₂0 : x₂ / y₂ ≠ 0 := div_ne_zero hx₂0 hy₂0
    have haddX : (W.map A.subtype).toAffine.addX x₁ x₂
        ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) ∉ A := by
      rcases A.mem_or_inv_mem ((x₁ / y₁) / (x₂ / y₂)) with hcase | hcase
      ·
        refine (Affine.add_formal_param_estimate h₁.1 h₂.1 hx₁ hx₂ hPQ ht₂m ht₂0 hcase ?_).1
        rw [div_self ht₂0]
        exact A.one_mem
      ·
        rw [show ((x₁ / y₁) / (x₂ / y₂))⁻¹ = (x₂ / y₂) / (x₁ / y₁) by rw [inv_div]] at hcase
        refine (Affine.add_formal_param_estimate h₁.1 h₂.1 hx₁ hx₂ hPQ ht₁m ht₁0 ?_ hcase).1
        rw [div_self ht₁0]
        exact A.one_mem
    rw [Affine.Point.add_some hPQ]
    exact reducePointVS_some_of_notMem _ _ haddX

end KernelCase
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

section MixedCase

variable [DecidableEq L] [DecidableEq (ResidueField A)]
variable {W} (hΔ : (W.map (residue A)).Δ ≠ 0)

theorem reducePointVS_add_of_mem_of_notMem {x₁ y₁ x₂ y₂ : L}
    (h₁ : (W.map A.subtype).toAffine.Nonsingular x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Nonsingular x₂ y₂) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∉ A) :
    reducePointVS hΔ (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) =
      reducePointVS hΔ (.some x₁ y₁ h₁) + reducePointVS hΔ (.some x₂ y₂ h₂) := by

  rw [reducePointVS_some_of_notMem _ _ hx₂, add_zero]

  have hPn : (W.map A.subtype).toAffine.Nonsingular x₁ ((W.map A.subtype).toAffine.negY x₁ y₁) :=
    (Affine.nonsingular_neg _ _).mpr h₁
  have hQn : (W.map A.subtype).toAffine.Nonsingular x₂ ((W.map A.subtype).toAffine.negY x₂ y₂) :=
    (Affine.nonsingular_neg _ _).mpr h₂
  have hPneg : (.some x₁ ((W.map A.subtype).toAffine.negY x₁ y₁) hPn :
      (W.map A.subtype).toAffine.Point) = -(.some x₁ y₁ h₁) := (Affine.Point.neg_some h₁).symm
  have hQneg : (.some x₂ ((W.map A.subtype).toAffine.negY x₂ y₂) hQn :
      (W.map A.subtype).toAffine.Point) = -(.some x₂ y₂ h₂) := (Affine.Point.neg_some h₂).symm

  cases hadd : (.some x₁ y₁ h₁ + .some x₂ y₂ h₂ : (W.map A.subtype).toAffine.Point) with
  | zero =>

    exfalso
    have hP : (.some x₁ y₁ h₁ : (W.map A.subtype).toAffine.Point) = -(.some x₂ y₂ h₂) :=
      eq_neg_of_add_eq_zero_left hadd
    rw [← hQneg] at hP
    simp only [Affine.Point.some.injEq] at hP
    exact hx₂ (hP.1 ▸ hx₁)
  | some X₃ Y₃ h₃ =>
    by_cases hX₃ : X₃ ∈ A
    ·
      have hint := reducePointVS_add_of_mem hΔ h₃ hPn hX₃ hx₁
      have hSnegP : (.some X₃ Y₃ h₃ : (W.map A.subtype).toAffine.Point) +
          .some x₁ ((W.map A.subtype).toAffine.negY x₁ y₁) hPn = .some x₂ y₂ h₂ := by
        rw [hPneg, ← hadd]; abel
      rw [hSnegP, reducePointVS_some_of_notMem _ _ hx₂, hPneg, reducePointVS_neg,
        ← sub_eq_add_neg] at hint
      exact (sub_eq_zero.mp hint.symm)
    ·
      exfalso
      have hker := reducePointVS_add_of_notMem_of_notMem hΔ h₃ hQn hX₃ hx₂
      have hSnegQ : (.some X₃ Y₃ h₃ : (W.map A.subtype).toAffine.Point) +
          .some x₂ ((W.map A.subtype).toAffine.negY x₂ y₂) hQn = .some x₁ y₁ h₁ := by
        rw [hQneg, ← hadd]; abel
      rw [hSnegQ, reducePointVS_some_of_mem _ _ hx₁, reducePointVS_some_of_notMem _ _ hX₃,
        reducePointVS_some_of_notMem _ _ hx₂, add_zero] at hker
      injection hker

end MixedCase
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

section Homomorphism

variable [DecidableEq L] [DecidableEq (ResidueField A)]
variable {W} (hΔ : (W.map (residue A)).Δ ≠ 0)

theorem reducePointVS_add (P Q : (W.map A.subtype).toAffine.Point) :
    reducePointVS hΔ (P + Q) = reducePointVS hΔ P + reducePointVS hΔ Q := by
  cases P with
  | zero =>
    show reducePointVS hΔ ((0 : (W.map A.subtype).toAffine.Point) + Q) =
      reducePointVS hΔ (0 : (W.map A.subtype).toAffine.Point) + reducePointVS hΔ Q
    rw [zero_add, reducePointVS_zero, zero_add]
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      show reducePointVS hΔ (.some x₁ y₁ h₁ + (0 : (W.map A.subtype).toAffine.Point)) =
        reducePointVS hΔ (.some x₁ y₁ h₁) + reducePointVS hΔ (0 : (W.map A.subtype).toAffine.Point)
      rw [add_zero, reducePointVS_zero, add_zero]
    | some x₂ y₂ h₂ =>
      by_cases hx₁ : x₁ ∈ A <;> by_cases hx₂ : x₂ ∈ A
      · exact reducePointVS_add_of_mem hΔ h₁ h₂ hx₁ hx₂
      · exact reducePointVS_add_of_mem_of_notMem hΔ h₁ h₂ hx₁ hx₂
      · rw [add_comm, add_comm (reducePointVS hΔ (.some x₁ y₁ h₁))]
        exact reducePointVS_add_of_mem_of_notMem hΔ h₂ h₁ hx₂ hx₁
      · exact reducePointVS_add_of_notMem_of_notMem hΔ h₁ h₂ hx₁ hx₂

noncomputable def reduceHomVS :
    (W.map A.subtype).toAffine.Point →+ (W.map (residue A)).toAffine.Point where
  toFun := reducePointVS hΔ
  map_zero' := reducePointVS_zero hΔ
  map_add' := reducePointVS_add hΔ

end Homomorphism
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

p2m_open "IsLocalRing ValuationSubring P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.ValuationSubring WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve.Affine WeierstrassCurve.Affine.Point"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY Affine.Y_eq_of_Y_ne Affine.slope_of_X_ne Affine.equation_neg a₃ Affine.Point.add_of_Y_eq Affine.addPolynomial_slope a₁ map Affine.equation_iff_nonsingular_of_Δ_ne_zero Affine.nonsingular_iff a₄ a₂ a₆ Affine.Point.some Affine.Point.some.injEq Affine.Point.neg_zero Affine.negAddY Affine.Point.zero_def reduction Affine.map_addY Affine.negY_negY Affine.map_addX Affine.nonsingular_add toAffine Affine.slope_of_Y_ne Affine.Point Affine.addX Affine.Point.add_some Affine.nonsingular_neg map_Δ Affine.addPolynomial_eq Affine.Point.map Affine.Point.some_ne_zero Δ Affine.map_negY Affine.Y_eq_of_X_eq Affine.equation_iff Affine.map_nonsingular Affine.Point.neg_some j InZeroComponentAt"
p2m_open "WeierstrassCurve"

variable {L : Type*} [Field L] {A : ValuationSubring L} (W : WeierstrassCurve A)

private def _root_.WeierstrassCurve.formalParam : (W.map A.subtype).toAffine.Point → L
  | .zero => 0
  | .some x y _ => -(x / y)

p2m_export "WeierstrassCurve" "formalParam"
@[scoped simp] theorem formalParam_zero : W.formalParam 0 = 0 := rfl

@[scoped simp] theorem formalParam_some {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y) :
    W.formalParam (some x y h) = -(x / y) := rfl

private def _root_.WeierstrassCurve.IsNonIntegral (P : (W.map A.subtype).toAffine.Point) : Prop :=
  ∀ x y (h : (W.map A.subtype).toAffine.Nonsingular x y), P = some x y h → x ∉ A

p2m_export "WeierstrassCurve" "IsNonIntegral"
private theorem _root_.WeierstrassCurve.isNonIntegral_zero : W.IsNonIntegral 0 := fun _ _ h heq =>
  absurd heq (Ne.symm (some_ne_zero h))

p2m_export "WeierstrassCurve" "isNonIntegral_zero"
private theorem _root_.WeierstrassCurve.isNonIntegral_some_iff {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y) :
    W.IsNonIntegral (some x y h) ↔ x ∉ A := by
  refine ⟨fun hP => hP x y h rfl, fun hx x' y' h' heq => ?_⟩
  obtain ⟨rfl, rfl⟩ : x = x' ∧ y = y' := by rwa [Affine.Point.some.injEq] at heq
  exact hx

p2m_export "WeierstrassCurve" "isNonIntegral_some_iff"

private theorem _root_.WeierstrassCurve.exists_common_depth {x₁ y₁ x₂ y₂ : L}
    (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂)
    (hx₁ : x₁ ∉ A) (hx₂ : x₂ ∉ A) :
    ∃ τ : L, τ ∈ A.nonunits ∧ τ ≠ 0 ∧ (x₁ / y₁) / τ ∈ A ∧ (x₂ / y₂) / τ ∈ A := by
  have hy₁0 : y₁ ≠ 0 := Y_ne_zero_of_X_notMem W h₁ hx₁
  have hy₂0 : y₂ ≠ 0 := Y_ne_zero_of_X_notMem W h₂ hx₂
  have hx₁0 : x₁ ≠ 0 := fun h0 => hx₁ (h0 ▸ A.zero_mem)
  have hx₂0 : x₂ ≠ 0 := fun h0 => hx₂ (h0 ▸ A.zero_mem)
  have ht₁0 : x₁ / y₁ ≠ 0 := div_ne_zero hx₁0 hy₁0
  have ht₂0 : x₂ / y₂ ≠ 0 := div_ne_zero hx₂0 hy₂0
  rcases A.mem_or_inv_mem ((x₁ / y₁) / (x₂ / y₂)) with hd | hd
  · exact ⟨x₂ / y₂, X_div_Y_mem_nonunits W h₂ hx₂, ht₂0, hd, by
      rw [div_self ht₂0]; exact A.one_mem⟩
  · rw [show ((x₁ / y₁) / (x₂ / y₂))⁻¹ = (x₂ / y₂) / (x₁ / y₁) by rw [inv_div]] at hd
    exact ⟨x₁ / y₁, X_div_Y_mem_nonunits W h₁ hx₁, ht₁0, by
      rw [div_self ht₁0]; exact A.one_mem, hd⟩

p2m_export "WeierstrassCurve" "exists_common_depth"
variable [DecidableEq L]

private def _root_.WeierstrassCurve.nonIntegralLocus : AddSubgroup (W.map A.subtype).toAffine.Point where
  carrier := {P | W.IsNonIntegral P}
  zero_mem' := W.isNonIntegral_zero
  neg_mem' := by
    rintro (_ | @⟨a, b, hab⟩) hP
    · exact W.isNonIntegral_zero
    · rw [neg_some]
      exact (W.isNonIntegral_some_iff _).mpr ((W.isNonIntegral_some_iff hab).mp hP)
  add_mem' := by
    rintro (_ | @⟨x₁, y₁, h₁⟩) (_ | @⟨x₂, y₂, h₂⟩) hP hQ
    · simpa [← Affine.Point.zero_def] using W.isNonIntegral_zero
    · simpa [← Affine.Point.zero_def] using hQ
    · simpa [← Affine.Point.zero_def] using hP
    · have hx₁ : x₁ ∉ A := (W.isNonIntegral_some_iff h₁).mp hP
      have hx₂ : x₂ ∉ A := (W.isNonIntegral_some_iff h₂).mp hQ
      by_cases hxy : x₁ = x₂ ∧ y₁ = (W.map A.subtype).toAffine.negY x₂ y₂
      · rw [add_of_Y_eq hxy.1 hxy.2]
        exact W.isNonIntegral_zero
      · rw [add_some hxy]
        obtain ⟨τ, hτ, hτ0, ht₁, ht₂⟩ := W.exists_common_depth h₁.1 h₂.1 hx₁ hx₂
        exact (W.isNonIntegral_some_iff _).mpr
          (add_formal_param_estimate (W := W) h₁.1 h₂.1 hx₁ hx₂ hxy hτ hτ0 ht₁ ht₂).1

p2m_export "WeierstrassCurve" "nonIntegralLocus"
private theorem _root_.WeierstrassCurve.mem_nonIntegralLocus_some_iff {x y : L}
    (h : (W.map A.subtype).toAffine.Nonsingular x y) :
    some x y h ∈ W.nonIntegralLocus ↔ x ∉ A :=
  W.isNonIntegral_some_iff h

p2m_export "WeierstrassCurve" "mem_nonIntegralLocus_some_iff"
end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

open IsLocalRing

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY Affine.Y_eq_of_Y_ne Affine.slope_of_X_ne Affine.equation_neg a₃ Affine.Point.add_of_Y_eq Affine.addPolynomial_slope a₁ map Affine.equation_iff_nonsingular_of_Δ_ne_zero Affine.nonsingular_iff a₄ a₂ a₆ Affine.Point.some Affine.Point.some.injEq Affine.Point.neg_zero Affine.negAddY Affine.Point.zero_def reduction Affine.map_addY Affine.negY_negY Affine.map_addX Affine.nonsingular_add toAffine Affine.slope_of_Y_ne Affine.Point Affine.addX Affine.Point.add_some Affine.nonsingular_neg map_Δ Affine.addPolynomial_eq Affine.Point.map Affine.Point.some_ne_zero Δ Affine.map_negY Affine.Y_eq_of_X_eq Affine.equation_iff Affine.map_nonsingular Affine.Point.neg_some j InZeroComponentAt"
p2m_open "WeierstrassCurve"

section General

variable {L : Type*} [Field L] {A : ValuationSubring L} (W : WeierstrassCurve A)

private def _root_.WeierstrassCurve.HasNonsingularReduction (P : (W.map A.subtype).toAffine.Point) : Prop :=
  ∀ x y (h : (W.map A.subtype).toAffine.Nonsingular x y), P = .some x y h →
    ∀ (hx : x ∈ A) (hy : y ∈ A),
      (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩)

p2m_export "WeierstrassCurve" "HasNonsingularReduction"

private theorem _root_.WeierstrassCurve.hasNonsingularReduction_zero : W.HasNonsingularReduction 0 :=
  fun _ _ h heq => absurd heq (Ne.symm (Affine.Point.some_ne_zero h))

p2m_export "WeierstrassCurve" "hasNonsingularReduction_zero"

private theorem _root_.WeierstrassCurve.hasNonsingularReduction_some_iff {x y : L}
    (h : (W.map A.subtype).toAffine.Nonsingular x y) :
    W.HasNonsingularReduction (.some x y h) ↔
      ∀ (hx : x ∈ A) (hy : y ∈ A),
        (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩) := by
  refine ⟨fun hP hx hy => hP x y h rfl hx hy, fun hns x' y' h' heq hx' hy' => ?_⟩
  obtain ⟨rfl, rfl⟩ : x = x' ∧ y = y' := by rwa [Affine.Point.some.injEq] at heq
  exact hns hx' hy'

p2m_export "WeierstrassCurve" "hasNonsingularReduction_some_iff"

private theorem _root_.WeierstrassCurve.hasNonsingularReduction_some_of_notMem {x y : L}
    (h : (W.map A.subtype).toAffine.Nonsingular x y) (hx : x ∉ A) :
    W.HasNonsingularReduction (.some x y h) :=
  (W.hasNonsingularReduction_some_iff h).mpr fun hx' _ => absurd hx' hx

p2m_export "WeierstrassCurve" "hasNonsingularReduction_some_of_notMem"

private theorem _root_.WeierstrassCurve.hasNonsingularReduction_of_good (hΔ : (W.map (residue A)).Δ ≠ 0)
    (P : (W.map A.subtype).toAffine.Point) : W.HasNonsingularReduction P :=
  fun _ _ h _ _ _ => Affine.nonsingular_residue W hΔ h.1

p2m_export "WeierstrassCurve" "hasNonsingularReduction_of_good"

private theorem _root_.WeierstrassCurve.hasNonsingularReduction_of_isNonIntegral {P : (W.map A.subtype).toAffine.Point}
    (hP : W.IsNonIntegral P) : W.HasNonsingularReduction P :=
  fun x y h heq hx _ => absurd hx (hP x y h heq)

p2m_export "WeierstrassCurve" "hasNonsingularReduction_of_isNonIntegral"

private theorem _root_.WeierstrassCurve.hasNonsingularReduction_neg {P : (W.map A.subtype).toAffine.Point}
    (hP : W.HasNonsingularReduction P) : W.HasNonsingularReduction (-P) := by
  cases P with
  | zero =>
    show W.HasNonsingularReduction (-(0 : (W.map A.subtype).toAffine.Point))
    rw [Affine.Point.neg_zero]
    exact W.hasNonsingularReduction_zero
  | some x y h =>
    rw [Affine.Point.neg_some]
    rw [W.hasNonsingularReduction_some_iff] at hP
    rw [W.hasNonsingularReduction_some_iff]
    intro hx hy'
    have hy : y ∈ A := Affine.Y_mem_of_X_mem W h.1 hx
    have hns := hP hx hy
    have hkey : residue A (⟨(W.map A.subtype).toAffine.negY x y, hy'⟩ : A) =
        (W.map (residue A)).toAffine.negY (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩) := by
      rw [A.residue_eq_of_coe_eq hy' (v := W.toAffine.negY ⟨x, hx⟩ ⟨y, hy⟩)
        (coe_negY hx hy).symm]
      exact residue_negY hx hy
    rw [hkey]
    exact (Affine.nonsingular_neg ..).mpr hns

p2m_export "WeierstrassCurve" "hasNonsingularReduction_neg"
section NonIntegralLocus

variable [DecidableEq L]

private theorem _root_.WeierstrassCurve.isNonIntegral_of_mem_nonIntegralLocus {P : (W.map A.subtype).toAffine.Point}
    (hP : P ∈ W.nonIntegralLocus) : W.IsNonIntegral P :=
  fun _ _ h heq => (W.mem_nonIntegralLocus_some_iff h).mp (heq ▸ hP)

p2m_export "WeierstrassCurve" "isNonIntegral_of_mem_nonIntegralLocus"

private theorem _root_.WeierstrassCurve.hasNonsingularReduction_of_mem_nonIntegralLocus {P : (W.map A.subtype).toAffine.Point}
    (hP : P ∈ W.nonIntegralLocus) : W.HasNonsingularReduction P :=
  W.hasNonsingularReduction_of_isNonIntegral (W.isNonIntegral_of_mem_nonIntegralLocus hP)

p2m_export "WeierstrassCurve" "hasNonsingularReduction_of_mem_nonIntegralLocus"
end NonIntegralLocus
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

private lemma some_smoothLocus_congr {R : Type*} [CommRing R] {V : Affine R} {x₁ x₂ y₁ y₂ : R}
    (hx : x₁ = x₂) (hy : y₁ = y₂) (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

open Classical in

private noncomputable def _root_.WeierstrassCurve.reducePointSmooth :
    (W.map A.subtype).toAffine.Point → (W.map (residue A)).toAffine.Point
  | .zero => .zero
  | .some x y h =>
    if hx : x ∈ A then
      if hns : (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x, hx⟩)
          (residue A ⟨y, Affine.Y_mem_of_X_mem W h.1 hx⟩) then
        .some _ _ hns
      else .zero
    else .zero

p2m_export "WeierstrassCurve" "reducePointSmooth"
@[scoped simp]
private theorem _root_.WeierstrassCurve.reducePointSmooth_zero : W.reducePointSmooth 0 = 0 := rfl

p2m_export "WeierstrassCurve" "reducePointSmooth_zero"
private theorem _root_.WeierstrassCurve.reducePointSmooth_some_of_mem {x y : L}
    (h : (W.map A.subtype).toAffine.Nonsingular x y) (hx : x ∈ A) {hy : y ∈ A}
    (hns : (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩)) :
    W.reducePointSmooth (.some x y h) = .some (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩) hns := by
  simp only [reducePointSmooth]
  rw [dif_pos hx]
  exact dif_pos hns

p2m_export "WeierstrassCurve" "reducePointSmooth_some_of_mem"
private theorem _root_.WeierstrassCurve.reducePointSmooth_some_of_notMem {x y : L}
    (h : (W.map A.subtype).toAffine.Nonsingular x y) (hx : x ∉ A) :
    W.reducePointSmooth (.some x y h) = 0 := by
  simp only [reducePointSmooth]
  exact dif_neg hx

p2m_export "WeierstrassCurve" "reducePointSmooth_some_of_notMem"
private theorem _root_.WeierstrassCurve.reducePointSmooth_some_of_singular {x y : L}
    (h : (W.map A.subtype).toAffine.Nonsingular x y) (hx : x ∈ A) {hy : y ∈ A}
    (hsing : ¬ (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x, hx⟩)
      (residue A ⟨y, hy⟩)) :
    W.reducePointSmooth (.some x y h) = 0 := by
  simp only [reducePointSmooth]
  rw [dif_pos hx]
  exact dif_neg fun hcon => hsing hcon

p2m_export "WeierstrassCurve" "reducePointSmooth_some_of_singular"

theorem reducePointSmooth_eq_reducePointVS (hΔ : (W.map (residue A)).Δ ≠ 0)
    (P : (W.map A.subtype).toAffine.Point) :
    W.reducePointSmooth P = reducePointVS hΔ P := by
  cases P with
  | zero => rfl
  | some x y h =>
    by_cases hx : x ∈ A
    · rw [W.reducePointSmooth_some_of_mem h hx
        (Affine.nonsingular_residue W hΔ (x := ⟨x, hx⟩)
          (y := ⟨y, Affine.Y_mem_of_X_mem W h.1 hx⟩) h.1),
        reducePointVS_some_of_mem _ _ hx]
    · rw [W.reducePointSmooth_some_of_notMem h hx, reducePointVS_some_of_notMem _ _ hx]

private theorem _root_.WeierstrassCurve.reducePointSmooth_neg (P : (W.map A.subtype).toAffine.Point) :
    W.reducePointSmooth (-P) = -W.reducePointSmooth P := by
  cases P with
  | zero =>
    show W.reducePointSmooth (-(0 : (W.map A.subtype).toAffine.Point)) =
      -W.reducePointSmooth (0 : (W.map A.subtype).toAffine.Point)
    rw [Affine.Point.neg_zero, reducePointSmooth_zero, Affine.Point.neg_zero]
  | some x y h =>
    rw [Affine.Point.neg_some]
    by_cases hx : x ∈ A
    · have hy : y ∈ A := Affine.Y_mem_of_X_mem W h.1 hx
      have hy' : (W.map A.subtype).toAffine.negY x y ∈ A := negY_mem hx hy
      have hkey : residue A (⟨(W.map A.subtype).toAffine.negY x y, hy'⟩ : A) =
          (W.map (residue A)).toAffine.negY (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩) := by
        rw [A.residue_eq_of_coe_eq hy' (v := W.toAffine.negY ⟨x, hx⟩ ⟨y, hy⟩)
          (coe_negY hx hy).symm]
        exact residue_negY hx hy
      by_cases hns : (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x, hx⟩)
          (residue A ⟨y, hy⟩)
      · have hns' : (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x, hx⟩)
            (residue A ⟨(W.map A.subtype).toAffine.negY x y, hy'⟩) := by
          rw [hkey]
          exact (Affine.nonsingular_neg ..).mpr hns
        rw [W.reducePointSmooth_some_of_mem _ hx hns', W.reducePointSmooth_some_of_mem h hx hns,
          Affine.Point.neg_some]
        exact some_smoothLocus_congr rfl hkey _ _
      · have hns' : ¬ (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x, hx⟩)
            (residue A ⟨(W.map A.subtype).toAffine.negY x y, hy'⟩) := by
          rw [hkey]
          intro hcon
          exact hns ((Affine.nonsingular_neg ..).mp hcon)
        rw [W.reducePointSmooth_some_of_singular _ hx hns',
          W.reducePointSmooth_some_of_singular h hx hns]
        exact (Affine.Point.neg_zero).symm
    · rw [W.reducePointSmooth_some_of_notMem _ hx, W.reducePointSmooth_some_of_notMem h hx]
      exact (Affine.Point.neg_zero).symm

p2m_export "WeierstrassCurve" "reducePointSmooth_neg"
section Kernel

variable [DecidableEq L]

private theorem _root_.WeierstrassCurve.reducePointSmooth_eq_zero_of_mem_nonIntegralLocus
    {P : (W.map A.subtype).toAffine.Point} (hP : P ∈ W.nonIntegralLocus) :
    W.reducePointSmooth P = 0 := by
  cases P with
  | zero => exact W.reducePointSmooth_zero
  | some x y h =>
    exact W.reducePointSmooth_some_of_notMem h ((W.mem_nonIntegralLocus_some_iff h).mp hP)

p2m_export "WeierstrassCurve" "reducePointSmooth_eq_zero_of_mem_nonIntegralLocus"

private theorem _root_.WeierstrassCurve.mem_nonIntegralLocus_of_reducePointSmooth_eq_zero
    {P : (W.map A.subtype).toAffine.Point} (hP : W.HasNonsingularReduction P)
    (h0 : W.reducePointSmooth P = 0) : P ∈ W.nonIntegralLocus := by
  cases P with
  | zero => exact zero_mem _
  | some x y h =>
    by_cases hx : x ∈ A
    · exfalso
      have hy : y ∈ A := Affine.Y_mem_of_X_mem W h.1 hx
      have hns := (W.hasNonsingularReduction_some_iff h).mp hP hx hy
      rw [W.reducePointSmooth_some_of_mem h hx hns] at h0
      exact Affine.Point.some_ne_zero hns h0
    · exact (W.mem_nonIntegralLocus_some_iff h).mpr hx

p2m_export "WeierstrassCurve" "mem_nonIntegralLocus_of_reducePointSmooth_eq_zero"
end Kernel
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

p2m_open_scoped "WeierstrassCurve.Affine" in

theorem Affine.notMem_nonunits_of_sub_negY_mem_nonunits_of_nonsingular_residue
    {x y : L} (hx : x ∈ A) (hy : y ∈ A)
    (hns : (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩))
    (hY : y - (W.map A.subtype).toAffine.negY x y ∈ A.nonunits) :
    3 * x ^ 2 + 2 * (W.map A.subtype).toAffine.a₂ * x + (W.map A.subtype).toAffine.a₄ -
      (W.map A.subtype).toAffine.a₁ * y ∉ A.nonunits := by

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

theorem Affine.slope_notMem_of_sub_mem_nonunits_of_nonsingular_residue
    {x₁ x₂ y₁ y₂ : L} (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hy₁ : y₁ ∈ A)
    (hns₁ : (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x₁, hx₁⟩)
      (residue A ⟨y₁, hy₁⟩))
    (hPQ : ¬(x₁ = x₂ ∧ y₁ = (W.map A.subtype).toAffine.negY x₂ y₂))
    (hxx : x₁ - x₂ ∈ A.nonunits)
    (hyy : y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A.nonunits) :
    (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ ∉ A := by
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

    have hnum := Affine.notMem_nonunits_of_sub_negY_mem_nonunits_of_nonsingular_residue W
      hx₁ hy₁ hns₁ hden
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

      have hnum := Affine.notMem_nonunits_of_sub_negY_mem_nonunits_of_nonsingular_residue W
        hx₁ hy₁ hns₁ hden

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

theorem Affine.addX_notMem_of_sub_mem_nonunits_of_nonsingular_residue
    {x₁ x₂ y₁ y₂ : L} (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hy₁ : y₁ ∈ A)
    (hns₁ : (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x₁, hx₁⟩)
      (residue A ⟨y₁, hy₁⟩))
    (hPQ : ¬(x₁ = x₂ ∧ y₁ = (W.map A.subtype).toAffine.negY x₂ y₂))
    (hxx : x₁ - x₂ ∈ A.nonunits)
    (hyy : y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A.nonunits) :
    (W.map A.subtype).toAffine.addX x₁ x₂ ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) ∉ A := by
  have hℓ := Affine.slope_notMem_of_sub_mem_nonunits_of_nonsingular_residue W h₁ h₂ hx₁ hx₂
    hy₁ hns₁ hPQ hxx hyy
  set ℓ : L := (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂
  have ha₁ : (W.map A.subtype).toAffine.a₁ ∈ A := SetLike.coe_mem W.a₁
  have ha₂ : (W.map A.subtype).toAffine.a₂ ∈ A := SetLike.coe_mem W.a₂

  rw [show (W.map A.subtype).toAffine.addX x₁ x₂ ℓ =
    ℓ * (ℓ + (W.map A.subtype).toAffine.a₁) +
      (-(W.map A.subtype).toAffine.a₂ - x₁ - x₂) from by rw [Affine.addX]; ring]
  exact A.add_notMem (A.mul_notMem hℓ (by simpa [add_comm] using A.add_notMem hℓ ha₁))
    (A.toSubring.sub_mem (A.toSubring.sub_mem (A.toSubring.neg_mem ha₂) hx₁) hx₂)

end Slope
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

end General
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

open IsLocalRing

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY Affine.Y_eq_of_Y_ne Affine.slope_of_X_ne Affine.equation_neg a₃ Affine.Point.add_of_Y_eq Affine.addPolynomial_slope a₁ map Affine.equation_iff_nonsingular_of_Δ_ne_zero Affine.nonsingular_iff a₄ a₂ a₆ Affine.Point.some Affine.Point.some.injEq Affine.Point.neg_zero Affine.negAddY Affine.Point.zero_def reduction Affine.map_addY Affine.negY_negY Affine.map_addX Affine.nonsingular_add toAffine Affine.slope_of_Y_ne Affine.Point Affine.addX Affine.Point.add_some Affine.nonsingular_neg map_Δ Affine.addPolynomial_eq Affine.Point.map Affine.Point.some_ne_zero Δ Affine.map_negY Affine.Y_eq_of_X_eq Affine.equation_iff Affine.map_nonsingular Affine.Point.neg_some j InZeroComponentAt"
p2m_open "WeierstrassCurve"

variable {L : Type*} [Field L] {A : ValuationSubring L} {W : WeierstrassCurve A}

private lemma some_smoothClosure_congr {R : Type*} [CommRing R] {V : Affine R}
    {x₁ x₂ y₁ y₂ : R} (hx : x₁ = x₂) (hy : y₁ = y₂) (h₁ : V.Nonsingular x₁ y₁)
    (h₂ : V.Nonsingular x₂ y₂) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

section CoordinatewiseEngine

variable [DecidableEq L] [DecidableEq (ResidueField A)]

theorem addX_mem_of_not_inverse {x₁ y₁ x₂ y₂ : L}
    (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hred : ¬(x₁ - x₂ ∈ A.nonunits ∧
      y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A.nonunits)) :
    (W.map A.subtype).toAffine.addX x₁ x₂ ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) ∈ A := by
  obtain ⟨hsmem, -⟩ := slope_mem_residue_of_not_inverse h₁ h₂ hx₁ hx₂ hred
  have hX_coe : (W.map A.subtype).toAffine.addX x₁ x₂
      ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) =
      ((W.toAffine.addX ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩
        ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩ : A) : L) :=
    Affine.map_addX (W' := W) A.subtype (⟨x₁, hx₁⟩ : A) (⟨x₂, hx₂⟩ : A)
      ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩
  rw [hX_coe]
  exact SetLike.coe_mem _

theorem addY_mem_of_not_inverse {x₁ y₁ x₂ y₂ : L}
    (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hred : ¬(x₁ - x₂ ∈ A.nonunits ∧
      y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A.nonunits)) :
    (W.map A.subtype).toAffine.addY x₁ x₂ y₁
      ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) ∈ A := by
  obtain ⟨hsmem, -⟩ := slope_mem_residue_of_not_inverse h₁ h₂ hx₁ hx₂ hred
  have hy₁ : y₁ ∈ A := Affine.Y_mem_of_X_mem W h₁ hx₁
  have hY_coe : (W.map A.subtype).toAffine.addY x₁ x₂ y₁
      ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) =
      ((W.toAffine.addY ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ ⟨y₁, hy₁⟩
        ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩ : A) : L) :=
    Affine.map_addY (W' := W) A.subtype (⟨x₁, hx₁⟩ : A) (⟨y₁, hy₁⟩ : A) (⟨x₂, hx₂⟩ : A)
      ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩
  rw [hY_coe]
  exact SetLike.coe_mem _

set_option maxHeartbeats 3200000 in

theorem residue_addX_of_not_inverse {x₁ y₁ x₂ y₂ : L}
    (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hy₁ : y₁ ∈ A) (hy₂ : y₂ ∈ A)
    (hred : ¬(x₁ - x₂ ∈ A.nonunits ∧
      y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A.nonunits))
    (hmem : (W.map A.subtype).toAffine.addX x₁ x₂
      ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) ∈ A) :
    residue A ⟨(W.map A.subtype).toAffine.addX x₁ x₂
        ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂), hmem⟩ =
      (W.map (residue A)).toAffine.addX (residue A ⟨x₁, hx₁⟩) (residue A ⟨x₂, hx₂⟩)
        ((W.map (residue A)).toAffine.slope (residue A ⟨x₁, hx₁⟩) (residue A ⟨x₂, hx₂⟩)
          (residue A ⟨y₁, hy₁⟩) (residue A ⟨y₂, hy₂⟩)) := by
  obtain ⟨hsmem, hsres⟩ := slope_mem_residue_of_not_inverse h₁ h₂ hx₁ hx₂ hred
  have hsres' : residue A ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩ =
      (W.map (residue A)).toAffine.slope (residue A ⟨x₁, hx₁⟩) (residue A ⟨x₂, hx₂⟩)
        (residue A ⟨y₁, hy₁⟩) (residue A ⟨y₂, hy₂⟩) := hsres
  have hX_coe : (W.map A.subtype).toAffine.addX x₁ x₂
      ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) =
      ((W.toAffine.addX ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩
        ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩ : A) : L) :=
    Affine.map_addX (W' := W) A.subtype (⟨x₁, hx₁⟩ : A) (⟨x₂, hx₂⟩ : A)
      ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩
  calc residue A ⟨(W.map A.subtype).toAffine.addX x₁ x₂
          ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂), hmem⟩
      = residue A (W.toAffine.addX ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩
          ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩) :=
        A.residue_eq_of_coe_eq hmem hX_coe
    _ = (W.map (residue A)).toAffine.addX (residue A ⟨x₁, hx₁⟩) (residue A ⟨x₂, hx₂⟩)
          (residue A ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩) :=
        (Affine.map_addX (W' := W) (residue A) (⟨x₁, hx₁⟩ : A) (⟨x₂, hx₂⟩ : A)
          ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩).symm
    _ = _ := by rw [hsres']

set_option maxHeartbeats 3200000 in

theorem residue_addY_of_not_inverse {x₁ y₁ x₂ y₂ : L}
    (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hy₁ : y₁ ∈ A) (hy₂ : y₂ ∈ A)
    (hred : ¬(x₁ - x₂ ∈ A.nonunits ∧
      y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A.nonunits))
    (hmem : (W.map A.subtype).toAffine.addY x₁ x₂ y₁
      ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) ∈ A) :
    residue A ⟨(W.map A.subtype).toAffine.addY x₁ x₂ y₁
        ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂), hmem⟩ =
      (W.map (residue A)).toAffine.addY (residue A ⟨x₁, hx₁⟩) (residue A ⟨x₂, hx₂⟩)
        (residue A ⟨y₁, hy₁⟩)
        ((W.map (residue A)).toAffine.slope (residue A ⟨x₁, hx₁⟩) (residue A ⟨x₂, hx₂⟩)
          (residue A ⟨y₁, hy₁⟩) (residue A ⟨y₂, hy₂⟩)) := by
  obtain ⟨hsmem, hsres⟩ := slope_mem_residue_of_not_inverse h₁ h₂ hx₁ hx₂ hred
  have hsres' : residue A ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩ =
      (W.map (residue A)).toAffine.slope (residue A ⟨x₁, hx₁⟩) (residue A ⟨x₂, hx₂⟩)
        (residue A ⟨y₁, hy₁⟩) (residue A ⟨y₂, hy₂⟩) := hsres
  have hY_coe : (W.map A.subtype).toAffine.addY x₁ x₂ y₁
      ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) =
      ((W.toAffine.addY ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ ⟨y₁, hy₁⟩
        ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩ : A) : L) :=
    Affine.map_addY (W' := W) A.subtype (⟨x₁, hx₁⟩ : A) (⟨y₁, hy₁⟩ : A) (⟨x₂, hx₂⟩ : A)
      ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩
  calc residue A ⟨(W.map A.subtype).toAffine.addY x₁ x₂ y₁
          ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂), hmem⟩
      = residue A (W.toAffine.addY ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ ⟨y₁, hy₁⟩
          ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩) :=
        A.residue_eq_of_coe_eq hmem hY_coe
    _ = (W.map (residue A)).toAffine.addY (residue A ⟨x₁, hx₁⟩) (residue A ⟨x₂, hx₂⟩)
          (residue A ⟨y₁, hy₁⟩)
          (residue A ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩) :=
        (Affine.map_addY (W' := W) (residue A) (⟨x₁, hx₁⟩ : A) (⟨y₁, hy₁⟩ : A)
          (⟨x₂, hx₂⟩ : A)
          ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩).symm
    _ = _ := by rw [hsres']

end CoordinatewiseEngine
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

section CaseAnalysis

variable [DecidableEq L] [DecidableEq (ResidueField A)]

set_option maxHeartbeats 6400000 in

private lemma addAux_of_mem_of_mem {x₁ y₁ x₂ y₂ : L}
    (h₁ : (W.map A.subtype).toAffine.Nonsingular x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Nonsingular x₂ y₂) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hP : W.HasNonsingularReduction (.some x₁ y₁ h₁))
    (hQ : W.HasNonsingularReduction (.some x₂ y₂ h₂)) :
    W.HasNonsingularReduction (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) ∧
      W.reducePointSmooth (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) =
        W.reducePointSmooth (.some x₁ y₁ h₁) + W.reducePointSmooth (.some x₂ y₂ h₂) := by
  have hy₁ : y₁ ∈ A := Affine.Y_mem_of_X_mem W h₁.1 hx₁
  have hy₂ : y₂ ∈ A := Affine.Y_mem_of_X_mem W h₂.1 hx₂
  have hns₁ := (W.hasNonsingularReduction_some_iff h₁).mp hP hx₁ hy₁
  have hns₂ := (W.hasNonsingularReduction_some_iff h₂).mp hQ hx₂ hy₂
  by_cases hred : x₁ - x₂ ∈ A.nonunits ∧
      y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A.nonunits
  ·

    obtain ⟨hredx, hredy⟩ := (residue_inverse_iff hx₁ hy₁ hx₂ hy₂).mpr hred
    by_cases hPQ : x₁ = x₂ ∧ y₁ = (W.map A.subtype).toAffine.negY x₂ y₂
    · constructor
      · rw [Affine.Point.add_of_Y_eq hPQ.1 hPQ.2]
        exact W.hasNonsingularReduction_zero
      · rw [Affine.Point.add_of_Y_eq hPQ.1 hPQ.2, W.reducePointSmooth_zero,
          W.reducePointSmooth_some_of_mem h₁ hx₁ hns₁, W.reducePointSmooth_some_of_mem h₂ hx₂ hns₂,
          Affine.Point.add_of_Y_eq hredx hredy]
    · have haddX := Affine.addX_notMem_of_sub_mem_nonunits_of_nonsingular_residue W h₁.1 h₂.1
        hx₁ hx₂ hy₁ hns₁ hPQ hred.1 hred.2
      constructor
      · rw [Affine.Point.add_some hPQ]
        exact W.hasNonsingularReduction_some_of_notMem _ haddX
      · rw [Affine.Point.add_some hPQ, W.reducePointSmooth_some_of_notMem _ haddX,
          W.reducePointSmooth_some_of_mem h₁ hx₁ hns₁, W.reducePointSmooth_some_of_mem h₂ hx₂ hns₂,
          Affine.Point.add_of_Y_eq hredx hredy]
  ·

    have hPQ : ¬(x₁ = x₂ ∧ y₁ = (W.map A.subtype).toAffine.negY x₂ y₂) := by
      rintro ⟨hxe, hye⟩
      exact hred ⟨by rw [hxe, sub_self]; exact A.nonunits.zero_mem,
        by rw [hye, sub_self]; exact A.nonunits.zero_mem⟩
    have hredk : ¬(residue A ⟨x₁, hx₁⟩ = residue A ⟨x₂, hx₂⟩ ∧
        residue A ⟨y₁, hy₁⟩ =
          (W.map (residue A)).toAffine.negY (residue A ⟨x₂, hx₂⟩) (residue A ⟨y₂, hy₂⟩)) :=
      fun h => hred ((residue_inverse_iff hx₁ hy₁ hx₂ hy₂).mp h)
    have hXmem : (W.map A.subtype).toAffine.addX x₁ x₂
        ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) ∈ A :=
      addX_mem_of_not_inverse h₁.1 h₂.1 hx₁ hx₂ hred
    have hYmem : (W.map A.subtype).toAffine.addY x₁ x₂ y₁
        ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) ∈ A :=
      addY_mem_of_not_inverse h₁.1 h₂.1 hx₁ hx₂ hred
    have hXres := residue_addX_of_not_inverse h₁.1 h₂.1 hx₁ hx₂ hy₁ hy₂ hred hXmem
    have hYres := residue_addY_of_not_inverse h₁.1 h₂.1 hx₁ hx₂ hy₁ hy₂ hred hYmem
    have hns₃ : (W.map (residue A)).toAffine.Nonsingular
        (residue A ⟨(W.map A.subtype).toAffine.addX x₁ x₂
          ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂), hXmem⟩)
        (residue A ⟨(W.map A.subtype).toAffine.addY x₁ x₂ y₁
          ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂), hYmem⟩) := by
      rw [hXres, hYres]
      exact Affine.nonsingular_add hns₁ hns₂ hredk
    constructor
    · rw [Affine.Point.add_some hPQ, W.hasNonsingularReduction_some_iff]
      intro hx hy
      exact hns₃
    · rw [Affine.Point.add_some hPQ, W.reducePointSmooth_some_of_mem _ hXmem hns₃,
        W.reducePointSmooth_some_of_mem h₁ hx₁ hns₁, W.reducePointSmooth_some_of_mem h₂ hx₂ hns₂,
        Affine.Point.add_some hredk]
      exact some_smoothClosure_congr hXres hYres _ _

private lemma addAux_of_notMem_of_notMem {x₁ y₁ x₂ y₂ : L}
    (h₁ : (W.map A.subtype).toAffine.Nonsingular x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Nonsingular x₂ y₂) (hx₁ : x₁ ∉ A) (hx₂ : x₂ ∉ A) :
    W.HasNonsingularReduction (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) ∧
      W.reducePointSmooth (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) =
        W.reducePointSmooth (.some x₁ y₁ h₁) + W.reducePointSmooth (.some x₂ y₂ h₂) := by
  have hPmem : (.some x₁ y₁ h₁ : (W.map A.subtype).toAffine.Point) ∈ W.nonIntegralLocus :=
    (W.mem_nonIntegralLocus_some_iff h₁).mpr hx₁
  have hQmem : (.some x₂ y₂ h₂ : (W.map A.subtype).toAffine.Point) ∈ W.nonIntegralLocus :=
    (W.mem_nonIntegralLocus_some_iff h₂).mpr hx₂
  have hSmem : (.some x₁ y₁ h₁ + .some x₂ y₂ h₂ : (W.map A.subtype).toAffine.Point) ∈
      W.nonIntegralLocus := add_mem hPmem hQmem
  refine ⟨W.hasNonsingularReduction_of_mem_nonIntegralLocus hSmem, ?_⟩
  rw [W.reducePointSmooth_eq_zero_of_mem_nonIntegralLocus hSmem,
    W.reducePointSmooth_some_of_notMem h₁ hx₁, W.reducePointSmooth_some_of_notMem h₂ hx₂,
    add_zero]

set_option maxHeartbeats 3200000 in

private lemma addAux_of_mem_of_notMem {x₁ y₁ x₂ y₂ : L}
    (h₁ : (W.map A.subtype).toAffine.Nonsingular x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Nonsingular x₂ y₂)
    (hP : W.HasNonsingularReduction (.some x₁ y₁ h₁)) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∉ A) :
    W.HasNonsingularReduction (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) ∧
      W.reducePointSmooth (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) =
        W.reducePointSmooth (.some x₁ y₁ h₁) + W.reducePointSmooth (.some x₂ y₂ h₂) := by
  have hy₁ : y₁ ∈ A := Affine.Y_mem_of_X_mem W h₁.1 hx₁
  have hns₁ := (W.hasNonsingularReduction_some_iff h₁).mp hP hx₁ hy₁

  have hPn : (W.map A.subtype).toAffine.Nonsingular x₁ ((W.map A.subtype).toAffine.negY x₁ y₁) :=
    (Affine.nonsingular_neg _ _).mpr h₁
  have hPneg : (.some x₁ ((W.map A.subtype).toAffine.negY x₁ y₁) hPn :
      (W.map A.subtype).toAffine.Point) = -(.some x₁ y₁ h₁) := (Affine.Point.neg_some h₁).symm
  cases hadd : (.some x₁ y₁ h₁ + .some x₂ y₂ h₂ : (W.map A.subtype).toAffine.Point) with
  | zero =>

    exfalso
    have hPQ : (.some x₁ y₁ h₁ : (W.map A.subtype).toAffine.Point) = -(.some x₂ y₂ h₂) :=
      eq_neg_of_add_eq_zero_left hadd
    rw [Affine.Point.neg_some] at hPQ
    simp only [Affine.Point.some.injEq] at hPQ
    exact hx₂ (hPQ.1 ▸ hx₁)
  | some X₃ Y₃ h₃ =>
    by_cases hX₃ : X₃ ∈ A
    ·

      have hY₃ : Y₃ ∈ A := Affine.Y_mem_of_X_mem W h₃.1 hX₃
      have hkey : X₃ - x₁ ∈ A.nonunits ∧
          Y₃ - (W.map A.subtype).toAffine.negY x₁ ((W.map A.subtype).toAffine.negY x₁ y₁) ∈
            A.nonunits := by
        by_contra hcon

        have hSnegP : (.some X₃ Y₃ h₃ : (W.map A.subtype).toAffine.Point) +
            .some x₁ ((W.map A.subtype).toAffine.negY x₁ y₁) hPn = .some x₂ y₂ h₂ := by
          rw [hPneg, ← hadd]; abel

        have hSP : ¬(X₃ = x₁ ∧
            Y₃ = (W.map A.subtype).toAffine.negY x₁ ((W.map A.subtype).toAffine.negY x₁ y₁)) := by
          rintro ⟨hX, hY⟩
          have h0 : (.some X₃ Y₃ h₃ : (W.map A.subtype).toAffine.Point) +
              .some x₁ ((W.map A.subtype).toAffine.negY x₁ y₁) hPn = 0 :=
            Affine.Point.add_of_Y_eq hX hY
          rw [hSnegP] at h0
          exact Affine.Point.some_ne_zero h₂ h0

        have haddX : (W.map A.subtype).toAffine.addX X₃ x₁
            ((W.map A.subtype).toAffine.slope X₃ x₁ Y₃
              ((W.map A.subtype).toAffine.negY x₁ y₁)) ∈ A :=
          addX_mem_of_not_inverse h₃.1 hPn.1 hX₃ hx₁ hcon
        rw [Affine.Point.add_some hSP] at hSnegP
        simp only [Affine.Point.some.injEq] at hSnegP
        exact hx₂ (hSnegP.1 ▸ haddX)
      rw [Affine.negY_negY] at hkey
      have hXres : residue A ⟨X₃, hX₃⟩ = residue A ⟨x₁, hx₁⟩ :=
        (A.residue_eq_residue_iff_sub_mem_nonunits hX₃ hx₁).mpr hkey.1
      have hYres : residue A ⟨Y₃, hY₃⟩ = residue A ⟨y₁, hy₁⟩ :=
        (A.residue_eq_residue_iff_sub_mem_nonunits hY₃ hy₁).mpr hkey.2
      have hnsS : (W.map (residue A)).toAffine.Nonsingular (residue A ⟨X₃, hX₃⟩)
          (residue A ⟨Y₃, hY₃⟩) := by
        rw [hXres, hYres]
        exact hns₁
      constructor
      · rw [W.hasNonsingularReduction_some_iff]
        intro hx hy
        exact hnsS
      · rw [W.reducePointSmooth_some_of_mem h₃ hX₃ hnsS,
          W.reducePointSmooth_some_of_notMem h₂ hx₂,
          W.reducePointSmooth_some_of_mem h₁ hx₁ hns₁, add_zero]
        exact some_smoothClosure_congr hXres hYres _ _
    ·
      exfalso
      have hS : (.some X₃ Y₃ h₃ : (W.map A.subtype).toAffine.Point) ∈ W.nonIntegralLocus :=
        (W.mem_nonIntegralLocus_some_iff h₃).mpr hX₃
      have hQmem : (.some x₂ y₂ h₂ : (W.map A.subtype).toAffine.Point) ∈ W.nonIntegralLocus :=
        (W.mem_nonIntegralLocus_some_iff h₂).mpr hx₂
      have hPmem : (.some x₁ y₁ h₁ : (W.map A.subtype).toAffine.Point) ∈ W.nonIntegralLocus := by
        have hPeq : (.some x₁ y₁ h₁ : (W.map A.subtype).toAffine.Point) =
            .some X₃ Y₃ h₃ - .some x₂ y₂ h₂ := by
          rw [← hadd]; abel
        rw [hPeq]
        exact sub_mem hS hQmem
      exact ((W.mem_nonIntegralLocus_some_iff h₁).mp hPmem) hx₁

end CaseAnalysis
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

section Closure

variable [DecidableEq L] [DecidableEq (ResidueField A)]

private theorem _root_.WeierstrassCurve.hasNonsingularReduction_add {P Q : (W.map A.subtype).toAffine.Point}
    (hP : W.HasNonsingularReduction P) (hQ : W.HasNonsingularReduction Q) :
    W.HasNonsingularReduction (P + Q) := by
  cases P with
  | zero =>
    show W.HasNonsingularReduction ((0 : (W.map A.subtype).toAffine.Point) + Q)
    rw [zero_add]
    exact hQ
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      show W.HasNonsingularReduction (.some x₁ y₁ h₁ + (0 : (W.map A.subtype).toAffine.Point))
      rw [add_zero]
      exact hP
    | some x₂ y₂ h₂ =>
      by_cases hx₁ : x₁ ∈ A <;> by_cases hx₂ : x₂ ∈ A
      · exact (addAux_of_mem_of_mem h₁ h₂ hx₁ hx₂ hP hQ).1
      · exact (addAux_of_mem_of_notMem h₁ h₂ hP hx₁ hx₂).1
      · rw [add_comm (Affine.Point.some x₁ y₁ h₁) (Affine.Point.some x₂ y₂ h₂)]
        exact (addAux_of_mem_of_notMem h₂ h₁ hQ hx₂ hx₁).1
      · exact (addAux_of_notMem_of_notMem h₁ h₂ hx₁ hx₂).1

p2m_export "WeierstrassCurve" "hasNonsingularReduction_add"

private theorem _root_.WeierstrassCurve.reducePointSmooth_add_of_hasNonsingularReduction
    {P Q : (W.map A.subtype).toAffine.Point}
    (hP : W.HasNonsingularReduction P) (hQ : W.HasNonsingularReduction Q) :
    W.reducePointSmooth (P + Q) = W.reducePointSmooth P + W.reducePointSmooth Q := by
  cases P with
  | zero =>
    show W.reducePointSmooth ((0 : (W.map A.subtype).toAffine.Point) + Q) =
      W.reducePointSmooth (0 : (W.map A.subtype).toAffine.Point) + W.reducePointSmooth Q
    rw [zero_add, W.reducePointSmooth_zero, zero_add]
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      show W.reducePointSmooth (.some x₁ y₁ h₁ + (0 : (W.map A.subtype).toAffine.Point)) =
        W.reducePointSmooth (.some x₁ y₁ h₁) +
          W.reducePointSmooth (0 : (W.map A.subtype).toAffine.Point)
      rw [add_zero, W.reducePointSmooth_zero, add_zero]
    | some x₂ y₂ h₂ =>
      by_cases hx₁ : x₁ ∈ A <;> by_cases hx₂ : x₂ ∈ A
      · exact (addAux_of_mem_of_mem h₁ h₂ hx₁ hx₂ hP hQ).2
      · exact (addAux_of_mem_of_notMem h₁ h₂ hP hx₁ hx₂).2
      · rw [add_comm (Affine.Point.some x₁ y₁ h₁) (Affine.Point.some x₂ y₂ h₂),
          (addAux_of_mem_of_notMem h₂ h₁ hQ hx₂ hx₁).2]
        exact add_comm _ _
      · exact (addAux_of_notMem_of_notMem h₁ h₂ hx₁ hx₂).2

p2m_export "WeierstrassCurve" "reducePointSmooth_add_of_hasNonsingularReduction"
end Closure
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY Affine.Y_eq_of_Y_ne Affine.slope_of_X_ne Affine.equation_neg a₃ Affine.Point.add_of_Y_eq Affine.addPolynomial_slope a₁ map Affine.equation_iff_nonsingular_of_Δ_ne_zero Affine.nonsingular_iff a₄ a₂ a₆ Affine.Point.some Affine.Point.some.injEq Affine.Point.neg_zero Affine.negAddY Affine.Point.zero_def reduction Affine.map_addY Affine.negY_negY Affine.map_addX Affine.nonsingular_add toAffine Affine.slope_of_Y_ne Affine.Point Affine.addX Affine.Point.add_some Affine.nonsingular_neg map_Δ Affine.addPolynomial_eq Affine.Point.map Affine.Point.some_ne_zero Δ Affine.map_negY Affine.Y_eq_of_X_eq Affine.equation_iff Affine.map_nonsingular Affine.Point.neg_some j InZeroComponentAt"
p2m_open "WeierstrassCurve"

variable {L : Type*} [Field L] {A : ValuationSubring L} (W : WeierstrassCurve A)

section Carrier

variable [DecidableEq L] [DecidableEq (ResidueField A)]

private def _root_.WeierstrassCurve.zeroComponentSubgroup : AddSubgroup (W.map A.subtype).toAffine.Point where
  carrier := {P | W.HasNonsingularReduction P}
  zero_mem' := W.hasNonsingularReduction_zero
  neg_mem' := fun {_P} hP => W.hasNonsingularReduction_neg hP
  add_mem' := fun {_P _Q} hP hQ => W.hasNonsingularReduction_add hP hQ

p2m_export "WeierstrassCurve" "zeroComponentSubgroup"
@[scoped simp]
theorem mem_zeroComponentSubgroup_iff {P : (W.map A.subtype).toAffine.Point} :
    P ∈ W.zeroComponentSubgroup ↔ W.HasNonsingularReduction P := Iff.rfl

theorem zeroComponentSubgroup_eq_top_of_good (hΔ : (W.map (residue A)).Δ ≠ 0) :
    W.zeroComponentSubgroup = ⊤ := by
  refine AddSubgroup.ext fun P => ?_
  simp only [AddSubgroup.mem_top, iff_true]
  exact W.hasNonsingularReduction_of_good hΔ P

theorem nonIntegralLocus_le_zeroComponentSubgroup :
    W.nonIntegralLocus ≤ W.zeroComponentSubgroup := fun _ hP =>
  W.hasNonsingularReduction_of_mem_nonIntegralLocus hP

private theorem _root_.WeierstrassCurve.mem_zeroComponentSubgroup_iff_disj {P : (W.map A.subtype).toAffine.Point} :
    P ∈ W.zeroComponentSubgroup ↔
      (P = 0 ∨ ∃ (x y : L) (h : (W.map A.subtype).toAffine.Nonsingular x y),
        P = .some x y h ∧ (x ∉ A ∨ ∃ (hx : x ∈ A) (hy : y ∈ A),
          (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩))) := by
  rw [mem_zeroComponentSubgroup_iff]
  cases P with
  | zero => exact ⟨fun _ => Or.inl rfl, fun _ => W.hasNonsingularReduction_zero⟩
  | some x y h =>
    rw [W.hasNonsingularReduction_some_iff h]
    constructor
    · intro H
      right
      by_cases hx : x ∈ A
      · exact ⟨x, y, h, rfl, Or.inr ⟨hx, Affine.Y_mem_of_X_mem W h.1 hx,
          H hx (Affine.Y_mem_of_X_mem W h.1 hx)⟩⟩
      · exact ⟨x, y, h, rfl, Or.inl hx⟩
    · rintro (h0 | ⟨x', y', h', heq, hor⟩)
      · exact absurd h0 (Affine.Point.some_ne_zero h)
      · obtain ⟨rfl, rfl⟩ : x = x' ∧ y = y' := by rwa [Affine.Point.some.injEq] at heq
        intro hx hy
        rcases hor with hx' | ⟨hx', hy', hns⟩
        · exact absurd hx hx'
        · exact hns

p2m_export "WeierstrassCurve" "mem_zeroComponentSubgroup_iff_disj"
omit [DecidableEq (ResidueField A)] in

theorem mem_nonIntegralLocus_iff_disj {P : (W.map A.subtype).toAffine.Point} :
    P ∈ W.nonIntegralLocus ↔
      (P = 0 ∨ ∃ (x y : L) (h : (W.map A.subtype).toAffine.Nonsingular x y),
        P = .some x y h ∧ x ∉ A) := by
  cases P with
  | zero => exact ⟨fun _ => Or.inl rfl, fun _ => W.nonIntegralLocus.zero_mem⟩
  | some x y h =>
    rw [W.mem_nonIntegralLocus_some_iff h]
    constructor
    · intro hx
      exact Or.inr ⟨x, y, h, rfl, hx⟩
    · rintro (h0 | ⟨x', y', h', heq, hx'⟩)
      · exact absurd h0 (Affine.Point.some_ne_zero h)
      · obtain ⟨rfl, rfl⟩ : x = x' ∧ y = y' := by rwa [Affine.Point.some.injEq] at heq
        exact hx'

private noncomputable def _root_.WeierstrassCurve.zeroComponentReduction :
    W.zeroComponentSubgroup →+ (W.map (residue A)).toAffine.Point where
  toFun P := W.reducePointSmooth P.1
  map_zero' := W.reducePointSmooth_zero
  map_add' P Q := W.reducePointSmooth_add_of_hasNonsingularReduction P.2 Q.2

p2m_export "WeierstrassCurve" "zeroComponentReduction"
theorem zeroComponentReduction_apply (P : W.zeroComponentSubgroup) :
    W.zeroComponentReduction P = W.reducePointSmooth P.1 := rfl

theorem zeroComponentReduction_some {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y)
    (hx : x ∈ A) (hy : y ∈ A)
    (hns : (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩))
    (hmem : (.some x y h : (W.map A.subtype).toAffine.Point) ∈ W.zeroComponentSubgroup) :
    W.zeroComponentReduction ⟨.some x y h, hmem⟩ =
      .some (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩) hns :=
  W.reducePointSmooth_some_of_mem h hx hns

theorem zeroComponentReduction_eq_zero_iff_mem (P : W.zeroComponentSubgroup) :
    W.zeroComponentReduction P = 0 ↔ (P : (W.map A.subtype).toAffine.Point) ∈ W.nonIntegralLocus :=
  ⟨fun h0 => W.mem_nonIntegralLocus_of_reducePointSmooth_eq_zero P.2 h0,
    fun hP => W.reducePointSmooth_eq_zero_of_mem_nonIntegralLocus hP⟩

theorem zeroComponentReduction_eq_zero_iff (P : W.zeroComponentSubgroup) :
    W.zeroComponentReduction P = 0 ↔
      ((P : (W.map A.subtype).toAffine.Point) = 0 ∨
        ∃ (x y : L) (h : (W.map A.subtype).toAffine.Nonsingular x y),
          (P : (W.map A.subtype).toAffine.Point) = .some x y h ∧ x ∉ A) := by
  rw [zeroComponentReduction_eq_zero_iff_mem, mem_nonIntegralLocus_iff_disj]

omit [DecidableEq (ResidueField A)] in

theorem eq_zero_of_mem_nonIntegralLocus_of_nsmul_eq_zero {n : ℕ} (hn : (n : ResidueField A) ≠ 0)
    {P : (W.map A.subtype).toAffine.Point} (hP : P ∈ W.nonIntegralLocus) (hnP : n • P = 0) :
    P = 0 := by
  cases P with
  | zero => rfl
  | some x y h =>
    exact absurd (X_mem_of_nsmul_eq_zero' W hn h hnP) ((W.mem_nonIntegralLocus_some_iff h).mp hP)

end Carrier
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

section Galois

variable {K : Type*} [Field K] [Algebra K L]

theorem residue_decomp_smul {σ : L ≃ₐ[K] L} (hσ : σ ∈ A.decompositionSubgroup K) {a : L}
    (ha : a ∈ A) :
    residue A ⟨σ a, A.smul_mem_of_mem_decompositionSubgroup K hσ ha⟩ =
      (MulSemiringAction.toRingHom (A.decompositionSubgroup K) (ResidueField A) ⟨σ, hσ⟩)
        (residue A ⟨a, ha⟩) := by
  rfl

private theorem _root_.WeierstrassCurve.hasNonsingularReduction_decomp_smul {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.decompositionSubgroup K)
    (ha₁ : σ (W.a₁ : L) = W.a₁) (ha₂ : σ (W.a₂ : L) = W.a₂) (ha₃ : σ (W.a₃ : L) = W.a₃)
    (ha₄ : σ (W.a₄ : L) = W.a₄) (ha₆ : σ (W.a₆ : L) = W.a₆)
    {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y)
    (h' : (W.map A.subtype).toAffine.Nonsingular (σ x) (σ y))
    (hP : W.HasNonsingularReduction (.some x y h)) :
    W.HasNonsingularReduction (.some (σ x) (σ y) h') := by
  rw [W.hasNonsingularReduction_some_iff] at hP ⊢
  intro hσx hσy
  have hx : x ∈ A := by
    simpa using A.smul_mem_of_mem_decompositionSubgroup K (inv_mem hσ) hσx
  have hy : y ∈ A := by
    simpa using A.smul_mem_of_mem_decompositionSubgroup K (inv_mem hσ) hσy
  have hns := hP hx hy

  set g : ResidueField A →+* ResidueField A :=
    MulSemiringAction.toRingHom (A.decompositionSubgroup K) (ResidueField A) ⟨σ, hσ⟩ with hg
  have hginj : Function.Injective g := g.injective

  have hfix : ∀ (a : A), σ (a : L) = a → g (residue A a) = residue A a := by
    intro a ha
    rw [hg, ← residue_decomp_smul hσ a.2]
    exact congrArg (residue A) (Subtype.ext ha)
  have hcurve : (W.map (residue A)).map g = W.map (residue A) := by
    ext
    · exact hfix W.a₁ ha₁
    · exact hfix W.a₂ ha₂
    · exact hfix W.a₃ ha₃
    · exact hfix W.a₄ ha₄
    · exact hfix W.a₆ ha₆

  have key := (Affine.map_nonsingular (W := (W.map (residue A)).toAffine) hginj
    (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩)).mpr hns
  rw [show ((W.map (residue A)).toAffine.map g) = ((W.map (residue A)).map g).toAffine from rfl,
    hcurve] at key
  have ex : residue A ⟨σ x, hσx⟩ = g (residue A ⟨x, hx⟩) := residue_decomp_smul hσ hx
  have ey : residue A ⟨σ y, hσy⟩ = g (residue A ⟨y, hy⟩) := residue_decomp_smul hσ hy
  rw [ex, ey]
  exact key

p2m_export "WeierstrassCurve" "hasNonsingularReduction_decomp_smul"

private theorem _root_.WeierstrassCurve.reducePointSmooth_some_apply_of_mem_inertia {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.decompositionSubgroup K)
    (hσI : (⟨σ, hσ⟩ : A.decompositionSubgroup K) ∈ A.inertiaSubgroup K)
    {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y)
    (h' : (W.map A.subtype).toAffine.Nonsingular (σ x) (σ y)) :
    W.reducePointSmooth (.some (σ x) (σ y) h') = W.reducePointSmooth (.some x y h) := by
  by_cases hx : x ∈ A
  · have hy : y ∈ A := Affine.Y_mem_of_X_mem W h.1 hx
    have hσx : σ x ∈ A := A.smul_mem_of_mem_decompositionSubgroup K hσ hx
    have hσy : σ y ∈ A := A.smul_mem_of_mem_decompositionSubgroup K hσ hy
    have ex : residue A ⟨σ x, hσx⟩ = residue A ⟨x, hx⟩ :=
      A.residue_smul_eq_of_mem_inertiaSubgroup hσ hσI ⟨x, hx⟩
    have ey : residue A ⟨σ y, hσy⟩ = residue A ⟨y, hy⟩ :=
      A.residue_smul_eq_of_mem_inertiaSubgroup hσ hσI ⟨y, hy⟩
    by_cases hns : (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x, hx⟩)
        (residue A ⟨y, hy⟩)
    · have hns' : (W.map (residue A)).toAffine.Nonsingular (residue A ⟨σ x, hσx⟩)
          (residue A ⟨σ y, hσy⟩) := by rw [ex, ey]; exact hns
      rw [W.reducePointSmooth_some_of_mem h' hσx hns', W.reducePointSmooth_some_of_mem h hx hns]
      exact some_congr ex ey _ _
    · have hns' : ¬ (W.map (residue A)).toAffine.Nonsingular (residue A ⟨σ x, hσx⟩)
          (residue A ⟨σ y, hσy⟩) := by rw [ex, ey]; exact hns
      rw [W.reducePointSmooth_some_of_singular h' hσx hns',
        W.reducePointSmooth_some_of_singular h hx hns]
  · have hσx : σ x ∉ A := fun hmem => hx (by
      simpa using A.smul_mem_of_mem_decompositionSubgroup K (inv_mem hσ) hmem)
    rw [W.reducePointSmooth_some_of_notMem h' hσx, W.reducePointSmooth_some_of_notMem h hx]

p2m_export "WeierstrassCurve" "reducePointSmooth_some_apply_of_mem_inertia"
end Galois
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

namespace ValuationSubring
p2m_export "ValuationSubring" "subtype coe_mem_nonunits_iff neg_mem inertiaSubgroup toSubring ext mem_nonunits_iff_or zero_mem nonunits mem_nonunits_iff smul_mem_pointwise_smul inv_mem_nonunits_iff mem_top mul_mem one_mem mem_or_inv_mem nonunits_subset add_mem decompositionSubgroup valuation_le_one_iff algebra valuation subtype_injective LiesOverPrime smul_mem_of_mem_decompositionSubgroup residue_smul_eq_of_mem_inertiaSubgroup"
p2m_open "ValuationSubring"

theorem charP_residueField_of_liesOverPrime {L : Type*} [Field L] (A : ValuationSubring L)
    {q : ℕ} (hq : q.Prime) (hA : A.LiesOverPrime q) :
    CharP (IsLocalRing.ResidueField A) q :=
  (CharP.charP_iff_prime_eq_zero hq).mpr ((A.natCast_mem_nonunits_iff_residue_eq_zero q).mp hA)

end ValuationSubring
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY Affine.Y_eq_of_Y_ne Affine.slope_of_X_ne Affine.equation_neg a₃ Affine.Point.add_of_Y_eq Affine.addPolynomial_slope a₁ map Affine.equation_iff_nonsingular_of_Δ_ne_zero Affine.nonsingular_iff a₄ a₂ a₆ Affine.Point.some Affine.Point.some.injEq Affine.Point.neg_zero Affine.negAddY Affine.Point.zero_def reduction Affine.map_addY Affine.negY_negY Affine.map_addX Affine.nonsingular_add toAffine Affine.slope_of_Y_ne Affine.Point Affine.addX Affine.Point.add_some Affine.nonsingular_neg map_Δ Affine.addPolynomial_eq Affine.Point.map Affine.Point.some_ne_zero Δ Affine.map_negY Affine.Y_eq_of_X_eq Affine.equation_iff Affine.map_nonsingular Affine.Point.neg_some j InZeroComponentAt"
p2m_open "WeierstrassCurve"

p2m_open "IsLocalRing WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve.Affine WeierstrassCurve.Affine.Point"

section TFBridge

variable (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ))

private noncomputable def _root_.WeierstrassCurve.tfModel : WeierstrassCurve A :=
  ⟨⟨algebraMap ℚ (AlgebraicClosure ℚ) ((W.map (Int.castRingHom ℚ)).a₁), by
      show algebraMap ℚ (AlgebraicClosure ℚ) ((Int.castRingHom ℚ) W.a₁) ∈ A
      rw [eq_intCast, map_intCast]; exact intCast_mem A _⟩,
   ⟨algebraMap ℚ (AlgebraicClosure ℚ) ((W.map (Int.castRingHom ℚ)).a₂), by
      show algebraMap ℚ (AlgebraicClosure ℚ) ((Int.castRingHom ℚ) W.a₂) ∈ A
      rw [eq_intCast, map_intCast]; exact intCast_mem A _⟩,
   ⟨algebraMap ℚ (AlgebraicClosure ℚ) ((W.map (Int.castRingHom ℚ)).a₃), by
      show algebraMap ℚ (AlgebraicClosure ℚ) ((Int.castRingHom ℚ) W.a₃) ∈ A
      rw [eq_intCast, map_intCast]; exact intCast_mem A _⟩,
   ⟨algebraMap ℚ (AlgebraicClosure ℚ) ((W.map (Int.castRingHom ℚ)).a₄), by
      show algebraMap ℚ (AlgebraicClosure ℚ) ((Int.castRingHom ℚ) W.a₄) ∈ A
      rw [eq_intCast, map_intCast]; exact intCast_mem A _⟩,
   ⟨algebraMap ℚ (AlgebraicClosure ℚ) ((W.map (Int.castRingHom ℚ)).a₆), by
      show algebraMap ℚ (AlgebraicClosure ℚ) ((Int.castRingHom ℚ) W.a₆) ∈ A
      rw [eq_intCast, map_intCast]; exact intCast_mem A _⟩⟩

p2m_export "WeierstrassCurve" "tfModel"

theorem tfModel_map_subtype :
    (W.tfModel A).map A.subtype = (W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ) :=
  rfl

private theorem residue_mk_algebraMap_intCast (z : ℤ)
    (hz : algebraMap ℚ (AlgebraicClosure ℚ) ((Int.castRingHom ℚ) z) ∈ A) :
    residue A ⟨algebraMap ℚ (AlgebraicClosure ℚ) ((Int.castRingHom ℚ) z), hz⟩ =
      (z : ResidueField A) := by
  have : (⟨algebraMap ℚ (AlgebraicClosure ℚ) ((Int.castRingHom ℚ) z), hz⟩ : A) = (z : A) := by
    apply Subtype.ext
    push_cast
    rw [eq_intCast, map_intCast]
  rw [this, map_intCast]

theorem tfModel_map_residue :
    (W.tfModel A).map (residue A) = W.map (Int.castRingHom (ResidueField A)) := by
  ext
  · exact (residue_mk_algebraMap_intCast A W.a₁ _).trans (map_intCast _ _).symm
  · exact (residue_mk_algebraMap_intCast A W.a₂ _).trans (map_intCast _ _).symm
  · exact (residue_mk_algebraMap_intCast A W.a₃ _).trans (map_intCast _ _).symm
  · exact (residue_mk_algebraMap_intCast A W.a₄ _).trans (map_intCast _ _).symm
  · exact (residue_mk_algebraMap_intCast A W.a₆ _).trans (map_intCast _ _).symm

private theorem _root_.WeierstrassCurve.inZeroComponentAt_iff_mem_zeroComponentSubgroup [DecidableEq (ResidueField A)]
    (P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) :
    W.InZeroComponentAt A P ↔
      (P : ((W.tfModel A).map A.subtype).toAffine.Point) ∈ (W.tfModel A).zeroComponentSubgroup := by
  refine Iff.trans ?_ ((W.tfModel A).mem_zeroComponentSubgroup_iff_disj (P := P)).symm
  rw [tfModel_map_residue]
  exact Iff.rfl

p2m_export "WeierstrassCurve" "inZeroComponentAt_iff_mem_zeroComponentSubgroup"

private theorem _root_.WeierstrassCurve.smul_mem_zeroComponentSubgroup_tfModel [DecidableEq (ResidueField A)]
    {σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)} (hσ : σ ∈ A.decompositionSubgroup ℚ)
    {P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point}
    (hP : (P : ((W.tfModel A).map A.subtype).toAffine.Point) ∈ (W.tfModel A).zeroComponentSubgroup) :
    ((σ • P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) :
      ((W.tfModel A).map A.subtype).toAffine.Point) ∈ (W.tfModel A).zeroComponentSubgroup := by
  rcases P with _ | ⟨x, y, h⟩
  · exact (W.tfModel A).zeroComponentSubgroup.zero_mem
  · exact (W.tfModel A).hasNonsingularReduction_decomp_smul hσ (σ.commutes _) (σ.commutes _)
      (σ.commutes _) (σ.commutes _) (σ.commutes _) h _ hP

p2m_export "WeierstrassCurve" "smul_mem_zeroComponentSubgroup_tfModel"

theorem smul_sub_mem_nonIntegralLocus_tfModel [DecidableEq (ResidueField A)]
    {σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)} (hσ : σ ∈ A.decompositionSubgroup ℚ)
    (hσI : (⟨σ, hσ⟩ : A.decompositionSubgroup ℚ) ∈ A.inertiaSubgroup ℚ)
    {P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point}
    (hP : (P : ((W.tfModel A).map A.subtype).toAffine.Point) ∈ (W.tfModel A).zeroComponentSubgroup) :
    ((σ • P - P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) :
      ((W.tfModel A).map A.subtype).toAffine.Point) ∈ (W.tfModel A).nonIntegralLocus := by
  have hσP := W.smul_mem_zeroComponentSubgroup_tfModel A hσ hP
  have hnP : ((-P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) :
      ((W.tfModel A).map A.subtype).toAffine.Point) ∈ (W.tfModel A).zeroComponentSubgroup :=
    (W.tfModel A).zeroComponentSubgroup.neg_mem hP
  have hD : ((σ • P - P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) :
      ((W.tfModel A).map A.subtype).toAffine.Point) ∈ (W.tfModel A).zeroComponentSubgroup :=
    (W.tfModel A).zeroComponentSubgroup.sub_mem hσP hP
  refine (W.tfModel A).mem_nonIntegralLocus_of_reducePointSmooth_eq_zero hD ?_

  have hred : (W.tfModel A).reducePointSmooth (σ • P) = (W.tfModel A).reducePointSmooth P := by
    rcases P with _ | ⟨x, y, h⟩
    · rfl
    · exact (W.tfModel A).reducePointSmooth_some_apply_of_mem_inertia hσ hσI h _
  have e1 : (W.tfModel A).reducePointSmooth (σ • P - P) =
      (W.tfModel A).reducePointSmooth (σ • P + -P) := by rw [sub_eq_add_neg]
  have e2 : (W.tfModel A).reducePointSmooth (σ • P + -P) =
      (W.tfModel A).reducePointSmooth (σ • P) + (W.tfModel A).reducePointSmooth (-P) :=
    (W.tfModel A).reducePointSmooth_add_of_hasNonsingularReduction hσP hnP
  have e3 : (W.tfModel A).reducePointSmooth (-P) = -(W.tfModel A).reducePointSmooth P :=
    (W.tfModel A).reducePointSmooth_neg P
  rw [e1, e2, e3, hred, add_neg_cancel]

end TFBridge
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve"

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_inZeroComponentAt_smul.WeierstrassCurve.Affine WeierstrassCurve.Affine.Point"

theorem solution
    (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ))
    {σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)} (hσ : σ ∈ A.decompositionSubgroup ℚ)
    {P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point}
    (hP : W.InZeroComponentAt A P) : W.InZeroComponentAt A (σ • P) := by
  classical
  rw [W.inZeroComponentAt_iff_mem_zeroComponentSubgroup A] at hP ⊢
  exact W.smul_mem_zeroComponentSubgroup_tfModel A hσ hP

end S_WeierstrassCurve_inZeroComponentAt_smul
end P2MW
export P2MW.S_WeierstrassCurve_inZeroComponentAt_smul (solution)
