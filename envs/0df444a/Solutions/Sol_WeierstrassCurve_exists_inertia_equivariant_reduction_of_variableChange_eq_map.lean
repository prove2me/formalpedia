-- Prove2me | solution 1 for WeierstrassCurve.exists_inertia_equivariant_reduction_of_variableChange_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/cb30f033-f0c9-531e-8237-338105a40f0e

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_ZeroComponentReduction
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_inertia_equivariant_reduction_of_variableChange_eq_map

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point IsLocalRing ValuationSubring

namespace P2MKcSerreTate

section Cast

variable {R : Type*} [CommRing R]

def castPt {V₁ V₂ : Affine R} (h : V₁ = V₂) : V₁.Point → V₂.Point
  | .zero => .zero
  | .some x y hns => .some x y (h ▸ hns)

@[scoped simp] lemma castPt_zero {V₁ V₂ : Affine R} (h : V₁ = V₂) :
    castPt h (0 : V₁.Point) = 0 := rfl

lemma castPt_some {V₁ V₂ : Affine R} (h : V₁ = V₂) {x y : R} (hns : V₁.Nonsingular x y) :
    castPt h (.some x y hns) = .some x y (h ▸ hns) := rfl

lemma castPt_rfl {V : Affine R} (P : V.Point) : castPt rfl P = P := by
  cases P <;> rfl

lemma heq_castPt {V₁ V₂ : Affine R} (h : V₁ = V₂) (P : V₁.Point) : HEq P (castPt h P) := by
  subst h; rw [castPt_rfl]

lemma castPt_eq_zero_iff {V₁ V₂ : Affine R} (h : V₁ = V₂) (P : V₁.Point) :
    castPt h P = 0 ↔ P = 0 := by
  subst h; rw [castPt_rfl]

lemma some_congr {V : Affine R} {x₁ x₂ y₁ y₂ : R} (hx : x₁ = x₂) (hy : y₁ = y₂)
    (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

lemma heq_some_of_eq {V₁ V₂ : Affine R} (hV : V₁ = V₂) {x₁ x₂ y₁ y₂ : R} (hx : x₁ = x₂)
    (hy : y₁ = y₂) (h₁ : V₁.Nonsingular x₁ y₁) (h₂ : V₂.Nonsingular x₂ y₂) :
    HEq (Point.some x₁ y₁ h₁) (Point.some x₂ y₂ h₂) := by
  subst hV; subst hx; subst hy; rfl

lemma heq_zero_of_eq {V₁ V₂ : Affine R} (hV : V₁ = V₂) :
    HEq (0 : V₁.Point) (0 : V₂.Point) := by
  subst hV; rfl

variable {F' : Type*} [Field F'] [DecidableEq F']

lemma castPt_add {V₁ V₂ : Affine F'} (h : V₁ = V₂) (P Q : V₁.Point) :
    castPt h (P + Q) = castPt h P + castPt h Q := by
  subst h; simp only [castPt_rfl]

def castAddHom {V₁ V₂ : Affine F'} (h : V₁ = V₂) : V₁.Point →+ V₂.Point where
  toFun := castPt h
  map_zero' := castPt_zero h
  map_add' := castPt_add h

@[scoped simp] lemma castAddHom_apply {V₁ V₂ : Affine F'} (h : V₁ = V₂) (P : V₁.Point) :
    castAddHom h P = castPt h P := rfl

end Cast

section Coord

variable {K : Type*} [Field K]

lemma vcXInv_mul (C C' : VariableChange K) (x : K) :
    vcXInv (C * C') x = vcXInv C (vcXInv C' x) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  have hu' : (C'.u : K) ≠ 0 := C'.u.ne_zero
  simp only [vcXInv, VariableChange.mul_def, Units.val_inv_eq_inv_val, Units.val_mul]
  field_simp
  ring

lemma vcYInv_mul (C C' : VariableChange K) (x y : K) :
    vcYInv (C * C') x y = vcYInv C (vcXInv C' x) (vcYInv C' x y) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  have hu' : (C'.u : K) ≠ 0 := C'.u.ne_zero
  simp only [vcXInv, vcYInv, VariableChange.mul_def, Units.val_inv_eq_inv_val, Units.val_mul]
  field_simp
  ring

variable {K' : Type*} [Field K'] (φ : K →+* K')

lemma map_vcXInv (C : VariableChange K) (x : K) :
    φ (vcXInv C x) = vcXInv (C.map φ) (φ x) := by
  simp only [vcXInv, VariableChange.map, Units.coe_map_inv, map_mul, map_pow, map_sub]
  rfl

lemma map_vcYInv (C : VariableChange K) (x y : K) :
    φ (vcYInv C x y) = vcYInv (C.map φ) (φ x) (φ y) := by
  simp only [vcYInv, VariableChange.map, Units.coe_map_inv, map_mul, map_pow, map_sub]
  rfl

end Coord

section IntegralCoord

variable {M : Type*} [Field M] {A : ValuationSubring M}

lemma coe_map_u (C₀ : VariableChange A) :
    (((C₀.map A.subtype).u : Mˣ) : M) = ((C₀.u : Aˣ) : A) := rfl

lemma coe_map_u_inv (C₀ : VariableChange A) :
    (((C₀.map A.subtype).u⁻¹ : Mˣ) : M) = ((C₀.u⁻¹ : Aˣ) : A) := by
  simp only [VariableChange.map, Units.coe_map_inv]; rfl

lemma vcXInv_map_subtype (C₀ : VariableChange A) (x : M) :
    vcXInv (C₀.map A.subtype) x = ((C₀.u⁻¹ : Aˣ) : A) ^ 2 * (x - (C₀.r : M)) := by
  rw [vcXInv, coe_map_u_inv]; rfl

lemma vcYInv_map_subtype (C₀ : VariableChange A) (x y : M) :
    vcYInv (C₀.map A.subtype) x y =
      ((C₀.u⁻¹ : Aˣ) : A) ^ 3 * (y - (C₀.t : M) - (C₀.s : M) * (x - (C₀.r : M))) := by
  rw [vcYInv, coe_map_u_inv]; rfl

lemma vcXInv_mem_iff (C₀ : VariableChange A) (x : M) :
    vcXInv (C₀.map A.subtype) x ∈ A ↔ x ∈ A := by
  constructor
  · intro h
    have hx : x = vcX (C₀.map A.subtype) (vcXInv (C₀.map A.subtype) x) := (vcX_vcXInv x).symm
    rw [hx, vcX, coe_map_u]
    exact add_mem (mul_mem (pow_mem (SetLike.coe_mem _) 2) h) (SetLike.coe_mem C₀.r)
  · intro hx
    rw [vcXInv_map_subtype]
    exact mul_mem (pow_mem (SetLike.coe_mem _) 2) (sub_mem hx (SetLike.coe_mem C₀.r))

lemma vcYInv_mem (C₀ : VariableChange A) {x y : M} (hx : x ∈ A) (hy : y ∈ A) :
    vcYInv (C₀.map A.subtype) x y ∈ A := by
  rw [vcYInv_map_subtype]
  exact mul_mem (pow_mem (SetLike.coe_mem _) 3)
    (sub_mem (sub_mem hy (SetLike.coe_mem C₀.t))
      (mul_mem (SetLike.coe_mem C₀.s) (sub_mem hx (SetLike.coe_mem C₀.r))))

lemma residue_vcXInv (C₀ : VariableChange A) {x : M} (hx : x ∈ A)
    (h : vcXInv (C₀.map A.subtype) x ∈ A) :
    residue A ⟨vcXInv (C₀.map A.subtype) x, h⟩ =
      vcXInv (C₀.map (residue A)) (residue A ⟨x, hx⟩) := by
  have hA : (⟨vcXInv (C₀.map A.subtype) x, h⟩ : A) =
      ((C₀.u⁻¹ : Aˣ) : A) ^ 2 * (⟨x, hx⟩ - C₀.r) := by
    apply Subtype.ext
    show vcXInv (C₀.map A.subtype) x = _
    rw [vcXInv_map_subtype]
    push_cast
    ring
  rw [hA, vcXInv, VariableChange.map, Units.coe_map_inv, map_mul, map_pow, map_sub]
  rfl

lemma residue_vcYInv (C₀ : VariableChange A) {x y : M} (hx : x ∈ A) (hy : y ∈ A)
    (h : vcYInv (C₀.map A.subtype) x y ∈ A) :
    residue A ⟨vcYInv (C₀.map A.subtype) x y, h⟩ =
      vcYInv (C₀.map (residue A)) (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩) := by
  have hA : (⟨vcYInv (C₀.map A.subtype) x y, h⟩ : A) =
      ((C₀.u⁻¹ : Aˣ) : A) ^ 3 * (⟨y, hy⟩ - C₀.t - C₀.s * (⟨x, hx⟩ - C₀.r)) := by
    apply Subtype.ext
    show vcYInv (C₀.map A.subtype) x y = _
    rw [vcYInv_map_subtype]
    push_cast
    ring
  rw [hA, vcYInv, VariableChange.map, Units.coe_map_inv]
  simp only [map_mul, map_pow, map_sub]
  rfl

end IntegralCoord

section IntegralChange

variable {M : Type*} [Field M] {A : ValuationSubring M}

lemma coe_notMem_nonunits_of_isUnit {a : A} (ha : IsUnit a) : (a : M) ∉ A.nonunits := by
  rw [coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff, not_not]
  exact ha

lemma pow_mem_nonunits {a : M} (ha : a ∈ A.nonunits) {n : ℕ} (hn : n ≠ 0) :
    a ^ n ∈ A.nonunits := by
  induction n with
  | zero => exact absurd rfl hn
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simpa using ha
    · rw [pow_succ]
      exact A.nonunits.mul_mem (ih hpos.ne') ha

lemma mem_of_sq_add_mul_eq {z b c : M} (hb : b ∈ A) (hc : c ∈ A) (h : z ^ 2 + b * z = c) :
    z ∈ A := by
  by_contra hz
  have hz0 : z ≠ 0 := fun h0 => hz (h0 ▸ A.zero_mem)
  have hzi : z⁻¹ ∈ A.nonunits := A.inv_mem_nonunits_of_notMem hz
  have key : (1 : M) = c * (z⁻¹ * z⁻¹) - b * z⁻¹ := by
    field_simp
    linear_combination h
  refine A.one_notMem_nonunits ?_
  rw [key]
  exact A.nonunits.sub_mem (A.mul_mem_nonunits hc (A.nonunits.mul_mem hzi hzi))
    (A.mul_mem_nonunits hb hzi)

theorem exists_map_subtype_eq_of_smul_eq (W W' : WeierstrassCurve A) (g : VariableChange M)
    (hg : g • W'.map A.subtype = W.map A.subtype) (hW : IsUnit W.Δ) (hW' : IsUnit W'.Δ) :
    ∃ g₀ : VariableChange A, g₀.map A.subtype = g := by
  obtain ⟨gu, r, s, t⟩ := g

  set u : M := (gu : M) with hu_def
  have hu0 : u ≠ 0 := gu.ne_zero
  have huinv : ((gu⁻¹ : Mˣ) : M) = u⁻¹ := Units.val_inv_eq_inv_val gu

  have hΔ : ((W.Δ : A) : M) = u⁻¹ ^ 12 * ((W'.Δ : A) : M) := by
    have h := congrArg WeierstrassCurve.Δ hg
    rw [variableChange_Δ, map_Δ, map_Δ] at h
    dsimp only at h
    rw [huinv] at h
    exact h.symm
  have hΔW : ((W.Δ : A) : M) ∉ A.nonunits := coe_notMem_nonunits_of_isUnit hW
  have hΔW' : ((W'.Δ : A) : M) ∉ A.nonunits := coe_notMem_nonunits_of_isUnit hW'

  have hu : u ∈ A ∧ u⁻¹ ∈ A := by
    rcases A.mem_or_inv_mem u with huA | huA
    · refine ⟨huA, A.inv_mem_of_notMem_nonunits fun hun => hΔW' ?_⟩
      have h' : ((W'.Δ : A) : M) = ((W.Δ : A) : M) * u ^ 12 := by
        rw [hΔ]; field_simp
      rw [h']
      exact A.mul_mem_nonunits (SetLike.coe_mem _) (pow_mem_nonunits hun (by norm_num))
    · refine ⟨?_, huA⟩
      have hun : u⁻¹ ∉ A.nonunits := fun hun => hΔW <| by
        rw [hΔ, mul_comm]
        exact A.mul_mem_nonunits (SetLike.coe_mem _) (pow_mem_nonunits hun (by norm_num))
      simpa using A.inv_mem_of_notMem_nonunits hun
  obtain ⟨huA, huiA⟩ := hu

  let u₀ : Aˣ := ⟨⟨u, huA⟩, ⟨u⁻¹, huiA⟩, Subtype.ext (mul_inv_cancel₀ hu0),
    Subtype.ext (inv_mul_cancel₀ hu0)⟩

  have h2A : (2 : M) ∈ A := by
    have : (2 : M) = ((2 : ℕ) : M) := by norm_num
    rw [this]; exact A.natCast_mem 2
  have h3A : (3 : M) ∈ A := by
    have : (3 : M) = ((3 : ℕ) : M) := by norm_num
    rw [this]; exact A.natCast_mem 3

  have ha₁ : (W'.map A.subtype).a₁ ∈ A := SetLike.coe_mem W'.a₁
  have ha₂ : (W'.map A.subtype).a₂ ∈ A := SetLike.coe_mem W'.a₂
  have ha₃ : (W'.map A.subtype).a₃ ∈ A := SetLike.coe_mem W'.a₃
  have ha₄ : (W'.map A.subtype).a₄ ∈ A := SetLike.coe_mem W'.a₄
  have ha₆ : (W'.map A.subtype).a₆ ∈ A := SetLike.coe_mem W'.a₆
  have hb₂ : (W'.map A.subtype).b₂ ∈ A := by rw [map_b₂]; exact SetLike.coe_mem _
  have hb₄ : (W'.map A.subtype).b₄ ∈ A := by rw [map_b₄]; exact SetLike.coe_mem _
  have hb₆ : (W'.map A.subtype).b₆ ∈ A := by rw [map_b₆]; exact SetLike.coe_mem _
  have hb₈ : (W'.map A.subtype).b₈ ∈ A := by rw [map_b₈]; exact SetLike.coe_mem _
  have hB₂ : (W.map A.subtype).a₂ ∈ A := SetLike.coe_mem W.a₂
  have hB₆ : (W.map A.subtype).a₆ ∈ A := SetLike.coe_mem W.a₆
  have hBb₆ : (W.map A.subtype).b₆ ∈ A := by rw [map_b₆]; exact SetLike.coe_mem _
  have hBb₈ : (W.map A.subtype).b₈ ∈ A := by rw [map_b₈]; exact SetLike.coe_mem _

  have h6 : u ^ 6 * (W.map A.subtype).b₆ = (W'.map A.subtype).b₆
      + 2 * r * (W'.map A.subtype).b₄ + r ^ 2 * (W'.map A.subtype).b₂ + 4 * r ^ 3 := by
    have h := congrArg WeierstrassCurve.b₆ hg
    rw [variableChange_b₆] at h
    dsimp only at h
    rw [huinv] at h
    rw [← h]; field_simp
  have h8 : u ^ 8 * (W.map A.subtype).b₈ = (W'.map A.subtype).b₈
      + 3 * r * (W'.map A.subtype).b₆ + 3 * r ^ 2 * (W'.map A.subtype).b₄
      + r ^ 3 * (W'.map A.subtype).b₂ + 3 * r ^ 4 := by
    have h := congrArg WeierstrassCurve.b₈ hg
    rw [variableChange_b₈] at h
    dsimp only at h
    rw [huinv] at h
    rw [← h]; field_simp
  have hr : r ∈ A := by
    by_contra hrA
    have hr0 : r ≠ 0 := fun h0 => hrA (h0 ▸ A.zero_mem)
    have hri : r⁻¹ ∈ A.nonunits := A.inv_mem_nonunits_of_notMem hrA
    have hri2 : r⁻¹ ^ 2 ∈ A.nonunits := pow_mem_nonunits hri two_ne_zero
    have hri3 : r⁻¹ ^ 3 ∈ A.nonunits := pow_mem_nonunits hri three_ne_zero
    have hri4 : r⁻¹ ^ 4 ∈ A.nonunits := pow_mem_nonunits hri four_ne_zero

    have h4 : (4 : M) =
        (u ^ 6 * (W.map A.subtype).b₆ - (W'.map A.subtype).b₆) * r⁻¹ ^ 3
          - 2 * (W'.map A.subtype).b₄ * r⁻¹ ^ 2 - (W'.map A.subtype).b₂ * r⁻¹ := by
      rw [h6]; field_simp; ring
    have h4m : (4 : M) ∈ A.nonunits := by
      rw [h4]
      refine A.nonunits.sub_mem (A.nonunits.sub_mem ?_ ?_) ?_
      · exact A.mul_mem_nonunits (sub_mem (mul_mem (pow_mem huA 6) hBb₆) hb₆) hri3
      · exact A.mul_mem_nonunits (mul_mem h2A hb₄) hri2
      · exact A.mul_mem_nonunits hb₂ hri

    have h3 : (3 : M) =
        (u ^ 8 * (W.map A.subtype).b₈ - (W'.map A.subtype).b₈) * r⁻¹ ^ 4
          - 3 * (W'.map A.subtype).b₆ * r⁻¹ ^ 3 - 3 * (W'.map A.subtype).b₄ * r⁻¹ ^ 2
          - (W'.map A.subtype).b₂ * r⁻¹ := by
      rw [h8]; field_simp; ring
    have h3m : (3 : M) ∈ A.nonunits := by
      rw [h3]
      refine A.nonunits.sub_mem (A.nonunits.sub_mem (A.nonunits.sub_mem ?_ ?_) ?_) ?_
      · exact A.mul_mem_nonunits (sub_mem (mul_mem (pow_mem huA 8) hBb₈) hb₈) hri4
      · exact A.mul_mem_nonunits (mul_mem h3A hb₆) hri3
      · exact A.mul_mem_nonunits (mul_mem h3A hb₄) hri2
      · exact A.mul_mem_nonunits hb₂ hri
    refine A.one_notMem_nonunits ?_
    have h1 : (1 : M) = 4 - 3 := by norm_num
    rw [h1]
    exact A.nonunits.sub_mem h4m h3m

  have h2 : u ^ 2 * (W.map A.subtype).a₂ =
      (W'.map A.subtype).a₂ - s * (W'.map A.subtype).a₁ + 3 * r - s ^ 2 := by
    have h := congrArg WeierstrassCurve.a₂ hg
    rw [variableChange_a₂] at h
    dsimp only at h
    rw [huinv] at h
    rw [← h]; field_simp
  have hs : s ∈ A := by
    refine mem_of_sq_add_mul_eq (b := (W'.map A.subtype).a₁)
      (c := (W'.map A.subtype).a₂ + 3 * r - u ^ 2 * (W.map A.subtype).a₂) ha₁ ?_ ?_
    · exact sub_mem (add_mem ha₂ (mul_mem h3A hr)) (mul_mem (pow_mem huA 2) hB₂)
    · linear_combination h2

  have h6' : u ^ 6 * (W.map A.subtype).a₆ =
      (W'.map A.subtype).a₆ + r * (W'.map A.subtype).a₄ + r ^ 2 * (W'.map A.subtype).a₂
        + r ^ 3 - t * (W'.map A.subtype).a₃ - t ^ 2 - r * t * (W'.map A.subtype).a₁ := by
    have h := congrArg WeierstrassCurve.a₆ hg
    rw [variableChange_a₆] at h
    dsimp only at h
    rw [huinv] at h
    rw [← h]; field_simp
  have ht : t ∈ A := by
    refine mem_of_sq_add_mul_eq (b := (W'.map A.subtype).a₃ + r * (W'.map A.subtype).a₁)
      (c := (W'.map A.subtype).a₆ + r * (W'.map A.subtype).a₄ + r ^ 2 * (W'.map A.subtype).a₂
        + r ^ 3 - u ^ 6 * (W.map A.subtype).a₆) (add_mem ha₃ (mul_mem hr ha₁)) ?_ ?_
    · exact sub_mem (add_mem (add_mem (add_mem ha₆ (mul_mem hr ha₄))
        (mul_mem (pow_mem hr 2) ha₂)) (pow_mem hr 3)) (mul_mem (pow_mem huA 6) hB₆)
    · linear_combination h6'

  refine ⟨⟨u₀, ⟨r, hr⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩, ?_⟩
  ext <;> rfl

end IntegralChange

section Conj

variable {F M : Type*} [Field F] [Field M] [Algebra F M] {A : ValuationSubring M}

noncomputable def decompRingHom (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F) : A →+* A :=
  MulSemiringAction.toRingHom (A.decompositionSubgroup F) A ⟨σ, hσ⟩

@[scoped simp] lemma coe_decompRingHom_apply (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F)
    (a : A) : ((decompRingHom σ hσ a : A) : M) = σ a := rfl

lemma subtype_comp_decompRingHom (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F) :
    A.subtype.comp (decompRingHom σ hσ) = (σ : M →+* M).comp A.subtype := by
  ext a; rfl

lemma residue_comp_decompRingHom (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F)
    (hσI : (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F) :
    (residue A).comp (decompRingHom σ hσ) = residue A := by
  ext a
  exact A.residue_smul_eq_of_mem_inertiaSubgroup hσ hσI a

variable (W : WeierstrassCurve A)

noncomputable def conj (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F) : WeierstrassCurve A :=
  W.map (decompRingHom σ hσ)

lemma conj_map_subtype (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F) :
    (conj W σ hσ).map A.subtype = (W.map A.subtype).map (σ : M →+* M) := by
  rw [conj, WeierstrassCurve.map_map, WeierstrassCurve.map_map, subtype_comp_decompRingHom]

lemma conj_map_residue (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F)
    (hσI : (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F) :
    (conj W σ hσ).map (residue A) = W.map (residue A) := by
  rw [conj, WeierstrassCurve.map_map, residue_comp_decompRingHom σ hσ hσI]

lemma isUnit_conj_Δ (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F) (hW : IsUnit W.Δ) :
    IsUnit (conj W σ hσ).Δ := by
  rw [conj, map_Δ]
  exact hW.map _

end Conj

section Main

variable {F M : Type*} [Field F] [Field M] [DecidableEq M] [Algebra F M]
  {A : ValuationSubring M} [DecidableEq (ResidueField A)]

noncomputable def vcInvAddHom (C : VariableChange M) (V : Affine M) :
    V.Point →+ (C • V).toAffine.Point where
  toFun := vcInvFun C V
  map_zero' := vcInvFun_zero
  map_add' := vcInvFun_add C V

@[scoped simp] lemma vcInvAddHom_apply (C : VariableChange M) (V : Affine M) (P : V.Point) :
    vcInvAddHom C V P = vcInvFun C V P := rfl

lemma vcInvFun_some (C : VariableChange M) (V : Affine M) {x y : M} (h : V.Nonsingular x y) :
    vcInvFun C V (.some x y h) = .some (vcXInv C x) (vcYInv C x y)
      ((nonsingular_variableChange_iff (vcXInv C x) (vcYInv C x y)).mpr
        (by rwa [vcX_vcXInv, vcY_vcYInv])) := rfl

lemma VariableChange.map_mul' {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (C C' : VariableChange R) : (C * C').map φ = C.map φ * C'.map φ :=
  (VariableChange.mapHom φ).map_mul C C'

lemma VariableChange.map_inv' {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (C : VariableChange R) : C⁻¹.map φ = (C.map φ)⁻¹ :=
  (VariableChange.mapHom φ).map_inv C

variable (E : WeierstrassCurve F) (W : WeierstrassCurve A) (κ : VariableChange M)

lemma baseChange_map_algEquiv (σ : M ≃ₐ[F] M) :
    (E.baseChange M).map (σ : M →+* M) = E.baseChange M := by
  have h := E.map_baseChange (σ : M →ₐ[F] M)
  exact h

lemma cocycle_smul_conj (hκ : κ • E.baseChange M = W.map A.subtype)
    (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F) :
    (κ * (κ.map (σ : M →+* M))⁻¹) • (conj W σ hσ).map A.subtype = W.map A.subtype := by
  have h1 : (conj W σ hσ).map A.subtype = κ.map (σ : M →+* M) • E.baseChange M := by
    rw [conj_map_subtype, ← hκ, ← map_variableChange, baseChange_map_algEquiv]
  rw [h1, ← mul_smul, inv_mul_cancel_right, hκ]

lemma heq_reducePoint_of_inertia (hΔr : (W.map (residue A)).Δ ≠ 0) (g₀ : VariableChange A)
    (hfix : g₀.map (residue A) • W.map (residue A) = W.map (residue A))
    (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F)
    (hσI : (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F)
    {x₁ y₁ x₂ y₂ : M} (h₁ : (W.map A.subtype).toAffine.Nonsingular x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Nonsingular x₂ y₂)
    (hx₂ : x₂ = vcXInv (g₀.map A.subtype) (σ x₁))
    (hy₂ : y₂ = vcYInv (g₀.map A.subtype) (σ x₁) (σ y₁)) :
    HEq (vcInvFun (g₀.map (residue A)) (W.map (residue A)).toAffine
        (reducePoint hΔr (.some x₁ y₁ h₁)))
      (reducePoint hΔr (.some x₂ y₂ h₂)) := by
  subst hx₂ hy₂
  by_cases hx₁ : x₁ ∈ A
  ·
    have hy₁ : y₁ ∈ A := Affine.Y_mem_of_X_mem W h₁.1 hx₁
    have hσx₁ : σ x₁ ∈ A := A.smul_mem_of_mem_decompositionSubgroup F hσ hx₁
    have hσy₁ : σ y₁ ∈ A := A.smul_mem_of_mem_decompositionSubgroup F hσ hy₁
    have hx₂ : vcXInv (g₀.map A.subtype) (σ x₁) ∈ A := (vcXInv_mem_iff g₀ _).mpr hσx₁
    have hy₂ : vcYInv (g₀.map A.subtype) (σ x₁) (σ y₁) ∈ A := vcYInv_mem g₀ hσx₁ hσy₁
    have hresx : residue A ⟨σ x₁, hσx₁⟩ = residue A ⟨x₁, hx₁⟩ :=
      A.residue_smul_eq_of_mem_inertiaSubgroup hσ hσI ⟨x₁, hx₁⟩
    have hresy : residue A ⟨σ y₁, hσy₁⟩ = residue A ⟨y₁, hy₁⟩ :=
      A.residue_smul_eq_of_mem_inertiaSubgroup hσ hσI ⟨y₁, hy₁⟩
    rw [reducePoint_some_of_mem hΔr h₁ hx₁, reducePoint_some_of_mem hΔr h₂ hx₂, vcInvFun_some]
    apply heq_some_of_eq hfix
    · rw [residue_vcXInv g₀ hσx₁ hx₂, hresx]
    · rw [A.residue_eq_of_coe_eq _ (v := ⟨vcYInv (g₀.map A.subtype) (σ x₁) (σ y₁), hy₂⟩) rfl,
        residue_vcYInv g₀ hσx₁ hσy₁ hy₂, hresx, hresy]
  ·
    have hσx₁ : σ x₁ ∉ A := fun hmem => hx₁ <| by
      simpa using A.smul_mem_of_mem_decompositionSubgroup F (inv_mem hσ) hmem
    have hx₂ : vcXInv (g₀.map A.subtype) (σ x₁) ∉ A := by
      rw [vcXInv_mem_iff]; exact hσx₁
    rw [reducePoint_some_of_notMem hΔr h₁ hx₁, reducePoint_some_of_notMem hΔr h₂ hx₂,
      vcInvFun_zero]
    exact heq_zero_of_eq hfix

theorem exists_inertia_equivariant_reduction
    (hκ : κ • E.baseChange M = W.map A.subtype) (hΔ : IsUnit W.Δ) :
    ∃ (θ : (E.baseChange M).toAffine.Point →+ (W.map (residue A)).toAffine.Point)
      (g : (M ≃ₐ[F] M) → VariableChange A),
      (∀ (n : ℕ) (P : (E.baseChange M).toAffine.Point),
          (n : ResidueField A) ≠ 0 → n • P = 0 → θ P = 0 → P = 0) ∧
      (∀ (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F),
          (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
          (g σ).map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹ ∧
          (g σ).map (residue A) • W.map (residue A) = W.map (residue A) ∧
          ∀ P : (E.baseChange M).toAffine.Point,
            HEq (Point.vcInvFun ((g σ).map (residue A)) (W.map (residue A)).toAffine (θ P))
              (θ (Point.map (σ : M →ₐ[F] M) P))) ∧
      (∀ (σ τ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F)
          (hτ : τ ∈ A.decompositionSubgroup F),
          (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
          (⟨τ, hτ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
          (g (σ * τ)).map (residue A) = (g σ).map (residue A) * (g τ).map (residue A)) := by
  classical

  have hΔr : (W.map (residue A)).Δ ≠ 0 := (map_residue_Δ_ne_zero_iff W).mpr hΔ
  have hκ' : (κ • (E.baseChange M).toAffine) = (W.map A.subtype).toAffine := hκ
  let θ : (E.baseChange M).toAffine.Point →+ (W.map (residue A)).toAffine.Point :=
    (reduceHom hΔr).comp
      ((castAddHom hκ').comp (vcInvAddHom κ (E.baseChange M).toAffine))
  have hθ : ∀ P, θ P =
      reducePoint hΔr (castPt hκ' (vcInvFun κ (E.baseChange M).toAffine P)) := fun P => rfl

  have hg : ∀ (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F),
      ∃ g₀ : VariableChange A, g₀.map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹ :=
    fun σ hσ => exists_map_subtype_eq_of_smul_eq W (conj W σ hσ) _
      (cocycle_smul_conj E W κ hκ σ hσ) hΔ (isUnit_conj_Δ W σ hσ hΔ)
  let g : (M ≃ₐ[F] M) → VariableChange A := fun σ =>
    if hσ : σ ∈ A.decompositionSubgroup F then (hg σ hσ).choose else 1
  have hgσ : ∀ (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F),
      (g σ).map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹ := fun σ hσ => by
    simp only [g, dif_pos hσ]
    exact (hg σ hσ).choose_spec

  have hgconj : ∀ (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F),
      g σ • conj W σ hσ = W := fun σ hσ => by
    apply WeierstrassCurve.map_injective (f := A.subtype) Subtype.val_injective
    show (g σ • conj W σ hσ).map A.subtype = W.map A.subtype
    rw [← map_variableChange, hgσ σ hσ, cocycle_smul_conj E W κ hκ σ hσ]

  have hgres : ∀ (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F),
      (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
      (g σ).map (residue A) • W.map (residue A) = W.map (residue A) := fun σ hσ hσI => by
    conv_lhs => rw [← conj_map_residue W σ hσ hσI]
    rw [map_variableChange, hgconj σ hσ]
  refine ⟨θ, g, ?_, ?_, ?_⟩
  ·

    intro n P hn hP hθP
    cases P with
    | zero => rfl
    | some x y h =>
      exfalso

      have hQ : n • (castPt hκ' (vcInvFun κ (E.baseChange M).toAffine (.some x y h))) = 0 := by
        have := congrArg ((castAddHom hκ').comp (vcInvAddHom κ (E.baseChange M).toAffine)) hP
        rw [map_nsmul, _root_.map_zero] at this
        exact this
      rw [hθ] at hθP
      rw [vcInvFun_some, castPt_some] at hQ hθP
      have hx : vcXInv κ x ∈ A :=
        X_mem_of_nsmul_eq_zero_of_formalCoordinates (W := W) hn _ hQ
      rw [reducePoint_some_of_mem hΔr _ hx] at hθP
      exact Point.some_ne_zero _ hθP
  · intro σ hσ hσI
    have hgM := hgσ σ hσ
    have hfix := hgres σ hσ hσI
    refine ⟨hgM, hfix, fun P => ?_⟩
    cases P with
    | zero => exact heq_zero_of_eq hfix
    | some x y h =>

      have hκfac : κ = (g σ).map A.subtype * κ.map (σ : M →+* M) := by
        rw [hgM, inv_mul_cancel_right]
      have hmx : ∀ z : M, σ (vcXInv κ z) = vcXInv (κ.map (σ : M →+* M)) (σ z) :=
        fun z => map_vcXInv (σ : M →+* M) κ z
      have hmy : ∀ z w : M, σ (vcYInv κ z w) = vcYInv (κ.map (σ : M →+* M)) (σ z) (σ w) :=
        fun z w => map_vcYInv (σ : M →+* M) κ z w
      have key_x : vcXInv κ (σ x) = vcXInv ((g σ).map A.subtype) (σ (vcXInv κ x)) := by
        conv_lhs => rw [hκfac]
        rw [vcXInv_mul, hmx]
      have key_y : vcYInv κ (σ x) (σ y) =
          vcYInv ((g σ).map A.subtype) (σ (vcXInv κ x)) (σ (vcYInv κ x y)) := by
        conv_lhs => rw [hκfac]
        rw [vcYInv_mul, hmx, hmy]
      rw [hθ, hθ, Point.map_some, vcInvFun_some, vcInvFun_some, castPt_some, castPt_some]
      exact heq_reducePoint_of_inertia W hΔr (g σ) hfix σ hσ hσI _ _ key_x key_y
  ·

    intro σ τ hσ hτ hσI hτI
    have hστ : σ * τ ∈ A.decompositionSubgroup F := mul_mem hσ hτ
    have hcomp : ((σ * τ : M ≃ₐ[F] M) : M →+* M) = (σ : M →+* M).comp (τ : M →+* M) :=
      RingHom.ext fun _ => rfl

    have hM : (g (σ * τ)).map A.subtype =
        (g σ * (g τ).map (decompRingHom σ hσ)).map A.subtype := by
      rw [VariableChange.map_mul', VariableChange.map_map, subtype_comp_decompRingHom,
        ← VariableChange.map_map, hgσ _ hστ, hgσ σ hσ, hgσ τ hτ, VariableChange.map_mul',
        VariableChange.map_inv', VariableChange.map_map, hcomp]
      group

    have hA : g (σ * τ) = g σ * (g τ).map (decompRingHom σ hσ) :=
      VariableChange.map_injective Subtype.val_injective hM
    rw [hA, VariableChange.map_mul', VariableChange.map_map, residue_comp_decompRingHom σ hσ hσI]

end Main

end P2MKcSerreTate
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_inertia_equivariant_reduction_of_variableChange_eq_map.P2MKcSerreTate"

open P2MKcSerreTate in
universe u v in
theorem solution
    {F : Type u} {M : Type v} [Field F] [Field M] [DecidableEq M] [Algebra F M]
    (A : ValuationSubring M) [DecidableEq (ResidueField A)]
    (E : WeierstrassCurve F) (W : WeierstrassCurve A) (κ : VariableChange M)
    (hκ : κ • E.baseChange M = W.map A.subtype) (hΔ : IsUnit W.Δ) :
    ∃ (θ : (E.baseChange M).toAffine.Point →+ (W.map (residue A)).toAffine.Point)
      (g : (M ≃ₐ[F] M) → VariableChange A),
      (∀ (n : ℕ) (P : (E.baseChange M).toAffine.Point),
          (n : ResidueField A) ≠ 0 → n • P = 0 → θ P = 0 → P = 0) ∧
      (∀ (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F),
          (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
          (g σ).map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹ ∧
          (g σ).map (residue A) • W.map (residue A) = W.map (residue A) ∧
          ∀ P : (E.baseChange M).toAffine.Point,
            HEq (Point.vcInvFun ((g σ).map (residue A)) (W.map (residue A)).toAffine (θ P))
              (θ (Point.map (σ : M →ₐ[F] M) P))) ∧
      (∀ (σ τ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F)
          (hτ : τ ∈ A.decompositionSubgroup F),
          (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
          (⟨τ, hτ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
          (g (σ * τ)).map (residue A) = (g σ).map (residue A) * (g τ).map (residue A)) :=
  exists_inertia_equivariant_reduction E W κ hκ hΔ

end S_WeierstrassCurve_exists_inertia_equivariant_reduction_of_variableChange_eq_map
end P2MW
export P2MW.S_WeierstrassCurve_exists_inertia_equivariant_reduction_of_variableChange_eq_map (solution)
