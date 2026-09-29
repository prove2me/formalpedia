-- Prove2me | solution 1 for WeierstrassCurve.exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/ff2b59bf-ad7b-5d69-a0d7-de427d95092e

import Mathlib
import Definitions.Def_WeierstrassCurve_ReduceHom
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

namespace ChildL
open WeierstrassCurve IsLocalRing
variable {L : Type*} [Field L] {A : ValuationSubring L} {W : WeierstrassCurve A}
variable [DecidableEq L] [DecidableEq (ResidueField A)]

theorem reduceHom_injOn' (hΔ : (W.map (residue A)).Δ ≠ 0) {N : ℕ} (hN : (N : ResidueField A) ≠ 0)
    {P Q : (W.map A.subtype).toAffine.Point} (hP : N • P = 0) (hQ : N • Q = 0)
    (h : reduceHom hΔ P = reduceHom hΔ Q) : P = Q := by
  have h1 : N • (P - Q) = 0 := by rw [nsmul_sub, hP, hQ, sub_zero]
  have h2 : reducePoint hΔ (P - Q) = 0 := by
    show reduceHom hΔ (P - Q) = 0
    rw [map_sub, h, sub_self]
  have key : P - Q = 0 := by
    generalize hR : P - Q = R at h1 h2
    cases R with
    | zero => rfl
    | some x y hxy =>
      exfalso
      have hx : x ∈ A := X_mem_of_nsmul_eq_zero' W hN hxy h1
      rw [reducePoint_some_of_mem hΔ hxy hx] at h2
      exact Affine.Point.some_ne_zero _ h2
  exact sub_eq_zero.mp key

end ChildL

noncomputable section

open WeierstrassCurve IsLocalRing

namespace ChildL

variable {L : Type*} [Field L] [DecidableEq L]
variable {A : ValuationSubring L} [DecidableEq (ResidueField A)]
variable {W : WeierstrassCurve A}

def mapPointFun {F F' : Type*} [Field F] [Field F'] (f : F →+* F') (V : WeierstrassCurve F) :
    V.toAffine.Point → (V.map f).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (f x) (f y) ((V.toAffine.map_nonsingular f.injective x y).mpr h)

theorem mapPointFun_add {F F' : Type*} [Field F] [Field F'] [DecidableEq F] [DecidableEq F']
    (f : F →+* F') (V : WeierstrassCurve F) (P Q : V.toAffine.Point) :
    mapPointFun f V (P + Q) = mapPointFun f V P + mapPointFun f V Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  any_goals rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = V.toAffine.negY x₂ y₂
  · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2]
    show (Affine.Point.zero : (V.map f).toAffine.Point) = Affine.Point.some _ _ _ + Affine.Point.some _ _ _
    rw [Affine.Point.add_of_Y_eq (congrArg f hxy.1) (by rw [hxy.2, Affine.map_negY])]
    rfl
  · have hxy' : ¬(f x₁ = f x₂ ∧ f y₁ = (V.map f).toAffine.negY (f x₂) (f y₂)) := by
      rintro ⟨hx, hy⟩
      rw [Affine.map_negY] at hy
      exact hxy ⟨f.injective hx, f.injective hy⟩
    rw [Affine.Point.add_some hxy]
    show Affine.Point.some _ _ _ = Affine.Point.some _ _ _ + Affine.Point.some _ _ _
    rw [Affine.Point.add_some hxy']
    congr 1
    · rw [Affine.map_slope, Affine.map_addX]
    · rw [Affine.map_slope, Affine.map_addY]

def mapPointHom {F F' : Type*} [Field F] [Field F'] [DecidableEq F] [DecidableEq F']
    (f : F →+* F') (V : WeierstrassCurve F) : V.toAffine.Point →+ (V.map f).toAffine.Point where
  toFun := mapPointFun f V
  map_zero' := rfl
  map_add' := mapPointFun_add f V

theorem mapPointHom_injective {F F' : Type*} [Field F] [Field F'] [DecidableEq F] [DecidableEq F']
    (f : F →+* F') (V : WeierstrassCurve F) : Function.Injective (mapPointHom f V) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · exact absurd h.symm (Affine.Point.some_ne_zero _)
  · exact absurd h (Affine.Point.some_ne_zero _)
  · have h' : (Affine.Point.some (f x₁) (f y₁) _ : (V.map f).toAffine.Point) = Affine.Point.some (f x₂) (f y₂) _ := h
    rw [Affine.Point.some.injEq] at h'
    obtain ⟨hx, hy⟩ := h'
    have hx' := f.injective hx; have hy' := f.injective hy
    subst hx'; subst hy'; rfl

def torsionMap {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (g : G →+ G') (n : ℕ) :
    Submodule.torsionBy ℤ G (n : ℤ) → Submodule.torsionBy ℤ G' (n : ℤ) :=
  fun P => ⟨g P, by
    have hP := P.2
    rw [Submodule.mem_torsionBy_iff] at hP ⊢
    rw [← map_zsmul, hP, map_zero]⟩

theorem torsionMap_injective {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (g : G →+ G') (n : ℕ)
    (hg : ∀ ⦃P Q : G⦄, n • P = 0 → n • Q = 0 → g P = g Q → P = Q) :
    Function.Injective (torsionMap g n) := by
  intro P Q h
  apply Subtype.ext
  have hP := P.2; have hQ := Q.2
  rw [Submodule.mem_torsionBy_iff, natCast_zsmul] at hP hQ
  exact hg hP hQ (congrArg Subtype.val h)

theorem main [IsAlgClosed L] [CharZero L] (hΔ : (W.map (residue A)).Δ ≠ 0)
    {ℓ : ℕ} (hℓ : (ℓ : ResidueField A) ≠ 0)
    (Q₀ : (W.map (residue A)).toAffine.Point) (hQ₀ : ℓ • Q₀ = 0) :
    ∃ Q : (W.map A.subtype).toAffine.Point, ℓ • Q = 0 ∧ reduceHom hΔ Q = Q₀ := by
  letI : DecidableEq (AlgebraicClosure (ResidueField A)) := Classical.decEq _
  haveI hEA : W.IsElliptic := ⟨(map_residue_Δ_ne_zero_iff W).mp hΔ⟩

  have hunit : IsUnit W.Δ := (map_residue_Δ_ne_zero_iff W).mp hΔ
  haveI hEL : (W.map A.subtype).IsElliptic := by
    refine ⟨?_⟩
    rw [WeierstrassCurve.map_Δ]
    exact (hunit.map A.subtype)
  haveI hEk : (W.map (residue A)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩

  let ι : ResidueField A →+* AlgebraicClosure (ResidueField A) :=
    algebraMap (ResidueField A) (AlgebraicClosure (ResidueField A))
  haveI hEkbar : ((W.map (residue A)).map ι).IsElliptic := by
    refine ⟨?_⟩; rw [WeierstrassCurve.map_Δ]; exact hEk.isUnit.map ι

  have hℓL : (ℓ : L) ≠ 0 := by
    intro h
    apply hℓ
    have : (ℓ : ResidueField A) = residue A (ℓ : A) := by simp
    rw [this]
    have hA : ((ℓ : A) : L) = 0 := by exact_mod_cast h
    have : (ℓ : A) = 0 := Subtype.ext hA
    rw [this, map_zero]
  have hℓk : (ℓ : AlgebraicClosure (ResidueField A)) ≠ 0 := by
    rw [← map_natCast ι]; exact (map_ne_zero ι).mpr hℓ

  have hZ : Nat.card (ZMod ℓ × ZMod ℓ) = ℓ ^ 2 := by
    haveI : NeZero ℓ := ⟨by rintro rfl; exact hℓ (by simp)⟩
    rw [Nat.card_prod, Nat.card_zmod, sq]
  have hcL : Nat.card (Submodule.torsionBy ℤ (W.map A.subtype).toAffine.Point (ℓ : ℤ)) = ℓ ^ 2 := by
    obtain ⟨e⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
      (F := L) (K := L) (W.map A.subtype) hℓL
    rw [← hZ]
    exact (Nat.card_congr e.toEquiv).symm
  have hck : Nat.card (Submodule.torsionBy ℤ ((W.map (residue A)).map ι).toAffine.Point (ℓ : ℤ))
      = ℓ ^ 2 := by
    obtain ⟨e⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
      (F := ResidueField A) (K := AlgebraicClosure (ResidueField A)) (W.map (residue A)) hℓk
    rw [← hZ]
    exact (Nat.card_congr e.toEquiv).symm

  let r := torsionMap (reduceHom hΔ) ℓ
  let m := torsionMap (mapPointHom ι (W.map (residue A))) ℓ
  have hr : Function.Injective r :=
    torsionMap_injective _ _ (fun P Q hP hQ h => ChildL.reduceHom_injOn' hΔ hℓ hP hQ h)
  have hm : Function.Injective m :=
    torsionMap_injective _ _ (fun P Q _ _ h => mapPointHom_injective ι _ h)

  have hℓ0 : ℓ ≠ 0 := by rintro rfl; exact hℓ (by simp)
  haveI : Finite (Submodule.torsionBy ℤ ((W.map (residue A)).map ι).toAffine.Point (ℓ : ℤ)) :=
    Nat.finite_of_card_ne_zero (by rw [hck]; exact pow_ne_zero _ hℓ0)
  have hmr : Function.Bijective (m ∘ r) :=
    (hm.comp hr).bijective_of_nat_card_le (by rw [hcL, hck])

  have hrs : Function.Surjective r := by
    intro y
    obtain ⟨x, hx⟩ := hmr.2 (m y)
    exact ⟨x, hm hx⟩
  obtain ⟨P, hP⟩ := hrs ⟨Q₀, by rw [Submodule.mem_torsionBy_iff, natCast_zsmul]; exact hQ₀⟩
  refine ⟨P.1, ?_, congrArg Subtype.val hP⟩
  have := P.2
  rw [Submodule.mem_torsionBy_iff, natCast_zsmul] at this
  exact this

end ChildL

theorem solution
    {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L] [CharZero L]
    (A : ValuationSubring L) [DecidableEq (ResidueField A)]
    (W : WeierstrassCurve A) (hΔ : (W.map (residue A)).Δ ≠ 0)
    {ℓ : ℕ} (hℓ : (ℓ : ResidueField A) ≠ 0)
    (Q₀ : (W.map (residue A)).toAffine.Point) (hQ₀ : ℓ • Q₀ = 0) :
    ∃ Q : (W.map A.subtype).toAffine.Point, ℓ • Q = 0 ∧ reduceHom hΔ Q = Q₀ :=
  ChildL.main hΔ hℓ Q₀ hQ₀

end

end S_WeierstrassCurve_exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero
end P2MW
export P2MW.S_WeierstrassCurve_exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero (solution)
