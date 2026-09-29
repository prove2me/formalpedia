-- Prove2me | solution 1 for WeierstrassCurve.exists_torsionBy_linearEquiv_residueField_of_isFrobeniusAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/2444e304-f663-51d8-ab9b-093a8c3c9750

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Module.ZMod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.CharP.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Theorems.Thm_WeierstrassCurve_exists_reduction_inZeroComponentAt
import Theorems.Thm_WeierstrassCurve_torsion_integral_of_not_dvd
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_of_isGoodPrimeFor
import Theorems.Thm_WeierstrassCurve_nonsingular_residue_of_isGoodPrimeFor
import Theorems.Thm_WeierstrassCurve_map_residueField_discr_ne_zero_of_isGoodPrimeFor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_torsionBy_linearEquiv_residueField_of_isFrobeniusAt
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open scoped Classical

namespace M4cP1S2

theorem natCast_residueField_eq_zero (A : ValuationSubring (AlgebraicClosure ℚ)) {ℓ : ℕ}
    (hA : A.LiesOverPrime ℓ) : (ℓ : IsLocalRing.ResidueField A) = 0 := by
  obtain ⟨hmem, hmax⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal (A := A)).mp hA
  have h1 : ((ℓ : A) : AlgebraicClosure ℚ) = (ℓ : AlgebraicClosure ℚ) := by simp
  have h2 : (ℓ : A) = ⟨(ℓ : AlgebraicClosure ℚ), hmem⟩ := Subtype.ext h1
  have h3 : IsLocalRing.residue A (ℓ : A) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, h2]
    exact hmax
  rwa [map_natCast] at h3

theorem natCast_residueField_ne_zero (A : ValuationSubring (AlgebraicClosure ℚ)) {ℓ p : ℕ}
    (hℓ : ℓ.Prime) (hp : p.Prime) (hℓp : ℓ ≠ p) (hA : A.LiesOverPrime ℓ) :
    (p : IsLocalRing.ResidueField A) ≠ 0 := by
  intro hp0
  have hℓ0 := natCast_residueField_eq_zero A hA
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hℓ hp).mpr hℓp)
  have h := congrArg (fun z : ℤ => (z : IsLocalRing.ResidueField A)) hab
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_one, hℓ0, hp0,
    mul_zero, add_zero] at h
  exact zero_ne_one h

theorem not_dvd_of_prime_ne {ℓ p : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (hℓp : ℓ ≠ p) : ¬ ℓ ∣ p :=
  fun h => hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h)

theorem some_congr {F : Type*} [Field F] {V : WeierstrassCurve.Affine F} {x₁ y₁ x₂ y₂ : F}
    (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) (hx : x₁ = x₂) (hy : y₁ = y₂) :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

section Main

theorem card_torsion_generic (W : WeierstrassCurve ℤ) {ℓ p : ℕ} (hp : p.Prime)
    (hgood : W.IsGoodPrimeFor ℓ) :
    Nat.card (Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p)
      = p ^ 2 := by
  have hΔ : W.Δ ≠ 0 := fun h => hgood (h ▸ dvd_zero _)
  haveI : (W.map (Int.castRingHom ℚ)).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr (by rw [map_Δ, eq_intCast]; exact_mod_cast hΔ)⟩
  exact card_torsion_of_isAlgClosed (W.map (Int.castRingHom ℚ))
    (Nat.cast_ne_zero.mpr hp.ne_zero)

theorem card_torsion_special (W : WeierstrassCurve ℤ) {ℓ p : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime)
    (hℓp : ℓ ≠ p) (hgood : W.IsGoodPrimeFor ℓ) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime ℓ) :
    Nat.card (Submodule.torsionBy ℤ (W⁄(IsLocalRing.ResidueField A)).Point p) = p ^ 2 := by
  haveI : IsAlgClosed (IsLocalRing.ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI : (W.map (Int.castRingHom (IsLocalRing.ResidueField A))).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr (W.map_residueField_discr_ne_zero_of_isGoodPrimeFor hℓ hgood A hA)⟩
  exact card_torsion_of_isAlgClosed (K := IsLocalRing.ResidueField A)
    (W.map (Int.castRingHom (IsLocalRing.ResidueField A)))
    (natCast_residueField_ne_zero A hℓ hp hℓp hA)

theorem main (W : WeierstrassCurve ℤ) {ℓ p : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (hℓp : ℓ ≠ p)
    (hgood : W.IsGoodPrimeFor ℓ) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ)
    (φ : IsLocalRing.ResidueField A ≃ₐ[ℤ] IsLocalRing.ResidueField A)
    (hφ : ∀ x : IsLocalRing.ResidueField A, φ x = x ^ ℓ) :
    ∃ e : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p
        ≃ₗ[ZMod p] Submodule.torsionBy ℤ (W⁄(IsLocalRing.ResidueField A)).Point p,
      ∀ x : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p,
        e (σ • x) = φ • e x := by

  obtain ⟨red, h0, hadd, hval, -, hker, -⟩ := W.exists_reduction_inZeroComponentAt A

  have hZ : ∀ P, W.InZeroComponentAt A P := fun P =>
    W.inZeroComponentAt_of_isGoodPrimeFor hℓ hgood A hA P
  have hℓp' : ¬ ℓ ∣ p := not_dvd_of_prime_ne hℓ hp hℓp

  let ρ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point →+
      (W⁄(IsLocalRing.ResidueField A)).Point :=
    { toFun := red
      map_zero' := h0
      map_add' := fun P Q => hadd P Q (hZ P) (hZ Q) }
  have hρ : ∀ P, ρ P = red P := fun _ => rfl

  have hmem : ∀ x : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p,
      ρ x ∈ Submodule.torsionBy ℤ (W⁄(IsLocalRing.ResidueField A)).Point p := by
    intro x
    rw [Submodule.mem_torsionBy_iff, ← map_zsmul ρ, (Submodule.mem_torsionBy_iff _ _).mp x.2,
      _root_.map_zero]
  let f : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p →+
      Submodule.torsionBy ℤ (W⁄(IsLocalRing.ResidueField A)).Point p :=
    { toFun := fun x => ⟨ρ x, hmem x⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }
  have hf : ∀ x, (f x : (W⁄(IsLocalRing.ResidueField A)).Point) = red x := fun _ => rfl

  have hint : ∀ x : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p,
      (x : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) = 0 ∨
        ∃ (a b : AlgebraicClosure ℚ)
          (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular a b),
          (x : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) = .some a b h ∧
            a ∈ A ∧ b ∈ A := by
    intro x
    have hx : p • (x : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) = 0 := by
      rw [← natCast_zsmul]
      exact (Submodule.mem_torsionBy_iff _ _).mp x.2
    exact W.torsion_integral_of_not_dvd hℓ A hA hℓp' _ hx

  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx0
    have hred : red x = 0 := by
      rw [← hf]
      exact congrArg Subtype.val hx0
    apply Subtype.ext
    rcases hker _ (hZ _) hred with h | ⟨a, b, h, hxe, ha⟩
    · exact h
    · exfalso
      rcases hint x with h0' | ⟨a', b', h', hxe', ha', -⟩
      · rw [h0'] at hxe
        exact (Point.some_ne_zero h) hxe.symm
      · rw [hxe'] at hxe
        obtain ⟨haa, -⟩ := Point.some.inj hxe
        exact ha (haa ▸ ha')

  have hcardE := card_torsion_generic W (p := p) hp hgood
  have hcardk := card_torsion_special W (p := p) hℓ hp hℓp hgood A hA
  haveI : Finite (Submodule.torsionBy ℤ (W⁄(IsLocalRing.ResidueField A)).Point p) :=
    Nat.finite_of_card_ne_zero (by rw [hcardk]; exact pow_ne_zero 2 hp.ne_zero)
  have hbij : Function.Bijective (f.toZModLinearMap p) := by
    rw [AddMonoidHom.coe_toZModLinearMap]
    exact hinj.bijective_of_nat_card_le (by rw [hcardE, hcardk])
  refine ⟨LinearEquiv.ofBijective (f.toZModLinearMap p) hbij, fun x => ?_⟩
  rw [LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply,
    AddMonoidHom.coe_toZModLinearMap]
  apply Subtype.ext
  show ρ (σ • (x : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)) = φ • ρ x
  rcases hint x with hx0 | ⟨a, b, h, hxe, ha, hb⟩
  ·
    have hσ0 : σ • (0 : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) = 0 := rfl
    have hφ0 : φ • (0 : (W⁄(IsLocalRing.ResidueField A)).Point) = 0 := rfl
    rw [hx0, hσ0, _root_.map_zero, hφ0]
  ·
    let g : A.decompositionSubgroup ℚ := ⟨σ, hσ.mem_decompositionSubgroup⟩
    have hσa : σ a ∈ A := (g • (⟨a, ha⟩ : A)).2
    have hσb : σ b ∈ A := (g • (⟨b, hb⟩ : A)).2
    have hga : (⟨σ a, hσa⟩ : A) = g • ⟨a, ha⟩ := rfl
    have hgb : (⟨σ b, hσb⟩ : A) = g • ⟨b, hb⟩ := rfl

    obtain ⟨hσns, hσP⟩ :
        ∃ hσns : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular (σ a) (σ b),
          σ • (Point.some a b h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
            = Point.some (σ a) (σ b) hσns :=
      ⟨_, rfl⟩

    have hns := W.nonsingular_residue_of_isGoodPrimeFor hℓ hgood A hA h.left ha hb
    have hnsσ := W.nonsingular_residue_of_isGoodPrimeFor hℓ hgood A hA hσns.left hσa hσb
    rw [hxe, hσP, hρ, hρ, hval _ _ _ hσa hσb hnsσ, hval _ _ _ ha hb hns]

    have hφa : φ (IsLocalRing.residue A ⟨a, ha⟩) = IsLocalRing.residue A ⟨σ a, hσa⟩ := by
      rw [hφ, hga, IsLocalRing.ResidueField.residue_smul, hσ.smul_residue_eq]
    have hφb : φ (IsLocalRing.residue A ⟨b, hb⟩) = IsLocalRing.residue A ⟨σ b, hσb⟩ := by
      rw [hφ, hgb, IsLocalRing.ResidueField.residue_smul, hσ.smul_residue_eq]

    have hφns : (W.map (Int.castRingHom (IsLocalRing.ResidueField A))).toAffine.Nonsingular
        (φ (IsLocalRing.residue A ⟨a, ha⟩)) (φ (IsLocalRing.residue A ⟨b, hb⟩)) := by
      rw [hφa, hφb]
      exact hnsσ
    have hφP : φ • (Point.some (IsLocalRing.residue A ⟨a, ha⟩) (IsLocalRing.residue A ⟨b, hb⟩) hns :
        (W⁄(IsLocalRing.ResidueField A)).Point) = Point.some _ _ hφns := rfl
    exact (some_congr _ _ hφa.symm hφb.symm).trans hφP.symm

end Main

end M4cP1S2

theorem solution (W : WeierstrassCurve ℤ) (ℓ p : ℕ) (hℓ : ℓ.Prime) (hp : p.Prime) (hℓp : ℓ ≠ p) (hgood : W.IsGoodPrimeFor ℓ) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ) (φ : IsLocalRing.ResidueField A ≃ₐ[ℤ] IsLocalRing.ResidueField A) (hφ : ∀ x : IsLocalRing.ResidueField A, φ x = x ^ ℓ) : ∃ e : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p ≃ₗ[ZMod p] Submodule.torsionBy ℤ (W⁄(IsLocalRing.ResidueField A)).Point p, ∀ x : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p, e (σ • x) = φ • e x :=
  M4cP1S2.main W hℓ hp hℓp hgood A hA σ hσ φ hφ

end S_WeierstrassCurve_exists_torsionBy_linearEquiv_residueField_of_isFrobeniusAt
end P2MW
export P2MW.S_WeierstrassCurve_exists_torsionBy_linearEquiv_residueField_of_isFrobeniusAt (solution)
