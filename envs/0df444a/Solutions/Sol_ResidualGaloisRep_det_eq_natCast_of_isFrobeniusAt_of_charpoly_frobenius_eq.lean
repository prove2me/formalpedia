-- Prove2me | solution 1 for ResidualGaloisRep.det_eq_natCast_of_isFrobeniusAt_of_charpoly_frobenius_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/3f495ed4-fc0d-51ee-a0a2-45765bc565fc

import Mathlib
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_GaloisRep_Residual
import Theorems.Thm_GaloisRep_det_eq_cycloChar_pow_of_det_frobenius_eq_pow
import Theorems.Thm_ValuationSubring_IsFrobeniusAt_apply_rootOfUnity_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_det_eq_natCast_of_isFrobeniusAt_of_charpoly_frobenius_eq
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"

set_option autoImplicit false

open Polynomial

theorem solution
    {k : Type} [Field k] [Finite k] {p : ℕ} [Fact p.Prime] [CharP k p] (ρbar : ResidualGaloisRep k)
    (S : Finset ℕ) (N : ℕ) [NeZero N]
    (θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* k)
    (hθ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) = X ^ 2 - C (θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C (ℓ : k))
    (r : ℕ) (hr : r.Prime) (hrp : r ≠ p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime r)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : P.IsFrobeniusAt σ r) :
    LinearMap.det (ρbar.ρ σ) = (r : k) := by
  classical
  have hp : p.Prime := Fact.out

  let b := Module.finBasisOfFinrankEq k ρbar.V ρbar.finrank_eq
  let ρM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) k :=
    ((LinearMap.toMatrixAlgEquiv b).toMulEquiv.toMonoidHom.comp ρbar.ρ).toHomUnits
  have hρM : ∀ σ, (ρM σ).val = LinearMap.toMatrix b b (ρbar.ρ σ) := fun σ => rfl
  have hdetM : ∀ σ, Matrix.det (ρM σ).val = LinearMap.det (ρbar.ρ σ) := fun σ => by
    rw [hρM, LinearMap.det_toMatrix]
  have hfinM : GaloisFactorsThroughFiniteLevel ρM := by
    obtain ⟨L, hL, h1⟩ := ρbar.factorsThroughFiniteLevel
    refine ⟨L, hL, fun σ hσ => Units.ext ?_⟩
    rw [hρM, h1 σ hσ]
    exact LinearMap.toMatrix_one b

  haveI : NeZero ((p : ℕ) : AlgebraicClosure ℚ) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) p
  have hcard : Nat.card (rootsOfUnity p (AlgebraicClosure ℚ)) = p := hζ.card_rootsOfUnity
  let toRE : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) :=
    { toFun := fun σ => σ.toRingEquiv
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let cyc : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod p)ˣ :=
    (modularCyclotomicCharacter (AlgebraicClosure ℚ) hcard).comp toRE
  have hcyc : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ),
      μ ^ p = 1 → σ μ = μ ^ ((cyc σ : ZMod p)).val := by
    intro σ μ hμ
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne_zero] at hμ
      exact zero_ne_one hμ
    have hmem : Units.mk0 μ hμ0 ∈ rootsOfUnity p (AlgebraicClosure ℚ) := by
      rw [mem_rootsOfUnity]; exact Units.ext (by simpa using hμ)
    have := modularCyclotomicCharacter.spec (AlgebraicClosure ℚ) hcard σ.toRingEquiv hmem
    first | exact this | simpa using this

  have hdet : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ (↑S : Set ℕ) → ℓ ≠ p →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          Matrix.det (ρM σ).val = (ℓ : k) ^ 1 := by
    intro ℓ hℓ hℓN hℓS _ A hA σ hσ
    rw [hdetM, pow_one, LinearMap.det_eq_sign_charpoly_coeff, hθ ℓ hℓ hℓN hℓS A hA σ hσ, ρbar.finrank_eq]
    simp

  have main := GaloisRep.det_eq_cycloChar_pow_of_det_frobenius_eq_pow p cyc hcyc N (↑S : Set ℕ)
    S.finite_toSet 1 ρM hfinM hdet σ
  rw [hdetM, pow_one] at main
  rw [main]

  have e1 : ζ ^ ((cyc σ : ZMod p)).val = ζ ^ r :=
    (hcyc σ ζ hζ.pow_eq_one).symm.trans
      (ValuationSubring.IsFrobeniusAt.apply_rootOfUnity_eq_pow hp hr hrp P hP hσ ζ hζ.pow_eq_one)
  have hmod : ((cyc σ : ZMod p)).val ≡ r [MOD p] := by
    have key : ζ ^ (((cyc σ : ZMod p)).val % orderOf ζ) = ζ ^ (r % orderOf ζ) := by
      rw [pow_mod_orderOf, pow_mod_orderOf]; exact e1
    rw [← hζ.eq_orderOf] at key
    exact hζ.pow_inj (Nat.mod_lt _ hp.pos) (Nat.mod_lt _ hp.pos) key
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  exact (CharP.natCast_eq_natCast k p).mpr hmod

end S_ResidualGaloisRep_det_eq_natCast_of_isFrobeniusAt_of_charpoly_frobenius_eq
end P2MW
export P2MW.S_ResidualGaloisRep_det_eq_natCast_of_isFrobeniusAt_of_charpoly_frobenius_eq (solution)
