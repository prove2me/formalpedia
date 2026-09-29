-- Prove2me | solution 1 for ValuationSubring.cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/90ffba86-662e-5d0d-8552-f95909b7fdc1

import Definitions.Def_EllipticCurve_FrobeniusTrace
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Theorems.Thm_ValuationSubring_IsFrobeniusAt_apply_eq_pow_of_pow_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt

set_option autoImplicit false

theorem solution
    (m : ℕ)
    (cyc : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod m)ˣ)
    (hcyc : ∀ σ (μ : AlgebraicClosure ℚ), μ ^ m = 1 → σ μ = μ ^ ((cyc σ : ZMod m)).val)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓm : ¬ ℓ ∣ m) :
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
      ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
        cyc τ = ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓm) := by
  intro A hA τ hτ
  have hm0 : m ≠ 0 := fun h => hℓm (h ▸ dvd_zero ℓ)
  haveI : NeZero m := ⟨hm0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) m

  have hfr : τ ζ = ζ ^ ℓ :=
    ValuationSubring.IsFrobeniusAt.apply_eq_pow_of_pow_eq_one A τ ℓ m hA hτ
      (hℓ.coprime_iff_not_dvd.mpr hℓm).symm ζ hζ.pow_eq_one

  have hkey : ζ ^ ((cyc τ : ZMod m)).val = ζ ^ ℓ := (hcyc τ ζ hζ.pow_eq_one).symm.trans hfr
  have hfin : IsOfFinOrder ζ :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨m, Nat.pos_of_ne_zero hm0, hζ.pow_eq_one⟩
  have hmod : ((cyc τ : ZMod m)).val ≡ ℓ [MOD m] := by
    have h := hfin.pow_eq_pow_iff_modEq.mp hkey
    rwa [← hζ.eq_orderOf] at h
  refine Units.ext ?_
  rw [ZMod.coe_unitOfCoprime]
  have hv : (((cyc τ : ZMod m)).val : ZMod m) = ((ℓ : ℕ) : ZMod m) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  rwa [ZMod.natCast_val, ZMod.cast_id] at hv

example :
    ∀ (m : ℕ)
      (cyc : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod m)ˣ),
      (∀ σ (μ : AlgebraicClosure ℚ), μ ^ m = 1 → σ μ = μ ^ ((cyc σ : ZMod m)).val) →
    ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓm : ¬ ℓ ∣ m),
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
      ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
        cyc τ = ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓm) :=
  solution

#check @solution
#print axioms solution

end S_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
end P2MW
export P2MW.S_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt (solution)
