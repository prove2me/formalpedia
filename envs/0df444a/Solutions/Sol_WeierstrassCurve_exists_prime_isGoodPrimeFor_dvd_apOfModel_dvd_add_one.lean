-- Prove2me | solution 1 for WeierstrassCurve.exists_prime_isGoodPrimeFor_dvd_apOfModel_dvd_add_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/46569df2-100a-5a1e-af3b-f0086d879adf

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_TaylorWiles_Primes
import Theorems.Thm_FrobeniusDensity_exists_frobenius_conj_of_mul_self_eq_one_of_statement
import Theorems.Thm_WeierstrassCurve_galoisTrace_complexConjugation_eq_zero_and_det_eq_neg_one
import Theorems.Thm_FrobeniusDensity_statement
import Theorems.Thm_WeierstrassCurve_IsIntegralModelOf_galoisTrace_det_frobenius
import Theorems.Thm_WeierstrassCurve_galoisRepModuleEnd_factorsThroughFiniteLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_prime_isGoodPrimeFor_dvd_apOfModel_dvd_add_one
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral FrobeniusDensity.liesOver_ratBelow"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal FrobeniusEndo.linePencil_apply WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine.Point
open scoped CongruenceSubgroup

noncomputable section

namespace M5a3ChebW

noncomputable local instance instDecEqQbar : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

theorem isElliptic_map_of_Δ_ne_zero (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) :
    (W.map (Int.castRingHom ℚ)).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, WeierstrassCurve.map_Δ]
  rw [eq_intCast, isUnit_iff_ne_zero]
  exact_mod_cast hΔ

theorem isIntegralModelOf_map (W : WeierstrassCurve ℤ) :
    W.IsIntegralModelOf (W.map (Int.castRingHom ℚ)) :=
  ⟨1, one_smul _ _⟩

end M5a3ChebW

open M5a3ChebW in
theorem solution (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (p : ℕ) (hp : p.Prime) (S : Finset ℕ) :
    ∃ q' : ℕ, q'.Prime ∧ q' ∉ S ∧ W.IsGoodPrimeFor q' ∧
      (p : ℤ) ∣ W.apOfModel q' ∧ (p : ℤ) ∣ (q' : ℤ) + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set E : WeierstrassCurve ℚ := W.map (Int.castRingHom ℚ) with hE
  haveI : E.IsElliptic := isElliptic_map_of_Δ_ne_zero W hΔ
  have hW : W.IsIntegralModelOf E := isIntegralModelOf_map W

  obtain ⟨L, hLfin, hLker⟩ :=
    WeierstrassCurve.galoisRepModuleEnd_factorsThroughFiniteLevel E p
  haveI := hLfin

  have hFD : ∀ (M : Type) [Field M] [NumberField M] [IsGalois ℚ M], FrobeniusDensity.Statement M :=
    fun M _ _ _ => FrobeniusDensity.statement M
  set S' : Finset ℕ := S ∪ ({p} ∪ W.Δ.natAbs.primeFactors) with hS'
  obtain ⟨ℓ, hℓ, hℓS', A, τ, γ, hA, hτ, hfix⟩ :=
    FrobeniusDensity.exists_frobenius_conj_of_mul_self_eq_one_of_statement hFD L complexConjugation
      complexConjugation_mul_self S'
  rw [hS', Finset.mem_union, not_or, Finset.mem_union, not_or, Finset.mem_singleton] at hℓS'
  obtain ⟨hℓS, hℓp, hℓΔ⟩ := hℓS'
  have hgood : W.IsGoodPrimeFor ℓ := by
    intro hdvd
    exact hℓΔ (Nat.mem_primeFactors.mpr
      ⟨hℓ, by simpa using Int.natAbs_dvd_natAbs.mpr hdvd, Int.natAbs_ne_zero.mpr hΔ⟩)

  set ρ := galoisRepModuleEnd (S := ℚ) (K := AlgebraicClosure ℚ) E p with hρ
  have hone : ρ ((γ * τ * γ⁻¹)⁻¹ * complexConjugation) = 1 := by
    apply hLker
    intro x hx
    change (γ * τ * γ⁻¹)⁻¹ (complexConjugation x) = x
    rw [hfix x hx]
    change ((γ * τ * γ⁻¹)⁻¹ * (γ * τ * γ⁻¹)) x = x
    rw [inv_mul_cancel]
    rfl
  have hconj : ρ complexConjugation = ρ γ * ρ τ * ρ γ⁻¹ := by
    have : complexConjugation = (γ * τ * γ⁻¹) * ((γ * τ * γ⁻¹)⁻¹ * complexConjugation) := by group
    rw [this, map_mul, hone, mul_one, map_mul, map_mul]

  obtain ⟨htrc, hdetc⟩ :=
    WeierstrassCurve.galoisTrace_complexConjugation_eq_zero_and_det_eq_neg_one E hp
  rw [galoisTrace_def] at htrc

  have hinv₁ : ρ γ⁻¹ * ρ γ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hinv₂ : ρ γ * ρ γ⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have htrτ : LinearMap.trace (ZMod p) _ (ρ τ) = 0 := by
    rw [← htrc, ← hρ, hconj, LinearMap.trace_mul_comm, ← mul_assoc, hinv₁, one_mul]
  have hdetτ : LinearMap.det (ρ τ) = -1 := by
    rw [← hdetc, ← hρ, hconj, map_mul, map_mul, mul_comm (LinearMap.det (ρ γ)), mul_assoc, ← map_mul,
      hinv₂, map_one, mul_one]

  obtain ⟨h10tr, h10det⟩ := hW.galoisTrace_det_frobenius p ℓ hp hℓ hℓp hgood A hA τ hτ
  rw [galoisTrace_def] at h10tr
  refine ⟨ℓ, hℓ, hℓS, hgood, ?_, ?_⟩
  ·
    have h0 : ((W.apOfModel ℓ : ℤ) : ZMod p) = 0 := by rw [← h10tr]; exact htrτ
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
  ·
    have h0 : (((ℓ : ℤ) + 1 : ℤ) : ZMod p) = 0 := by
      push_cast
      rw [← h10det, hdetτ]; ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0

#print axioms solution

end
end S_WeierstrassCurve_exists_prime_isGoodPrimeFor_dvd_apOfModel_dvd_add_one
end P2MW
export P2MW.S_WeierstrassCurve_exists_prime_isGoodPrimeFor_dvd_apOfModel_dvd_add_one (solution)
