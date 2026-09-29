-- Prove2me | solution 1 for WeierstrassCurve.smul_inertia_displacement_eq_nsmul_of_torsion_of_dvd_discr_of_five_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/7722104d-4820-5ae1-9f10-b5577cf14ee6

import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_TateCurve_TateParameter
import Theorems.Thm_WeierstrassCurve_exists_addEquiv_torsionBy_localGaloisToGlobal_smul_eq_of_dvd_discr_of_five_le
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_smul_inertia_displacement_eq_nsmul_of_torsion_of_dvd_discr_of_five_le
p2m_attr_erase "instance" "GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.Point.instFinite WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false
open scoped WeierstrassCurve.Affine NNReal Classical Polynomial
p2m_open "WeierstrassCurve~card WeierstrassCurve.Affine WeierstrassCurve.Affine.Point"

namespace E87T15

variable (p : ℕ) [Fact p.Prime]

theorem exists_padicEmbedding_eq_of_pow_eq_one {ζ : AlgebraicClosure ℚ_[p]} (hζ : ζ ^ p = 1) :
    ∃ ζ₀ : AlgebraicClosure ℚ, ζ₀ ^ p = 1 ∧ padicEmbedding p ζ₀ = ζ := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  set f : Polynomial (AlgebraicClosure ℚ) := Polynomial.X ^ p - Polynomial.C 1 with hf
  have hsplit : f.Splits := IsAlgClosed.splits f
  have hroots := hsplit.roots_map (padicEmbedding p).toRingHom
  have hfmap : f.map (padicEmbedding p).toRingHom = Polynomial.X ^ p - Polynomial.C 1 := by
    rw [hf, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, map_one]
  have hmem : ζ ∈ (f.map (padicEmbedding p).toRingHom).roots := by
    rw [hfmap, Polynomial.mem_roots (Polynomial.X_pow_sub_C_ne_zero hp0 1)]
    simp [hζ]
  rw [hroots, Multiset.mem_map] at hmem
  obtain ⟨ζ₀, hζ₀, hζ₀eq⟩ := hmem
  refine ⟨ζ₀, ?_, hζ₀eq⟩
  rw [hf, Polynomial.mem_roots (Polynomial.X_pow_sub_C_ne_zero hp0 1)] at hζ₀
  simpa [sub_eq_zero] using hζ₀

theorem exists_exponents {ζ t : AlgebraicClosure ℚ_[p]} (hζ : IsPrimitiveRoot ζ p) {qT : ℚ_[p]}
    (ht : t ^ p = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) qT) (hqT0 : qT ≠ 0)
    (τ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) :
    ∃ e c : ℕ, τ ζ = ζ ^ e ∧ τ t = ζ ^ c * t := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos

  have h1 : (τ ζ) ^ p = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  obtain ⟨e, -, he⟩ := hζ.eq_pow_of_pow_eq_one h1

  have ht0 : t ≠ 0 := by
    intro h; rw [h, zero_pow hp0.ne'] at ht
    exact hqT0 ((map_eq_zero_iff _ (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])).injective).mp ht.symm)
  have h2 : (τ t / t) ^ p = 1 := by
    rw [div_pow, ← map_pow, ht, AlgEquiv.commutes, div_self]
    rw [← ht]; exact pow_ne_zero _ ht0
  obtain ⟨c, -, hc⟩ := hζ.eq_pow_of_pow_eq_one h2
  refine ⟨e, c, he.symm, ?_⟩
  rw [hc, div_mul_cancel₀ _ ht0]

end E87T15

namespace E87T15

theorem main
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hΔ : W.Δ ≠ 0)
    (hpΔ : (p : ℤ) ∣ W.Δ) (hpc₄ : ¬ (p : ℤ) ∣ W.c₄)
    (hcard : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2) :
    ∀ σ ∈ (padicPlace p).inertiaSubgroupIn ℚ, ∀ c : ℕ,
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ ^ c) →
      ∀ τ ∈ (padicPlace p).inertiaSubgroupIn ℚ,
        ∀ y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
          (p : ℤ) • y = 0 → σ • (τ • y - y) = (c : ℤ) • (τ • y - y) := by
  intro σ hσ c hσc τ hτ y hy
  obtain ⟨qT, ζ, t, Φ, hqT0, -, hζ, ht, hact⟩ :=
    W.exists_addEquiv_torsionBy_localGaloisToGlobal_smul_eq_of_dvd_discr_of_five_le p hp5 hΔ hpΔ hpc₄ hcard

  obtain ⟨σ', hσ', hσ'eq⟩ :=
    ValuationSubring.exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq p σ hσ
  obtain ⟨τ', hτ', hτ'eq⟩ :=
    ValuationSubring.exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq p τ hτ

  obtain ⟨eτ, cτ, heτ, hcτ⟩ := exists_exponents p hζ ht hqT0 τ'
  obtain ⟨-, cσ, -, hcσ⟩ := exists_exponents p hζ ht hqT0 σ'
  have heσ : σ' ζ = ζ ^ c := by
    obtain ⟨ζ₀, hζ₀, hζ₀eq⟩ := exists_padicEmbedding_eq_of_pow_eq_one p hζ.pow_eq_one
    rw [← hζ₀eq, ← padicEmbedding_localGaloisToGlobal, hσ'eq, hσc ζ₀ hζ₀, map_pow]

  let Y : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p :=
    ⟨y, (Submodule.mem_torsionBy_iff _ _).mpr hy⟩
  obtain ⟨⟨i, j⟩, hij⟩ := Φ.surjective Y

  have hdisp : τ • Y - Y = Φ ((eτ : ZMod p) • i + (cτ : ℕ) • j - i, 0) := by
    rw [← hij, ← hτ'eq, hact τ' hτ' eτ cτ heτ hcτ i j, ← map_sub, Prod.mk_sub_mk, sub_self]
    simp [nsmul_eq_mul]

  have hkey : σ • (τ • Y - Y) = (c : ℤ) • (τ • Y - Y) := by
    rw [hdisp, ← hσ'eq, hact σ' hσ' c cσ heσ hcσ, smul_zero, add_zero]
    rw [show (((c • ((eτ : ZMod p) • i + (cτ : ℕ) • j - i)) : ZMod p), (0 : ZMod p)) =
        c • (((eτ : ZMod p) • i + (cτ : ℕ) • j - i), (0 : ZMod p)) by
      rw [Prod.smul_mk, smul_zero], map_nsmul, natCast_zsmul]

  have hcoe : ((τ • Y - Y : Submodule.torsionBy ℤ _ p) : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
      = τ • y - y := rfl
  have := congrArg (Subtype.val) hkey
  simp [hcoe] at this
  exact this

end E87T15

theorem solution
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hΔ : W.Δ ≠ 0)
    (hpΔ : (p : ℤ) ∣ W.Δ) (hpc₄ : ¬ (p : ℤ) ∣ W.c₄)
    (hcard : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2) :
    ∀ σ ∈ (padicPlace p).inertiaSubgroupIn ℚ, ∀ c : ℕ,
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ ^ c) →
      ∀ τ ∈ (padicPlace p).inertiaSubgroupIn ℚ,
        ∀ y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
          (p : ℤ) • y = 0 → σ • (τ • y - y) = (c : ℤ) • (τ • y - y) :=
  E87T15.main W p hp5 hΔ hpΔ hpc₄ hcard

end S_WeierstrassCurve_smul_inertia_displacement_eq_nsmul_of_torsion_of_dvd_discr_of_five_le
end P2MW
export P2MW.S_WeierstrassCurve_smul_inertia_displacement_eq_nsmul_of_torsion_of_dvd_discr_of_five_le (solution)
