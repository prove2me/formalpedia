-- Prove2me | solution 1 for WeierstrassCurve.exists_quotient_dualPair_kernelIdealSet_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/fed611b4-1cc3-589b-b3ca-baa8ebb42e19

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal

import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_ker_eq_and_forall_comp_and_kernelIdealSet_eq
import Theorems.Thm_WeierstrassCurve_exists_addOrderOf_eq_prime_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_quotient_dualPair_kernelIdealSet_comp_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.pointAddEquivOfEq_refl compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q'] [Algebra (ZMod q') κ] [Algebra.IsAlgebraic (ZMod q') κ]
    (X₀ W : WeierstrassCurve κ) [X₀.IsElliptic] [W.IsElliptic]
    (hssW : ∀ P : (W.baseChange κ).toAffine.Point, q' • P = 0 → P = 0)
    (χ : (X₀.baseChange κ).toAffine.Point →+ (W.baseChange κ).toAffine.Point)
    (C : AddSubgroup (W.baseChange κ).toAffine.Point) (hC : (C : Set (W.baseChange κ).toAffine.Point).Finite) :
    ∃ (V : WeierstrassCurve κ) (_ : V.IsElliptic) (φ : (W.baseChange κ).toAffine.Point →+ (V.baseChange κ).toAffine.Point)
      (_ : φ ∈ WeierstrassCurve.rationalHomSet κ W V) (φ' : (V.baseChange κ).toAffine.Point →+ (W.baseChange κ).toAffine.Point)
      (_ : φ' ∈ WeierstrassCurve.rationalHomSet κ V W),
      φ.ker = C ∧
      (∀ (W₃ : WeierstrassCurve κ) [W₃.IsElliptic] (α : (W.baseChange κ).toAffine.Point →+ (W₃.baseChange κ).toAffine.Point),
        α ∈ WeierstrassCurve.rationalHomSet κ W W₃ → (∀ P ∈ C, α P = 0) →
          ∃ β ∈ WeierstrassCurve.rationalHomSet κ V W₃, α = β.comp φ) ∧
      φ'.comp φ = Nat.card C • AddMonoidHom.id _ ∧ φ.comp φ' = Nat.card C • AddMonoidHom.id _ ∧
      WeierstrassCurve.kernelIdealSet κ X₀ V (φ.comp χ) =
        {e : ↥(WeierstrassCurve.rationalEndSubring κ X₀) | ∃ σ ∈ WeierstrassCurve.rationalHomSet κ W X₀, (∀ P ∈ C, σ P = 0) ∧
          (e : AddMonoid.End (X₀.baseChange κ).toAffine.Point) = σ.comp χ} := by

  obtain ⟨V, hV, φ, hφ, hker, hup, -⟩ :=
    WeierstrassCurve.exists_mem_rationalHomSet_ker_eq_and_forall_comp_and_kernelIdealSet_eq q' W hssW C hC
  haveI : Finite C := hC

  have hne : φ ≠ 0 := by
    intro h0
    obtain ⟨r, hrge, hrp⟩ := Nat.exists_infinite_primes (max (Nat.card C) q' + 1)
    have hrq : r ≠ q' := by omega
    have hrκ : (r : κ) ≠ 0 := by
      intro h
      exact hrq ((Nat.prime_dvd_prime_iff_eq Fact.out hrp).mp ((CharP.cast_eq_zero_iff κ q' r).mp h)).symm
    obtain ⟨R, hR⟩ : ∃ R : (W.baseChange κ).toAffine.Point, addOrderOf R = r :=
      WeierstrassCurve.exists_addOrderOf_eq_prime_of_isAlgClosed W r hrp hrκ
    have hRC : R ∈ C := by rw [← hker, h0, AddMonoidHom.ker_zero]; trivial
    have hdvd : addOrderOf (⟨R, hRC⟩ : C) ∣ Nat.card C := addOrderOf_dvd_natCard _
    rw [AddSubgroup.addOrderOf_mk, hR] at hdvd
    have := Nat.le_of_dvd Nat.card_pos hdvd
    omega
  have hsurj : Function.Surjective φ := WeierstrassCurve.surjective_of_mem_rationalHomSet κ hφ hne

  have hkill : ∀ P ∈ C, (Nat.card C • AddMonoidHom.id (W.baseChange κ).toAffine.Point) P = 0 := by
    intro P hP
    have h : Nat.card C • (⟨P, hP⟩ : C) = 0 := addOrderOf_dvd_iff_nsmul_eq_zero.mp (addOrderOf_dvd_natCard _)
    have h' : Nat.card C • P = 0 := by
      have := congrArg Subtype.val h
      simpa only [AddSubmonoidClass.coe_nsmul, ZeroMemClass.coe_zero] using this
    simpa using h'

  have hnsmul : (Nat.card C • AddMonoidHom.id (W.baseChange κ).toAffine.Point) ∈ WeierstrassCurve.rationalHomSet κ W W := by
    let S : AddSubmonoid ((W.baseChange κ).toAffine.Point →+ (W.baseChange κ).toAffine.Point) :=
      { carrier := {ρ | ρ ∈ WeierstrassCurve.rationalHomSet κ W W}
        zero_mem' := WeierstrassCurve.zero_mem_rationalHomSet κ W W
        add_mem' := fun hρ hσ => WeierstrassCurve.add_mem_rationalHomSet κ W W hρ hσ }
    exact S.nsmul_mem (show AddMonoidHom.id _ ∈ S from WeierstrassCurve.id_mem_rationalHomSet κ W) _

  obtain ⟨φ', hφ', hβeq⟩ := hup W (Nat.card C • AddMonoidHom.id _) hnsmul hkill
  have hright : φ.comp φ' = Nat.card C • AddMonoidHom.id _ := by
    refine (AddMonoidHom.cancel_right hsurj).mp ?_
    ext P
    have e1 : φ' (φ P) = Nat.card C • P := (DFunLike.congr_fun hβeq P).symm
    show φ (φ' (φ P)) = Nat.card C • (φ P)
    rw [e1, map_nsmul]
  refine ⟨V, hV, φ, hφ, φ', hφ', hker, fun W₃ _ α hα hαC => hup W₃ α hα hαC, hβeq.symm, hright, ?_⟩
  ext e
  constructor
  · rintro ⟨ρ, hρ, he⟩
    refine ⟨ρ.comp φ, WeierstrassCurve.comp_mem_rationalHomSet κ W V X₀ hφ hρ, fun P hP => ?_, ?_⟩
    · have hP' : P ∈ φ.ker := by rw [hker]; exact hP
      show ρ (φ P) = 0
      rw [AddMonoidHom.mem_ker.mp hP']
      exact map_zero ρ
    · rw [he]; rfl
  · rintro ⟨σ, hσ, hσC, he⟩
    obtain ⟨β, hβ, hσβ⟩ := hup X₀ σ hσ hσC
    exact ⟨β, hβ, by rw [he, hσβ]; rfl⟩

end S_WeierstrassCurve_exists_quotient_dualPair_kernelIdealSet_comp_eq
end P2MW
export P2MW.S_WeierstrassCurve_exists_quotient_dualPair_kernelIdealSet_comp_eq (solution)
