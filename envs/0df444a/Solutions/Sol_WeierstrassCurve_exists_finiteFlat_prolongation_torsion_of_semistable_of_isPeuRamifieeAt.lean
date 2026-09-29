-- Prove2me | solution 1 for WeierstrassCurve.exists_finiteFlat_prolongation_torsion_of_semistable_of_isPeuRamifieeAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/61658e69-28c8-5312-b13a-6644562ffc8a

import Theorems.Thm_WeierstrassCurve_exists_finiteFlat_prolongation_torsion_of_multiplicativeReduction_of_peuRamifiee
import Theorems.Thm_WeierstrassCurve_exists_finiteFlat_prolongation_torsion_of_integralModel_isUnit_discr
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_WeierstrassCurve_PeuRamifiee
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_finiteFlat_prolongation_torsion_of_semistable_of_isPeuRamifieeAt
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly PadicInt.KummerCarrier.instFreeA PadicInt.KummerCarrier.instFiniteA HomogeneousIdealQuotientGrading.quotGradingSubmoduleGradedMonoid HomogeneousIdealQuotientGrading.quotGradingGradedMonoid HomogeneousIdealQuotientGrading.quotGradingSubmoduleGradedAlgebraOfHomogeneous HomogeneousIdealQuotientGrading.quotGradingGradedRingOfHomogeneous WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "simp" "TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.Universal.halveX_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassProjModel.schemeHomOverComp_coe WeierstrassProjModel.RelativeGroupLaw.mk.sizeOf_spec WeierstrassProjModel.RelativeGroupLaw.nsmul_zero WeierstrassProjModel.RelativeGroupLaw.nsmul_succ WeierstrassProjModel.projModelHomogeneousIdealCR_toIdeal WeierstrassProjModel.RelativeGroupLaw.mk.injEq WeierstrassProjModel.RelativeGroupLaw.mem_torsionSubset HomogeneousIdealQuotientGrading.pieceHom_coe HomogeneousIdealQuotientGrading.quotDecompose_mk HomogeneousIdealQuotientGrading.quotGradingPieceHom_coe NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X WeierstrassProjModel.kw_lrThird_substHom_X AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add"
p2m_attr_erase "simp" "AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec"

set_option autoImplicit false

noncomputable section

namespace FFSketchNS
open GaloisRep

section IrrZp
variable {p : ℕ}

theorem val_nonneg_of_mem [hp : Fact p.Prime] {q : ℚ} (hq : q ∈ ratLocalizedAt p) (hq0 : q ≠ 0) :
    0 ≤ padicValRat p q := by
  have hden : padicValNat p q.den = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun h => by
      have : p ∣ Nat.gcd q.den p := Nat.dvd_gcd h dvd_rfl
      rw [Nat.Coprime.gcd_eq_one hq] at this
      exact hp.out.one_lt.ne' (Nat.dvd_one.mp this))
  unfold padicValRat
  simp [hden]

theorem isUnit_of_val_eq_zero [hp : Fact p.Prime] {q : ℚ} (hq : q ∈ ratLocalizedAt p) (hq0 : q ≠ 0)
    (hv : padicValRat p q = 0) : IsUnit (⟨q, hq⟩ : ratLocalizedAt p) := by

  have hden : padicValNat p q.den = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun h => by
      have : p ∣ Nat.gcd q.den p := Nat.dvd_gcd h dvd_rfl
      rw [Nat.Coprime.gcd_eq_one hq] at this
      exact hp.out.one_lt.ne' (Nat.dvd_one.mp this))
  have hnum : ¬ (p : ℤ) ∣ q.num := by
    intro hdvd
    rw [padicValRat_def, hden, Nat.cast_zero, sub_zero, Nat.cast_eq_zero] at hv
    have h1 := (padicValInt_dvd_iff 1 q.num).mp (by simpa using hdvd)
    rcases h1 with h1 | h1
    · exact (Rat.num_ne_zero.mpr hq0) h1
    · omega

  have hinv : q⁻¹ ∈ ratLocalizedAt p := by
    show (q⁻¹).den.Coprime p
    have hq' : q⁻¹ = Rat.divInt q.den q.num := by
      conv_lhs => rw [← Rat.num_divInt_den q]
      rw [Rat.inv_divInt]
    have hd : ((q⁻¹).den : ℤ) ∣ q.num := by rw [hq']; exact Rat.den_dvd _ _
    apply Nat.Coprime.symm
    apply (Nat.Prime.coprime_iff_not_dvd hp.out).mpr
    intro h
    exact hnum (dvd_trans (Int.natCast_dvd_natCast.mpr h) hd)
  refine isUnit_iff_exists_inv.mpr ⟨⟨q⁻¹, hinv⟩, Subtype.ext ?_⟩
  show q * q⁻¹ = 1
  exact mul_inv_cancel₀ hq0

theorem irreducible_natCast_ratLocalizedAt' (p : ℕ) (hp : p.Prime) :
    Irreducible ((p : ℕ) : ratLocalizedAt p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpval : ((p : ℕ) : ratLocalizedAt p).1 = (p : ℚ) := by simp
  refine ⟨?_, ?_⟩
  ·
    intro hu
    obtain ⟨u, hu⟩ := hu
    have h1 : u.1.1 * (u⁻¹ : (ratLocalizedAt p)ˣ).1.1 = 1 := by
      have := congrArg (fun x : ratLocalizedAt p => x.1) (u.mul_inv)
      simpa only [Subring.coe_mul, Subring.coe_one] using this
    rw [hu, hpval] at h1
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hinv : (u⁻¹ : (ratLocalizedAt p)ˣ).1.1 = (p : ℚ)⁻¹ := by
      rw [← mul_inv_cancel₀ hp0] at h1
      exact mul_left_cancel₀ hp0 h1
    have hmem : ((p : ℚ)⁻¹).den.Coprime p := by rw [← hinv]; exact (u⁻¹ : (ratLocalizedAt p)ˣ).1.2
    rw [Rat.inv_natCast_den, if_neg hp.ne_zero] at hmem
    exact hp.one_lt.ne' ((Nat.coprime_self p).mp hmem)
  ·
    intro a b hab
    have ha0 : a.1 ≠ 0 := by
      intro h; have := congrArg (fun x : ratLocalizedAt p => x.1) hab
      simp [h] at this; exact hp.ne_zero (by exact_mod_cast this)
    have hb0 : b.1 ≠ 0 := by
      intro h; have := congrArg (fun x : ratLocalizedAt p => x.1) hab
      simp [h] at this; exact hp.ne_zero (by exact_mod_cast this)
    have hv : padicValRat p a.1 + padicValRat p b.1 = 1 := by
      have := congrArg (fun x : ratLocalizedAt p => padicValRat p x.1) hab
      simp only [Subring.coe_mul] at this
      rw [padicValRat.mul ha0 hb0] at this
      rw [← this, hpval]
      exact padicValRat.self hp.one_lt
    have ha := val_nonneg_of_mem a.2 ha0
    have hb := val_nonneg_of_mem b.2 hb0
    rcases (show padicValRat p a.1 = 0 ∨ padicValRat p b.1 = 0 by omega) with h | h
    · left; have := isUnit_of_val_eq_zero a.2 ha0 h; simpa using this
    · right; have := isUnit_of_val_eq_zero b.2 hb0 h; simpa using this

end IrrZp

theorem isUnit_intCast_ratLocalizedAt {p : ℕ} (hp : p.Prime) {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) :
    IsUnit ((n : ℤ) : ratLocalizedAt p) := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero _)
  have hmem : ((n : ℚ)⁻¹) ∈ ratLocalizedAt p := by
    show ((n : ℚ)⁻¹).den.Coprime p
    rw [Rat.inv_intCast_den, if_neg hn0]
    exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h => hn (Int.ofNat_dvd_left.mpr h))))
  refine isUnit_iff_exists_inv.mpr ⟨⟨(n : ℚ)⁻¹, hmem⟩, ?_⟩
  apply Subtype.ext
  show ((n : ℤ) : ratLocalizedAt p).1 * (n : ℚ)⁻¹ = 1
  have : ((n : ℤ) : ratLocalizedAt p).1 = (n : ℚ) := by simp
  rw [this]
  exact mul_inv_cancel₀ (by exact_mod_cast hn0)

open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in
theorem ff_solution (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hΔ : W.Δ ≠ 0)
    (hsemi : (p : ℤ) ∣ W.Δ → ¬ (p : ℤ) ∣ W.c₄)
    (hfin : (W.map (Int.castRingHom ℚ)).IsPeuRamifieeAt p p) :
    letI : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
      Module.Finite (GaloisRep.ratLocalizedAt p) H ∧
      Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
      ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
          Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ h : H, g h = σ (f h)) → e g = σ • (e f) := by
  have hp : p.Prime := Fact.out
  have hWE : W.IsIntegralModelOf (W.map (Int.castRingHom ℚ)) := ⟨1, one_smul _ _⟩
  by_cases hpΔ : (p : ℤ) ∣ W.Δ
  ·
    have hpr : p ∣ padicValInt p W.Δ := by
      have h := hfin
      unfold WeierstrassCurve.IsPeuRamifieeAt at h
      rw [WeierstrassCurve.map_Δ, eq_intCast, padicValRat.of_int] at h
      exact Int.natCast_dvd_natCast.mp h
    exact WeierstrassCurve.exists_finiteFlat_prolongation_torsion_of_multiplicativeReduction_of_peuRamifiee
      (W.map (Int.castRingHom ℚ)) hWE p hΔ hpΔ (hsemi hpΔ) hpr
  ·
    haveI : IsDiscreteValuationRing (ratLocalizedAt p) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p hp
    haveI : IsFractionRing (ratLocalizedAt p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p
    have heq : (W.map (Int.castRingHom (ratLocalizedAt p)))⁄ℚ = W.map (Int.castRingHom ℚ) := by
      show (W.map (Int.castRingHom (ratLocalizedAt p))).map (algebraMap (ratLocalizedAt p) ℚ) = _
      rw [WeierstrassCurve.map_map, RingHom.ext_int ((algebraMap (ratLocalizedAt p) ℚ).comp (Int.castRingHom (ratLocalizedAt p))) (Int.castRingHom ℚ)]
    have hΔu : IsUnit (W.map (Int.castRingHom (ratLocalizedAt p))).Δ := by
      rw [WeierstrassCurve.map_Δ, eq_intCast]
      exact isUnit_intCast_ratLocalizedAt hp hpΔ
    exact WeierstrassCurve.exists_finiteFlat_prolongation_torsion_of_integralModel_isUnit_discr
      (ratLocalizedAt p) (W.map (Int.castRingHom ℚ)) (W.map (Int.castRingHom (ratLocalizedAt p))) heq hΔu p
      (irreducible_natCast_ratLocalizedAt' p hp)

end FFSketchNS

end

open scoped WeierstrassCurve.Affine in
open WeierstrassCurve.Affine.Point in
theorem solution
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hΔ : W.Δ ≠ 0)
    (hsemi : (p : ℤ) ∣ W.Δ → ¬ (p : ℤ) ∣ W.c₄)
    (hfin : (W.map (Int.castRingHom ℚ)).IsPeuRamifieeAt p p) :
    letI : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
      Module.Finite (GaloisRep.ratLocalizedAt p) H ∧
      Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
      ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
          Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ h : H, g h = σ (f h)) → e g = σ • (e f) :=
  FFSketchNS.ff_solution W p hΔ hsemi hfin

end S_WeierstrassCurve_exists_finiteFlat_prolongation_torsion_of_semistable_of_isPeuRamifieeAt
end P2MW
export P2MW.S_WeierstrassCurve_exists_finiteFlat_prolongation_torsion_of_semistable_of_isPeuRamifieeAt (solution)
