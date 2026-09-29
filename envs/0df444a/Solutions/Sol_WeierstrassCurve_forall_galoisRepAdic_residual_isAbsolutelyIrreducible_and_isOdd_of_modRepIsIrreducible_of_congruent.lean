-- Prove2me | solution 1 for WeierstrassCurve.forall_galoisRepAdic_residual_isAbsolutelyIrreducible_and_isOdd_of_modRepIsIrreducible_of_congruent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/e565292e-4b03-5973-874c-879751b5542a

import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_GaloisRep_ResidualEquiv
import Definitions.Def_EllipticCurve_TateModule
import Theorems.Thm_WeierstrassCurve_residualGaloisRepOf_isIrreducible_iff
import Theorems.Thm_WeierstrassCurve_residualGaloisRepOf_isOdd
import Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_of_isIrreducible_of_isOdd
import Theorems.Thm_ResidualGaloisRep_IsAbsolutelyIrreducible_baseChangeAlong
import Theorems.Thm_ResidualGaloisRep_IsAbsolutelyIrreducible_of_isEquiv
import Theorems.Thm_ResidualGaloisRep_charpoly_eq
import Theorems.Thm_ResidualGaloisRep_charpoly_baseChangeAlong
import Theorems.Thm_WeierstrassCurve_card_torsionBy_eq_sq_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_galoisRepModuleEnd_factorsThroughFiniteLevel
import Theorems.Thm_WeierstrassCurve_tateModuleRep_charpoly_frobenius
import Theorems.Thm_WeierstrassCurve_tateModuleRep_baseChangeAlong_residual_isEquiv
import Theorems.Thm_GaloisRepAdic_charpoly_residual
import Theorems.Thm_GaloisRepAdic_charpoly_baseChangeAlong
import Theorems.Thm_GaloisRepAdic_residual_isEquiv_and_det_sub_mem_of_charpoly_frobenius_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_forall_galoisRepAdic_residual_isAbsolutelyIrreducible_and_isOdd_of_modRepIsIrreducible_of_congruent
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ValuationSubring.instIsAlgClosedResidueField FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal FrobeniusEndo.linePencil_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false
open Polynomial
open scoped WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

namespace DischargeLeaf

open IsLocalRing

private theorem det_eq_of_equiv {k : Type} [Field k] {ρ₁ ρ₂ : ResidualGaloisRep k} (e : ρ₁.Equiv ρ₂)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : LinearMap.det (ρ₂.ρ σ) = LinearMap.det (ρ₁.ρ σ) := by
  have h : ρ₂.ρ σ = (e.toLinearEquiv : ρ₁.V →ₗ[k] ρ₂.V) ∘ₗ ρ₁.ρ σ ∘ₗ (e.toLinearEquiv.symm : ρ₂.V →ₗ[k] ρ₁.V) := by
    apply LinearMap.ext
    intro y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [e.map_apply, LinearEquiv.apply_symm_apply]
  rw [h, LinearMap.det_conj]

private theorem isOdd_of_isEquiv {k : Type} [Field k] {ρ₁ ρ₂ : ResidualGaloisRep k} (e : ρ₁.IsEquiv ρ₂)
    (h : ρ₁.IsOdd) : ρ₂.IsOdd := by
  obtain ⟨e⟩ := e
  intro c hc hc1
  rw [det_eq_of_equiv e c]
  exact h c hc hc1

private theorem det_baseChangeAlong_eq_map {k k' : Type} [Field k] [Field k'] (ψ : k →+* k') (ρ : ResidualGaloisRep k)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.det ((ρ.baseChangeAlong ψ).ρ σ) = ψ (LinearMap.det (ρ.ρ σ)) := by
  have h1 := (ρ.baseChangeAlong ψ).charpoly_eq σ
  have h2 := ρ.charpoly_baseChangeAlong ψ σ
  have h3 := ρ.charpoly_eq σ
  have h := congrArg (fun f : k'[X] => f.coeff 0) (h1.symm.trans (h2.trans (congrArg (Polynomial.map ψ) h3)))
  simpa [Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_map] using h

private theorem isOdd_baseChangeAlong {k k' : Type} [Field k] [Field k'] (ψ : k →+* k') {ρ : ResidualGaloisRep k}
    (h : ρ.IsOdd) : (ρ.baseChangeAlong ψ).IsOdd := by
  intro c hc hc1
  rw [det_baseChangeAlong_eq_map, h c hc hc1, map_neg, map_one]

private theorem isEquiv_symm {k : Type} [Field k] {ρ₁ ρ₂ : ResidualGaloisRep k} (e : ρ₁.IsEquiv ρ₂) :
    ρ₂.IsEquiv ρ₁ := by
  obtain ⟨e⟩ := e
  exact ⟨e.symm⟩

private theorem two_ne_zero_zmod (lam : ℕ) [hp : Fact lam.Prime] (hlam2 : lam ≠ 2) : (2 : ZMod lam) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod lam) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff (ZMod lam) lam] at h'
  exact hlam2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h')

private theorem main
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    (lam : ℕ) [hp : Fact lam.Prime]
    (S : Finset ℕ)
    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [Finite (IsLocalRing.ResidueField O')]
    [CharZero O'] (hlamO' : (lam : O') ∈ IsLocalRing.maximalIdeal O')
    (chig : CuspForm.heckeAlgebra M 2 (↑S : Set ℕ) →+* ℂ)
    (iota : chig.range →+* O')
    (hlamS : lam ∈ S) (hMS : ∀ q : ℕ, q.Prime → q ∣ M → q ∈ S)
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (hbadS : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ W.Δ → q ∈ S)
    (hlam2 : lam ≠ 2) (hirr : W.ModRepIsIrreducible lam)
    (hcong : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      IsLocalRing.residue O' ((iota.comp chig.rangeRestrict) (CuspForm.heckeAlgebra.T hℓ hℓM hℓS)) =
        IsLocalRing.residue O' ((W.apOfModel ℓ : ℤ) : O'))
    (O'' : Type) [CommRing O''] [IsDomain O''] [IsDiscreteValuationRing O'']
    [IsAdicComplete (IsLocalRing.maximalIdeal O'') O''] [Finite (IsLocalRing.ResidueField O'')] [CharZero O'']
    [Algebra O' O''] [Module.Finite O' O''] [IsLocalHom (algebraMap O' O'')]
    (_hinj : Function.Injective (algebraMap O' O'')) (ρ : GaloisRepAdic O'')
    (hspec : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (_ : ℓ ≠ lam) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)),
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            LinearMap.charpoly (ρ.ρ σ) =
              X ^ 2 - C (algebraMap O' O'' ((iota.comp chig.rangeRestrict) (CuspForm.heckeAlgebra.T hℓ hℓM hℓS))) * X
                + C ((ℓ : O''))) :
    ρ.residual.IsAbsolutelyIrreducible ∧ ρ.residual.IsOdd := by

  have hpO'' : (lam : O'') ∈ maximalIdeal O'' := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hu' : IsUnit (algebraMap O' O'' (lam : O')) := by simpa using hu
    exact (mem_maximalIdeal _).mp hlamO' (‹IsLocalHom (algebraMap O' O'')›.map_nonunit _ hu')

  set Wq : WeierstrassCurve ℚ := W.map (Int.castRingHom ℚ) with hWq
  haveI hell : Wq.IsElliptic := ⟨by
    rw [hWq, WeierstrassCurve.map_Δ]
    exact isUnit_iff_ne_zero.mpr (by simpa using hΔ)⟩
  haveI hellbar : (Wq⁄(AlgebraicClosure ℚ)).IsElliptic :=
    ⟨by
      show IsUnit (Wq.map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ
      rw [WeierstrassCurve.map_Δ]
      exact hell.isUnit.map _⟩
  classical

  have hcardAll : ∀ n : ℕ,
      Nat.card (Submodule.torsionBy ℤ (Wq⁄(AlgebraicClosure ℚ)).Point ((lam ^ n : ℕ) : ℤ)) = (lam ^ n) ^ 2 :=
    fun n => WeierstrassCurve.card_torsionBy_eq_sq_of_isAlgClosed (Wq⁄(AlgebraicClosure ℚ))
      (by exact_mod_cast pow_ne_zero n (Nat.cast_ne_zero.mpr hp.out.ne_zero)) two_ne_zero
  have hcard₁ : Nat.card (Submodule.torsionBy ℤ (Wq⁄(AlgebraicClosure ℚ)).Point lam) = lam ^ 2 :=
    WeierstrassCurve.card_torsionBy_eq_sq_of_isAlgClosed (Wq⁄(AlgebraicClosure ℚ))
      (Nat.cast_ne_zero.mpr hp.out.ne_zero) two_ne_zero
  have hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ Wq lam) :=
    Wq.galoisRepModuleEnd_factorsThroughFiniteLevel lam

  set ρW : ResidualGaloisRep (ZMod lam) := Wq.residualGaloisRepOf lam hcard₁ hker with hρW
  have hWirr : ρW.IsIrreducible := (Wq.residualGaloisRepOf_isIrreducible_iff lam hcard₁ hker).mpr hirr
  have hWodd : ρW.IsOdd := Wq.residualGaloisRepOf_isOdd lam hcard₁ hker
  have hWabs : ρW.IsAbsolutelyIrreducible :=
    ρW.isAbsolutelyIrreducible_of_isIrreducible_of_isOdd (two_ne_zero_zmod lam hlam2) hWirr hWodd

  have hchar : ringChar (ResidueField O'') = lam := by
    have h0 : ((lam : ℕ) : ResidueField O'') = 0 := by
      rw [← map_natCast (residue O'') lam]
      exact (residue_eq_zero_iff _).mpr hpO''
    rcases (Nat.dvd_prime hp.out).mp (ringChar.dvd h0) with h | h
    · exact absurd h CharP.ringChar_ne_one
    · exact h
  let ι : ZMod lam →+* ResidueField O'' := ZMod.castHom (by rw [hchar]) (ResidueField O'')

  set ρT : GaloisRepAdic O'' :=
    (Wq.tateModuleRep lam hcardAll).baseChangeAlong (GaloisRep.padicIntToRing O'' lam hpO'')
      (GaloisRep.isLocalHom_padicIntToRing O'' lam hpO'') with hρT
  have hTequiv : ρT.residual.IsEquiv (ρW.baseChangeAlong ι) :=
    Wq.tateModuleRep_baseChangeAlong_residual_isEquiv lam hcardAll hcard₁ hker hpO'' ι
  have hTabs : ρT.residual.IsAbsolutelyIrreducible :=
    ResidualGaloisRep.IsAbsolutelyIrreducible.of_isEquiv (isEquiv_symm hTequiv) (hWabs.baseChangeAlong ι)
  have hTodd : ρT.residual.IsOdd := isOdd_of_isEquiv (isEquiv_symm hTequiv) (isOdd_baseChangeAlong ι hWodd)

  have hgood : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → W.IsGoodPrimeFor ℓ := fun ℓ hℓ hℓS hdvd => hℓS (hbadS ℓ hℓ hdvd)
  have hnelam : ∀ ℓ : ℕ, ℓ ∉ S → ℓ ≠ lam := fun ℓ hℓS h => hℓS (h ▸ hlamS)
  have hnotM : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ M := fun ℓ hℓ hℓS h => hℓS (hMS ℓ hℓ h)
  have hnotS : ∀ ℓ : ℕ, ℓ ∉ S → ℓ ∉ (↑S : Set ℕ) := fun ℓ hℓS => by simpa using hℓS

  have hκ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ),
      μ ^ (1 : ℕ) = 1 → σ μ = μ ^ (((1 : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod 1)ˣ) σ :
        ZMod 1)).val := by
    intro σ μ hμ
    rw [pow_one] at hμ
    subst hμ
    simp
  obtain ⟨hequiv, -, -⟩ :=
    GaloisRepAdic.residual_isEquiv_and_det_sub_mem_of_charpoly_frobenius_eq lam hpO'' ρ ρT.residual hTabs
      (RingHom.id _) 1 1 hκ 1 (Or.inl hlam2) S
      (fun ℓ hℓ hℓS => algebraMap O' O''
        ((iota.comp chig.rangeRestrict) (CuspForm.heckeAlgebra.T hℓ (hnotM ℓ hℓ hℓS) (hnotS ℓ hℓS))))
      (fun ℓ _ _ => residue O'' ((W.apOfModel ℓ : ℤ) : O''))
      (by

        intro ℓ hℓ hℓS
        rw [RingHom.id_apply, ← ResidueField.map_residue (algebraMap O' O''), hcong ℓ hℓ (hnotM ℓ hℓ hℓS)
          (hnotS ℓ hℓS), ResidueField.map_residue, map_intCast])
      (by
        intro ℓ hℓ hℓS A hA σ hσ
        rw [hspec ℓ hℓ (hnelam ℓ hℓS) (hnotM ℓ hℓ hℓS) (hnotS ℓ hℓS) A hA σ hσ]
        simp)
      (by

        intro ℓ hℓ hℓS A hA σ hσ
        rw [GaloisRepAdic.charpoly_residual, hρT, GaloisRepAdic.charpoly_baseChangeAlong,
          WeierstrassCurve.tateModuleRep_charpoly_frobenius W lam hcardAll ℓ hℓ (hgood ℓ hℓ hℓS) (hnelam ℓ hℓS) A hA
            σ hσ]
        simp [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_intCast,
          map_natCast])

  have hid : (ρT.residual.baseChangeAlong (RingHom.id _)).IsAbsolutelyIrreducible := hTabs.baseChangeAlong _
  refine ⟨ResidualGaloisRep.IsAbsolutelyIrreducible.of_isEquiv (isEquiv_symm hequiv) hid, ?_⟩
  exact isOdd_of_isEquiv (isEquiv_symm hequiv) (isOdd_baseChangeAlong _ hTodd)

end DischargeLeaf

theorem solution
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    (lam : ℕ) [Fact lam.Prime]
    (S : Finset ℕ)
    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [Finite (IsLocalRing.ResidueField O')]
    [CharZero O'] (hlamO' : (lam : O') ∈ IsLocalRing.maximalIdeal O')
    (chig : CuspForm.heckeAlgebra M 2 (↑S : Set ℕ) →+* ℂ)
    (hchig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      chig (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) = ModularFormClass.qCoeff g ℓ)
    (iota : chig.range →+* O')
    (hlamS : lam ∈ S) (hMS : ∀ q : ℕ, q.Prime → q ∣ M → q ∈ S)
    (W : WeierstrassCurve ℤ) (hss : W.IsSemistableModel) (hΔ : W.Δ ≠ 0)
    (hbadS : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ W.Δ → q ∈ S)
    (hlam2 : lam ≠ 2) (hirr : W.ModRepIsIrreducible lam)
    (hcong : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      IsLocalRing.residue O' ((iota.comp chig.rangeRestrict) (CuspForm.heckeAlgebra.T hℓ hℓM hℓS)) =
        IsLocalRing.residue O' ((W.apOfModel ℓ : ℤ) : O'))
    :
    ∀ (O'' : Type) [CommRing O''] [IsDomain O''] [IsDiscreteValuationRing O'']
      [IsAdicComplete (IsLocalRing.maximalIdeal O'') O''] [Finite (IsLocalRing.ResidueField O'')] [CharZero O'']
      [Algebra O' O''] [Module.Finite O' O''] [IsLocalHom (algebraMap O' O'')],
      Function.Injective (algebraMap O' O'') → ∀ (ρ : GaloisRepAdic O''),
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓlam : ℓ ≠ lam) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)),
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            LinearMap.charpoly (ρ.ρ σ) =
              X ^ 2 - C (algebraMap O' O'' ((iota.comp chig.rangeRestrict) (CuspForm.heckeAlgebra.T hℓ hℓM hℓS))) * X
                + C ((ℓ : O'')))
      → ρ.residual.IsAbsolutelyIrreducible ∧ ρ.residual.IsOdd := by
  have _ := hchig
  have _ := hss
  intro O'' _ _ _ _ _ _ _ _ _ hinj ρ hspec
  exact DischargeLeaf.main hg lam S O' hlamO' chig iota hlamS hMS W hΔ hbadS hlam2 hirr hcong O'' hinj ρ hspec

end S_WeierstrassCurve_forall_galoisRepAdic_residual_isAbsolutelyIrreducible_and_isOdd_of_modRepIsIrreducible_of_congruent
end P2MW
export P2MW.S_WeierstrassCurve_forall_galoisRepAdic_residual_isAbsolutelyIrreducible_and_isOdd_of_modRepIsIrreducible_of_congruent (solution)
