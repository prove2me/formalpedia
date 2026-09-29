-- Prove2me | solution 1 for WeierstrassCurve.modRep_blrDecomposition_heckeTorsion_of_frobeniusQuadratic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/ae6b0f63-29cc-50af-b3e0-47fb3d4bbb91

import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FreyPackage_MazurAttachmentApparatus
import Theorems.Thm_Representation_exists_blrDecomposition_of_spanTop_of_quadraticAnnihilation
import Theorems.Thm_ModularCurve_mTorsionGaloisRep_quadratic_of_frobeniusQuadratic_of_frobeniusPowerDense
import Theorems.Thm_WeierstrassCurve_IsIntegralModelOf_galoisTrace_det_frobenius
import Theorems.Thm_WeierstrassCurve_residualGaloisRepOf_isIrreducible_iff
import Theorems.Thm_WeierstrassCurve_residualGaloisRepOf_isOdd
import Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_of_isIrreducible_of_isOdd
import Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_iff_span_eq_top
import Theorems.Thm_Matrix_span_image_map_eq_top_of_span_eq_top
import Theorems.Thm_FreyPackage_frobeniusPowerDense_inf_of_restrictionKer_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_modRep_blrDecomposition_heckeTorsion_of_frobeniusQuadratic
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "FrobeniusEndo.linePencil_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false
open ModularCurve WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine

local instance instIsAlgebraicQbarBLRW : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ
local instance instIsAlgClosureQbarBLRW : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨inferInstance, inferInstance⟩
local instance instNormalQbarBLRW : Normal ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

namespace M5A3RibbonBLRW

private noncomputable def ρmatE (E : WeierstrassCurve ℚ) (p : ℕ)
    (b : Module.Basis (Fin 2) (ZMod p) (Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point p)) :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) (ZMod p) :=
  ((LinearMap.toMatrixAlgEquiv b).toMulEquiv.toMonoidHom).comp
    (galoisRepModuleEnd (S := ℚ) (K := AlgebraicClosure ℚ) E p)

private theorem spanTop_aux (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2)
    (𝔪 : Ideal HeckeAlg) (hmax : 𝔪.IsMaximal) [CharP (HeckeAlg ⧸ 𝔪) p]
    (hirr : GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ E p)
    (hker : GaloisFactorsThroughFiniteLevel
      (galoisRepModuleEnd (S := ℚ) (K := AlgebraicClosure ℚ) E p))
    (b : Module.Basis (Fin 2) (ZMod p) (Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point p)) :
    Submodule.span (HeckeAlg ⧸ 𝔪)
        (Set.range fun σ =>
          (ρmatE E p b σ).map (ZMod.castHom (dvd_refl p) (HeckeAlg ⧸ 𝔪))) = ⊤ := by
  haveI := hmax
  haveI hfinT : Finite (Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point p) :=
    Finite.of_equiv _ b.equivFun.toEquiv.symm
  have hcard : Nat.card (Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod,
      Module.finrank_eq_card_basis b, Fintype.card_fin]
  set R := E.residualGaloisRepOf p hcard hker with hRdef
  have hirrR : R.IsIrreducible :=
    (E.residualGaloisRepOf_isIrreducible_iff p hcard hker).mpr hirr
  have hoddR : R.IsOdd := E.residualGaloisRepOf_isOdd p hcard hker
  have h2 : (2 : ZMod p) ≠ 0 := by
    rw [show ((2 : ZMod p)) = ((2 : ℕ) : ZMod p) by norm_cast, Ne,
      CharP.cast_eq_zero_iff (ZMod p) p 2]
    exact fun hdvd => hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hdvd)
  have habs : R.IsAbsolutelyIrreducible :=
    R.isAbsolutelyIrreducible_of_isIrreducible_of_isOdd h2 hirrR hoddR
  have hspanE : Submodule.span (ZMod p) (Set.range ⇑R.ρ) = ⊤ :=
    R.isAbsolutelyIrreducible_iff_span_eq_top.mp habs
  have hspanM : Submodule.span (ZMod p) (Set.range fun σ => ρmatE E p b σ) = ⊤ := by
    have hmaple : Submodule.map (LinearMap.toMatrixAlgEquiv b).toLinearMap
        (Submodule.span (ZMod p) (Set.range ⇑R.ρ)) ≤
        Submodule.span (ZMod p) (Set.range fun σ => ρmatE E p b σ) :=
      (Submodule.map_span_le _ _ _).mpr
        (by rintro _ ⟨σ, rfl⟩; exact Submodule.subset_span ⟨σ, rfl⟩)
    rw [eq_top_iff]
    intro X _
    have hX : (LinearMap.toMatrixAlgEquiv b).symm X ∈
        Submodule.span (ZMod p) (Set.range ⇑R.ρ) := by rw [hspanE]; trivial
    exact hmaple ⟨_, hX, AlgEquiv.apply_symm_apply _ _⟩
  have hspanK : Submodule.span (HeckeAlg ⧸ 𝔪)
      ((fun X : Matrix (Fin 2) (Fin 2) (ZMod p) =>
          X.map (ZMod.castHom (dvd_refl p) (HeckeAlg ⧸ 𝔪))) ''
        Set.range fun σ => ρmatE E p b σ) = ⊤ := by
    letI : Field (HeckeAlg ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    exact Matrix.span_image_map_eq_top_of_span_eq_top
      (ZMod.castHom (dvd_refl p) (HeckeAlg ⧸ 𝔪)) hspanM
  rw [← Set.range_comp, Function.comp_def] at hspanK
  exact hspanK

private theorem trace_det_aux (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (W : WeierstrassCurve ℤ) (hW : W.IsIntegralModelOf E)
    (p : ℕ) [Fact p.Prime]
    {M : ℕ} (hM : 0 < M) (𝔪 : Ideal HeckeAlg) [CharP (HeckeAlg ⧸ 𝔪) p]
    (hcong : FreyPackage.IdealGoodPrimeCurveCongruence p M W 𝔪)
    (b : Module.Basis (Fin 2) (ZMod p) (Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point p)) :
    (∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ (M * p * W.Δ.natAbs).primeFactors → ¬ ℓ ∣ M * p) ∧
    ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ (M * p * W.Δ.natAbs).primeFactors →
      ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ →
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ ℓ →
          Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩)
              = ((ρmatE E p b σ).map (ZMod.castHom (dvd_refl p) (HeckeAlg ⧸ 𝔪))).trace ∧
            Ideal.Quotient.mk 𝔪 ((ℓ : HeckeAlg))
              = ((ρmatE E p b σ).map (ZMod.castHom (dvd_refl p) (HeckeAlg ⧸ 𝔪))).det := by
  classical
  have hp : p.Prime := Fact.out

  have hΔ : W.Δ ≠ 0 := by
    obtain ⟨C, hC⟩ := hW
    have hu : IsUnit (C • E).Δ := WeierstrassCurve.isUnit_Δ (W := C • E)
    rw [hC, WeierstrassCurve.map_Δ] at hu
    intro h0
    rw [h0, _root_.map_zero] at hu
    exact not_isUnit_zero hu
  have hn : M * p * W.Δ.natAbs ≠ 0 :=
    mul_ne_zero (mul_ne_zero hM.ne' hp.ne_zero) (Int.natAbs_ne_zero.mpr hΔ)
  have hnot : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ (M * p * W.Δ.natAbs).primeFactors →
      ¬ ℓ ∣ M * p * W.Δ.natAbs := fun ℓ hℓ hS hdvd =>
    hS (Nat.mem_primeFactors.mpr ⟨hℓ, hdvd, hn⟩)
  refine ⟨fun ℓ hℓ hS hdvd => hnot ℓ hℓ hS (hdvd.mul_right _), ?_⟩
  intro ℓ hℓ hS A hA σ hσ
  have hℓn := hnot ℓ hℓ hS
  have hℓM : ¬ ℓ ∣ M := fun h => hℓn ((h.mul_right _).mul_right _)
  have hℓp : ℓ ≠ p := by
    rintro rfl
    exact hℓn ((dvd_mul_left _ _).mul_right _)
  have hgood : W.IsGoodPrimeFor ℓ := by
    intro h
    exact hℓn ((Int.ofNat_dvd_left.mp h).mul_left _)

  have hmk : Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩)
      = ((W.apOfModel ℓ : ℤ) : HeckeAlg ⧸ 𝔪) := by
    have h : Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩)
        = Ideal.Quotient.mk 𝔪 (MvPolynomial.C (W.apOfModel ℓ : ℤ)) :=
      Ideal.Quotient.eq.mpr (hcong ℓ hℓ hgood hℓM hℓp)
    rw [h, eq_intCast MvPolynomial.C, map_intCast]

  obtain ⟨htr, hdet⟩ := hW.galoisTrace_det_frobenius p ℓ hp hℓ hℓp hgood A hA σ hσ
  have hmat : ρmatE E p b σ = LinearMap.toMatrix b b
      (galoisRepModuleEnd (S := ℚ) (K := AlgebraicClosure ℚ) E p σ) := rfl
  refine ⟨?_, ?_⟩
  · rw [← AddMonoidHom.map_trace, hmk, hmat, ← LinearMap.trace_eq_matrix_trace,
      ← galoisTrace_def, htr, map_intCast]
  · rw [map_natCast,
      show (ρmatE E p b σ).map (ZMod.castHom (dvd_refl p) (HeckeAlg ⧸ 𝔪))
          = (ZMod.castHom (dvd_refl p) (HeckeAlg ⧸ 𝔪)).mapMatrix (ρmatE E p b σ)
        from rfl,
      ← RingHom.map_det, hmat, LinearMap.det_toMatrix, hdet, map_natCast]

private theorem dense_aux (E : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime]
    {J : Type} [AddCommGroup J] [Module HeckeAlg J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg J]
    (𝔪 : Ideal HeckeAlg) [CharP (HeckeAlg ⧸ 𝔪) p]
    (hker : GaloisFactorsThroughFiniteLevel
      (galoisRepModuleEnd (S := ℚ) (K := AlgebraicClosure ℚ) E p))
    (hcont : GaloisFactorsThroughFiniteLevel
      (mTorsionGaloisRep (G := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J 𝔪))
    (b : Module.Basis (Fin 2) (ZMod p) (Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point p))
    (S : Finset ℕ) :
    FrobeniusPowerDense S
      (((RingHom.mapMatrix (ZMod.castHom (dvd_refl p) (HeckeAlg ⧸ 𝔪))).toMonoidHom.comp
            (ρmatE E p b)).ker ⊓
        fixingSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (heckeTorsion J 𝔪 : Set J)) := by
  classical
  obtain ⟨L, hLfin, hL⟩ := hker
  obtain ⟨L', hL'fin, hL'⟩ := hcont
  haveI : FiniteDimensional ℚ L := hLfin
  haveI : FiniteDimensional ℚ L' := hL'fin

  let Lc : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.normalClosure ℚ (↥(L ⊔ L')) (AlgebraicClosure ℚ)
  haveI : CharZero Lc := charZero_of_injective_algebraMap (algebraMap ℚ Lc).injective
  haveI : FiniteDimensional ℚ Lc :=
    normalClosure.is_finiteDimensional ℚ (↥(L ⊔ L')) (AlgebraicClosure ℚ)
  haveI : Normal ℚ Lc := normalClosure.normal ℚ (↥(L ⊔ L')) (AlgebraicClosure ℚ)
  haveI : NumberField Lc := NumberField.mk
  haveI : IsGalois ℚ Lc := IsGalois.mk
  have hLLc : L ≤ Lc := le_sup_left.trans (IntermediateField.le_normalClosure (L ⊔ L'))
  have hL'Lc : L' ≤ Lc := le_sup_right.trans (IntermediateField.le_normalClosure (L ⊔ L'))
  have hfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) Lc).ker →
        ∀ x : AlgebraicClosure ℚ, x ∈ Lc → σ x = x := by
    intro σ hσ x hx
    have h1 : AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) Lc σ = 1 :=
      MonoidHom.mem_ker.mp hσ
    have h := AlgEquiv.restrictNormalHom_apply Lc σ ⟨x, hx⟩
    exact h.symm.trans
      (congrArg (fun y : Lc => (y : AlgebraicClosure ℚ)) (DFunLike.congr_fun h1 ⟨x, hx⟩))
  refine FreyPackage.frobeniusPowerDense_inf_of_restrictionKer_le Lc _ _ ?_ ?_ S
  ·
    intro σ hσ
    have hσ1 : galoisRepModuleEnd (S := ℚ) (K := AlgebraicClosure ℚ) E p σ = 1 :=
      hL σ (fun x hx => hfix σ hσ x (hLLc hx))
    rw [MonoidHom.mem_ker]
    show (ZMod.castHom (dvd_refl p) (HeckeAlg ⧸ 𝔪)).mapMatrix (ρmatE E p b σ) = 1
    have hmat : ρmatE E p b σ = 1 := by
      show LinearMap.toMatrixAlgEquiv b
          (galoisRepModuleEnd (S := ℚ) (K := AlgebraicClosure ℚ) E p σ) = 1
      rw [hσ1, map_one]
    rw [hmat, map_one]
  ·
    intro σ hσ
    have hσ1 : mTorsionGaloisRep (G := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J 𝔪 σ = 1 :=
      hL' σ (fun x hx => hfix σ hσ x (hL'Lc hx))
    rw [mem_fixingSubgroup_iff]
    intro y hy
    have h := congrArg (fun f => ((f ⟨y, hy⟩ : heckeTorsion J 𝔪) : J)) hσ1
    simpa using h

private theorem main (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (W : WeierstrassCurve ℤ) (hW : W.IsIntegralModelOf E)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {J : Type} [AddCommGroup J] [Module HeckeAlg J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg J]
    {M : ℕ} (hM : 0 < M) (𝔪 : Ideal HeckeAlg) (hmax : 𝔪.IsMaximal) [CharP (HeckeAlg ⧸ 𝔪) p]
    (hirr : GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ E p)
    (hker : GaloisFactorsThroughFiniteLevel
      (galoisRepModuleEnd (S := ℚ) (K := AlgebraicClosure ℚ) E p))
    (hcong : FreyPackage.IdealGoodPrimeCurveCongruence p M W 𝔪)
    (hES : FrobeniusQuadratic (K := ℚ) (L := AlgebraicClosure ℚ) M p J)
    (hcont : GaloisFactorsThroughFiniteLevel
      (mTorsionGaloisRep (G := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J 𝔪))
    (hfin : Finite (heckeTorsion J 𝔪))
    (b : Module.Basis (Fin 2) (ZMod p) (Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point p)) :
    ∃ (n : ℕ) (e : heckeTorsion J 𝔪 ≃ₗ[HeckeAlg ⧸ 𝔪] (Fin n → (Fin 2 → HeckeAlg ⧸ 𝔪))),
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (w : heckeTorsion J 𝔪) (i : Fin n),
        e (mTorsionGaloisRep J 𝔪 σ w) i
          = ((ρmatE E p b σ).map (ZMod.castHom (dvd_refl p) (HeckeAlg ⧸ 𝔪))).mulVec (e w i) := by
  classical
  letI : Field (HeckeAlg ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  let ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ 𝔪) :=
    (RingHom.mapMatrix (ZMod.castHom (dvd_refl p) (HeckeAlg ⧸ 𝔪))).toMonoidHom.comp (ρmatE E p b)
  have h2 : (2 : HeckeAlg ⧸ 𝔪) ≠ 0 := by
    rw [show ((2 : HeckeAlg ⧸ 𝔪)) = ((2 : ℕ) : HeckeAlg ⧸ 𝔪) by norm_cast, Ne,
      CharP.cast_eq_zero_iff (HeckeAlg ⧸ 𝔪) p 2]
    exact fun hdvd => hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hdvd)
  have hp : ((p : ℕ) : HeckeAlg) ∈ 𝔪 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero (HeckeAlg ⧸ 𝔪) p
  obtain ⟨hS, hatt⟩ := trace_det_aux E W hW p hM 𝔪 hcong b
  have hdense := dense_aux E p 𝔪 hker hcont b (M * p * W.Δ.natAbs).primeFactors
  have hann := mTorsionGaloisRep_quadratic_of_frobeniusQuadratic_of_frobeniusPowerDense M p 𝔪 hp ρ hES hS
    hatt hdense
  haveI : Finite (heckeTorsion J 𝔪) := hfin
  haveI : Module.Finite (HeckeAlg ⧸ 𝔪) (heckeTorsion J 𝔪) := Module.Finite.of_finite
  have hspan := spanTop_aux E p hp2 𝔪 hmax hirr hker b
  obtain ⟨n, e, he⟩ := Representation.exists_blrDecomposition_of_spanTop_of_quadraticAnnihilation ρ
    (mTorsionGaloisRep (G := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J 𝔪) h2 hspan hann
  exact ⟨n, e, fun σ w i => he σ w i⟩

end M5A3RibbonBLRW

theorem solution
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (W : WeierstrassCurve ℤ) (hW : W.IsIntegralModelOf E)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {J : Type} [AddCommGroup J] [Module HeckeAlg J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg J]
    {M : ℕ} (hM : 0 < M) (𝔪 : Ideal HeckeAlg) (hmax : 𝔪.IsMaximal) [CharP (HeckeAlg ⧸ 𝔪) p]
    (hirr : GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ E p)
    (hker : GaloisFactorsThroughFiniteLevel
      (galoisRepModuleEnd (S := ℚ) (K := AlgebraicClosure ℚ) E p))
    (hcong : FreyPackage.IdealGoodPrimeCurveCongruence p M W 𝔪)
    (hES : FrobeniusQuadratic (K := ℚ) (L := AlgebraicClosure ℚ) M p J)
    (hcont : GaloisFactorsThroughFiniteLevel
      (mTorsionGaloisRep (G := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J 𝔪))
    (hfin : Finite (heckeTorsion J 𝔪))
    (b : Module.Basis (Fin 2) (ZMod p) (Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point p)) :
    ∃ (n : ℕ) (e : heckeTorsion J 𝔪 ≃ₗ[HeckeAlg ⧸ 𝔪] (Fin n → (Fin 2 → HeckeAlg ⧸ 𝔪))),
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (w : heckeTorsion J 𝔪) (i : Fin n),
        e (mTorsionGaloisRep J 𝔪 σ w) i
          = (((((LinearMap.toMatrixAlgEquiv b).toMulEquiv.toMonoidHom).comp
                (galoisRepModuleEnd (S := ℚ) (K := AlgebraicClosure ℚ) E p)) σ).map
              (ZMod.castHom (dvd_refl p) (HeckeAlg ⧸ 𝔪))).mulVec (e w i) :=
  M5A3RibbonBLRW.main E W hW p hp2 hM 𝔪 hmax hirr hker hcong hES hcont hfin b

end S_WeierstrassCurve_modRep_blrDecomposition_heckeTorsion_of_frobeniusQuadratic
end P2MW
export P2MW.S_WeierstrassCurve_modRep_blrDecomposition_heckeTorsion_of_frobeniusQuadratic (solution)
