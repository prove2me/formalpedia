-- Prove2me | solution 1 for WeierstrassCurve.exists_isGalois_goodModel_inertia_faithful_of_three_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/b0dcb01e-5070-5a1f-b1c3-5c8126dc417d

import Mathlib
import Theorems.Thm_WeierstrassCurve_exists_variableChange_eq_deuring_of_isUnit_three
import Theorems.Thm_WeierstrassCurve_exists_intermediateField_isGalois_card_torsion_eq_sq
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_isGalois_goodModel_inertia_faithful_of_three_ne_zero
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing Polynomial
open scoped Pointwise

noncomputable section

namespace P2MKcDeuringRoute

universe u v

variable {F : Type u} {Ω : Type v} [Field F] [Field Ω] [Algebra F Ω] [DecidableEq Ω]

section Three

variable (E : WeierstrassCurve F) [E.IsElliptic]

def psi2 : (E.baseChange Ω).toAffine.Point → Ω
  | .zero => 0
  | .some x y _ => 2 * y + (E.baseChange Ω).a₁ * x + (E.baseChange Ω).a₃

lemma psi2_some {x y : Ω} (h : (E.baseChange Ω).toAffine.Nonsingular x y) :
    psi2 E (.some x y h) = 2 * y + (E.baseChange Ω).a₁ * x + (E.baseChange Ω).a₃ := rfl

lemma psi2_ne_zero {x y : Ω} (h : (E.baseChange Ω).toAffine.Nonsingular x y)
    (h3 : (3 : ℕ) • Point.some x y h = 0) : psi2 E (.some x y h) ≠ 0 := by
  have h3' : Point.some x y h + Point.some x y h + Point.some x y h = 0 := by
    rw [← h3, show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul, two_nsmul]
  have h2P : Point.some x y h + Point.some x y h = -Point.some x y h := eq_neg_of_add_eq_zero_left h3'
  have hy : y ≠ (E.baseChange Ω).toAffine.negY x y := by
    intro hy
    have h0 : Point.some x y h + Point.some x y h = 0 := Point.add_self_of_Y_eq hy
    rw [h0] at h2P
    exact Point.some_ne_zero _ (neg_eq_zero.mp h2P.symm)
  rw [psi2_some]
  intro h0
  apply hy
  rw [Affine.negY]
  show y = -y - (E.baseChange Ω).a₁ * x - (E.baseChange Ω).a₃
  linear_combination h0

lemma psi2_map (φ : Ω →ₐ[F] Ω) (P : (E.baseChange Ω).toAffine.Point) :
    psi2 E (Point.map φ P) = φ (psi2 E P) := by
  rcases P with _ | ⟨x, y, h⟩
  · show psi2 E 0 = φ 0
    rw [map_zero]; rfl
  · rw [Point.map_some, psi2_some, psi2_some]
    have ha₁ : φ (E.baseChange Ω).a₁ = (E.baseChange Ω).a₁ := φ.commutes E.a₁
    have ha₃ : φ (E.baseChange Ω).a₃ = (E.baseChange Ω).a₃ := φ.commutes E.a₃
    rw [map_add, map_add, map_mul, map_mul, map_ofNat, ha₁, ha₃]

variable [IsAlgClosed Ω] (h3 : (3 : F) ≠ 0)

include h3 in
lemma three_ne_zero_Ω : (3 : Ω) ≠ 0 := by
  intro h; apply h3
  apply (algebraMap F Ω).injective
  rw [map_ofNat, _root_.map_zero, h]

include h3 in

lemma card_three_torsion : Nat.card {P : (E.baseChange Ω).toAffine.Point // (3 : ℕ) • P = 0} = 9 := by
  obtain ⟨e⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := Ω) E
    (n := 3) (three_ne_zero_Ω h3)
  have e2 : {P : (E.baseChange Ω).toAffine.Point // (3 : ℕ) • P = 0} ≃
      Submodule.torsionBy ℤ (E.baseChange Ω).toAffine.Point ((3 : ℕ) : ℤ) :=
    Equiv.subtypeEquivRight fun P => by
      rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
  rw [Nat.card_congr e2, ← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zmod]

include h3 in
lemma finite_three_torsion : Finite {P : (E.baseChange Ω).toAffine.Point // (3 : ℕ) • P = 0} :=
  Nat.finite_of_card_ne_zero (by rw [card_three_torsion E h3]; norm_num)

include h3 in

lemma exists_three_torsion : ∃ P : (E.baseChange Ω).toAffine.Point, (3 : ℕ) • P = 0 ∧ P ≠ 0 := by
  haveI := finite_three_torsion (Ω := Ω) E h3
  have h9 : 1 < Nat.card {P : (E.baseChange Ω).toAffine.Point // (3 : ℕ) • P = 0} := by
    rw [card_three_torsion E h3]; norm_num
  haveI := (Finite.one_lt_card_iff_nontrivial).mp h9
  obtain ⟨⟨P, hP⟩, hne⟩ := exists_ne
    (⟨0, by rw [smul_zero]⟩ : {P : (E.baseChange Ω).toAffine.Point // (3 : ℕ) • P = 0})
  exact ⟨P, hP, fun h => hne (Subtype.ext h)⟩

def cubeRoots : Set Ω :=
  {q | ∃ P : (E.baseChange Ω).toAffine.Point, (3 : ℕ) • P = 0 ∧ P ≠ 0 ∧ q ^ 3 = psi2 E P}

include h3 in
lemma finite_cubeRoots : (cubeRoots (Ω := Ω) E).Finite := by
  haveI := finite_three_torsion (Ω := Ω) E h3
  have h1 : cubeRoots (Ω := Ω) E ⊆
      ⋃ P : {P : (E.baseChange Ω).toAffine.Point // (3 : ℕ) • P = 0},
        {q : Ω | q ^ 3 = psi2 E P.1} := by
    rintro q ⟨P, hP, -, hq⟩
    exact Set.mem_iUnion.mpr ⟨⟨P, hP⟩, hq⟩
  refine Set.Finite.subset (Set.finite_iUnion fun P => ?_) h1
  have : {q : Ω | q ^ 3 = psi2 E P.1} = ((nthRoots 3 (psi2 E P.1)).toFinset : Set Ω) := by
    ext q
    rw [Set.mem_setOf_eq, Finset.mem_coe, Multiset.mem_toFinset, mem_nthRoots (by norm_num)]
  rw [this]
  exact Finset.finite_toSet _

lemma map_mem_cubeRoots (φ : Ω →ₐ[F] Ω) {q : Ω} (hq : q ∈ cubeRoots E) : φ q ∈ cubeRoots E := by
  obtain ⟨P, hP, hP0, hq⟩ := hq
  refine ⟨Point.map φ P, by rw [← map_nsmul, hP, map_zero], ?_, ?_⟩
  · intro h
    apply hP0
    apply Point.map_injective φ
    rw [h, map_zero]
  · rw [psi2_map, ← map_pow, hq]

end Three

section FieldS

variable (E : WeierstrassCurve F) [E.IsElliptic] [IsAlgClosed Ω] [Algebra.IsAlgebraic F Ω]
  (h3 : (3 : F) ≠ 0)

include h3 in

theorem exists_S : ∃ L : IntermediateField F Ω, IsGalois F L ∧
    (∀ σ : L ≃ₐ[F] L, (∀ P : (E.baseChange L).toAffine.Point, (3 : ℕ) • P = 0 →
      Point.map (σ : L →ₐ[F] L) P = P) → σ = 1) ∧
    (∀ {x y : Ω} (h : (E.baseChange Ω).toAffine.Nonsingular x y),
      (3 : ℕ) • Point.some x y h = 0 → x ∈ L ∧ y ∈ L) ∧
    FiniteDimensional F (L ⊔ IntermediateField.adjoin F (cubeRoots (Ω := Ω) E) : IntermediateField F Ω) ∧
    IsGalois F (L ⊔ IntermediateField.adjoin F (cubeRoots (Ω := Ω) E) : IntermediateField F Ω) := by
  have h3Ω : (3 : Ω) ≠ 0 := three_ne_zero_Ω h3
  obtain ⟨L, hLfd, hLgal, hLcard, hLfaith⟩ :=
    WeierstrassCurve.exists_intermediateField_isGalois_card_torsion_eq_sq (Ω := Ω) E (n := 3) h3
  haveI := hLfd; haveI := hLgal

  let ι : (E.baseChange L).toAffine.Point →+ (E.baseChange Ω).toAffine.Point :=
    Point.map (IntermediateField.val L)
  have hι : Function.Injective ι := Point.map_injective _
  let g : {P : (E.baseChange L).toAffine.Point // (3 : ℕ) • P = 0} →
      {P : (E.baseChange Ω).toAffine.Point // (3 : ℕ) • P = 0} :=
    fun P => ⟨ι P.1, by rw [← map_nsmul, P.2, map_zero]⟩
  have hg : Function.Injective g := fun P Q h => Subtype.ext (hι (congrArg Subtype.val h))
  haveI := finite_three_torsion (Ω := Ω) E h3
  have hgbij : Function.Bijective g :=
    hg.bijective_of_nat_card_le (by rw [card_three_torsion E h3, hLcard]; norm_num)
  have hcoords : ∀ {x y : Ω} (h : (E.baseChange Ω).toAffine.Nonsingular x y),
      (3 : ℕ) • Point.some x y h = 0 → x ∈ L ∧ y ∈ L := by
    intro x y h hP
    obtain ⟨⟨Q, hQ⟩, hQP⟩ := hgbij.2 ⟨Point.some x y h, hP⟩
    have hQP' : ι Q = Point.some x y h := congrArg Subtype.val hQP
    rcases Q with _ | ⟨x', y', h'⟩
    · exact absurd ((map_zero ι).symm.trans hQP') (Point.some_ne_zero _).symm
    · have := hQP'
      erw [Point.map_some] at this
      obtain ⟨hx, hy⟩ := Point.some.inj this
      exact ⟨hx ▸ x'.2, hy ▸ y'.2⟩

  have hsep3 : ∀ q ∈ cubeRoots (Ω := Ω) E, q ∈ separableClosure F Ω := by
    rintro q ⟨P, hP, hP0, hq⟩
    have hd : psi2 E P ∈ separableClosure F Ω ∧ psi2 E P ≠ 0 := by
      rcases P with _ | ⟨x, y, h⟩
      · exact absurd rfl hP0
      · obtain ⟨hx, hy⟩ := hcoords h hP
        haveI : Algebra.IsSeparable F L := IsGalois.to_isSeparable
        have hLsc : L ≤ separableClosure F Ω := le_separableClosure F Ω L
        refine ⟨?_, psi2_ne_zero E h hP⟩
        rw [psi2_some]
        exact add_mem (add_mem (mul_mem (by
          rw [show (2 : Ω) = algebraMap F Ω 2 from (map_ofNat _ 2).symm]
          exact IntermediateField.algebraMap_mem _ _) (hLsc hy))
          (mul_mem (IntermediateField.algebraMap_mem _ E.a₁) (hLsc hx)))
          (IntermediateField.algebraMap_mem _ E.a₃)
    obtain ⟨hdsc, hd0⟩ := hd
    let dS : separableClosure F Ω := ⟨psi2 E P, hdsc⟩
    let f : Polynomial (separableClosure F Ω) := X ^ 3 - Polynomial.C dS
    have hfmap : f.map (algebraMap (separableClosure F Ω) Ω) = X ^ 3 - Polynomial.C (psi2 E P) := by
      simp only [f, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]; rfl
    have hfsep : (f.map (algebraMap (separableClosure F Ω) Ω)).Separable := by
      rw [hfmap]; exact separable_X_pow_sub_C _ h3Ω hd0
    rw [mem_separableClosure_iff]
    have hf' : f.Separable := (Polynomial.separable_map _).mp hfsep
    have haeval : aeval q f = 0 := by
      rw [aeval_def, eval₂_eq_eval_map, hfmap, eval_sub, eval_pow, eval_X, eval_C, hq, sub_self]
    have hz : IsSeparable (separableClosure F Ω) q := hf'.of_dvd (minpoly.dvd _ q haeval)
    exact IsSeparable.of_algebra_isSeparable_of_isSeparable F hz

  haveI hfin : Finite (cubeRoots (Ω := Ω) E) := (finite_cubeRoots E h3).to_subtype
  have hCfd : FiniteDimensional F (IntermediateField.adjoin F (cubeRoots (Ω := Ω) E)) :=
    IntermediateField.finiteDimensional_adjoin fun x hx =>
      (Algebra.IsAlgebraic.isAlgebraic (R := F) x).isIntegral
  have hCsep : Algebra.IsSeparable F (IntermediateField.adjoin F (cubeRoots (Ω := Ω) E)) :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable F Ω).mpr fun x hx =>
      mem_separableClosure_iff.mp (hsep3 x hx)
  haveI : Normal F Ω :=
    normal_iff.mpr fun z => ⟨(Algebra.IsAlgebraic.isAlgebraic z).isIntegral, IsAlgClosed.splits _⟩
  have hCnormal : Normal F (IntermediateField.adjoin F (cubeRoots (Ω := Ω) E)) := by
    refine IntermediateField.normal_iff_forall_map_le.mpr fun σ => ?_
    rw [IntermediateField.adjoin_map]
    refine IntermediateField.adjoin.mono F _ _ ?_
    rintro _ ⟨z, hz, rfl⟩
    exact map_mem_cubeRoots E σ hz
  haveI := hCfd; haveI := hCsep; haveI := hCnormal
  haveI : IsGalois F (IntermediateField.adjoin F (cubeRoots (Ω := Ω) E)) := IsGalois.mk
  exact ⟨L, hLgal, hLfaith, hcoords, IntermediateField.finiteDimensional_sup _ _, inferInstance⟩

end FieldS

section Inertia

variable {M : Type*} [Field M] [Algebra F M] (A : ValuationSubring M)

lemma val_sub_lt_one_of_inertia {σ : M ≃ₐ[F] M} (hσ : σ ∈ A.decompositionSubgroup F)
    (hσI : (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F) (a : A) :
    A.valuation (σ a - a) < 1 := by
  have h1 : MulSemiringAction.toRingAut (A.decompositionSubgroup F) (ResidueField A) ⟨σ, hσ⟩ = 1 := hσI
  have hσa : σ a ∈ A := by
    have h := ValuationSubring.smul_mem_pointwise_smul σ (a : M) A a.2
    rwa [MulAction.mem_stabilizer_iff.mp hσ] at h
  have hres : residue A ⟨σ a, hσa⟩ = residue A a := by
    have : residue A ((⟨σ, hσ⟩ : A.decompositionSubgroup F) • a) = residue A a := by
      rw [IsLocalRing.ResidueField.residue_smul]
      show MulSemiringAction.toRingAut (A.decompositionSubgroup F) (ResidueField A) ⟨σ, hσ⟩
        (residue A a) = residue A a
      rw [h1]; rfl
    exact this
  have hmem : (⟨σ a, hσa⟩ : A) - a ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hres, sub_self]
  exact (A.valuation_lt_one_iff _).mp hmem

lemma smul_mem_of_decomposition {σ : M ≃ₐ[F] M} (hσ : σ ∈ A.decompositionSubgroup F) {a : M}
    (ha : a ∈ A) : σ a ∈ A := by
  have h := ValuationSubring.smul_mem_pointwise_smul σ a A ha
  rwa [MulAction.mem_stabilizer_iff.mp hσ] at h

lemma val_natCast_le (n : ℕ) : A.valuation (n : M) ≤ 1 := by
  rw [show (n : M) = ((n : A) : M) by simp]
  exact A.valuation_le_one _

lemma eq_one_of_cube_eq_one (h3 : IsUnit (3 : A)) {ζ : M} (hζA : A.valuation ζ ≤ 1) (hζ3 : ζ ^ 3 = 1)
    (hζ1 : A.valuation (ζ - 1) < 1) : ζ = 1 := by
  have hfac : (ζ - 1) * (ζ ^ 2 + ζ + 1) = 0 := by linear_combination hζ3
  rcases mul_eq_zero.mp hfac with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have h3v : A.valuation ((3 : A) : M) = 1 := (A.valuation_eq_one_iff _).mp h3
    have hv3 : A.valuation (3 : M) = 1 := h3v
    have hkey : (3 : M) = -((ζ - 1) * (ζ + 2)) := by linear_combination h
    have hv : A.valuation (3 : M) < 1 := by
      rw [hkey, Valuation.map_neg, Valuation.map_mul]
      have h2 : A.valuation (ζ + 2) ≤ 1 := by
        refine le_trans (Valuation.map_add _ _ _) (max_le hζA ?_)
        have := val_natCast_le A 2; simpa using this
      calc A.valuation (ζ - 1) * A.valuation (ζ + 2) ≤ A.valuation (ζ - 1) * 1 :=
            mul_le_mul_right h2 _
        _ = A.valuation (ζ - 1) := mul_one _
        _ < 1 := hζ1
    rw [hv3] at hv
    exact lt_irrefl _ hv

lemma eq_of_inertia_of_cube_eq (h3 : IsUnit (3 : A)) {σ : M ≃ₐ[F] M}
    (hσ : σ ∈ A.decompositionSubgroup F)
    (hσI : (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F) {x : M}
    (hx : A.valuation x = 1) (hcube : σ (x ^ 3) = x ^ 3) : σ x = x := by
  have hx0 : x ≠ 0 := by
    intro h; rw [h, Valuation.map_zero] at hx; exact zero_ne_one hx
  have hxA : x ∈ A := (A.valuation_le_one_iff x).mp hx.le
  have hσxA : σ x ∈ A := smul_mem_of_decomposition A hσ hxA
  set ζ : M := σ x / x with hζ
  have hζx : σ x = ζ * x := by rw [hζ, div_mul_cancel₀ _ hx0]
  have hζ3 : ζ ^ 3 = 1 := by
    rw [hζ, div_pow, ← map_pow, hcube, div_self (pow_ne_zero 3 hx0)]
  have hζA : A.valuation ζ ≤ 1 := by
    rw [hζ, map_div₀, hx, div_one]; exact (A.valuation_le_one_iff _).mpr hσxA
  have hζ1 : A.valuation (ζ - 1) < 1 := by
    have h := val_sub_lt_one_of_inertia A hσ hσI ⟨x, hxA⟩
    simp only at h
    have : ζ - 1 = (σ x - x) / x := by rw [hζ]; field_simp
    rw [this, map_div₀, hx, div_one]; exact h
  rw [hζx, eq_one_of_cube_eq_one A h3 hζA hζ3 hζ1, one_mul]

lemma val_eq_one_of_pow {x : M} {n : ℕ} (hn : n ≠ 0) (h : A.valuation (x ^ n) = 1) :
    A.valuation x = 1 := by
  rw [Valuation.map_pow] at h
  rcases lt_trichotomy (A.valuation x) 1 with h1 | h1 | h1
  · exact absurd h (ne_of_lt (pow_lt_one₀ zero_le' h1 hn))
  · exact h1
  · exact absurd h (ne_of_gt (one_lt_pow₀ h1 hn))

end Inertia

section Model

variable {E : WeierstrassCurve F} [E.IsElliptic] [IsAlgClosed Ω] [Algebra.IsAlgebraic F Ω]
  (h3 : (3 : F) ≠ 0) (L : IntermediateField F Ω) [IsGalois F L]
  (hLfaith : ∀ σ : L ≃ₐ[F] L, (∀ P : (E.baseChange L).toAffine.Point, (3 : ℕ) • P = 0 →
      Point.map (σ : L →ₐ[F] L) P = P) → σ = 1)
  (hcoords : ∀ {x y : Ω} (h : (E.baseChange Ω).toAffine.Nonsingular x y),
      (3 : ℕ) • Point.some x y h = 0 → x ∈ L ∧ y ∈ L)
  (M : IntermediateField F Ω)
  (hM : L ⊔ IntermediateField.adjoin F (cubeRoots (Ω := Ω) E) ≤ M)

include h3 hLfaith hcoords hM in
set_option maxHeartbeats 6400000 in

theorem model_and_faithful (A : ValuationSubring M) (h3A : IsUnit (3 : A))
    (hjA : algebraMap F M E.j ∈ A) :
    ∃ (W : WeierstrassCurve A) (κ : VariableChange M),
      κ • E.baseChange M = W.map A.subtype ∧ IsUnit W.Δ ∧
      ∀ (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F),
        (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
        (∀ P : (E.baseChange M).toAffine.Point, 3 • P = 0 → Point.map (σ : M →ₐ[F] M) P = P) →
        (∃ g : VariableChange A, g.map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹ ∧
            g.map (residue A) = 1) →
        ∀ x : M, (x : Ω) ∈ (L ⊔ IntermediateField.adjoin F (cubeRoots (Ω := Ω) E) :
          IntermediateField F Ω) → σ x = x := by
  haveI hEM : (E.baseChange M).IsElliptic := instIsEllipticMap E (algebraMap F M)
  have hLM : L ≤ M := le_sup_left.trans hM
  have hCM : cubeRoots (Ω := Ω) E ⊆ (M : Set Ω) := fun q hq =>
    hM (le_sup_right (b := IntermediateField.adjoin F (cubeRoots (Ω := Ω) E))
      (IntermediateField.subset_adjoin F _ hq))
  have h3M : (3 : M) ≠ 0 := by
    intro h; apply three_ne_zero_Ω (Ω := Ω) h3
    rw [← map_ofNat (algebraMap M Ω) 3, h, map_zero]

  have hval : Function.Injective (IntermediateField.val M) := (IntermediateField.val M).injective
  have hlift : ∀ {x y : Ω} (h : (E.baseChange Ω).toAffine.Nonsingular x y),
      (3 : ℕ) • Point.some x y h = 0 →
      ∃ (hx : x ∈ M) (hy : y ∈ M) (h' : (E.baseChange M).toAffine.Nonsingular ⟨x, hx⟩ ⟨y, hy⟩),
        (3 : ℕ) • Point.some _ _ h' = 0 := by
    intro x y h hP
    obtain ⟨hxL, hyL⟩ := hcoords h hP
    have hx : x ∈ M := hLM hxL
    have hy : y ∈ M := hLM hyL
    have h' : (E.baseChange M).toAffine.Nonsingular ⟨x, hx⟩ ⟨y, hy⟩ :=
      (Affine.baseChange_nonsingular E (f := IntermediateField.val M) hval ⟨x, hx⟩ ⟨y, hy⟩).mp h
    refine ⟨hx, hy, h', ?_⟩
    apply Point.map_injective (IntermediateField.val M)
    rw [map_nsmul, map_zero, Point.map_some]
    exact hP

  have ha₁ : ((E.baseChange M).a₁ : Ω) = (E.baseChange Ω).a₁ := rfl
  have ha₂ : ((E.baseChange M).a₂ : Ω) = (E.baseChange Ω).a₂ := rfl
  have ha₃ : ((E.baseChange M).a₃ : Ω) = (E.baseChange Ω).a₃ := rfl
  have ha₄ : ((E.baseChange M).a₄ : Ω) = (E.baseChange Ω).a₄ := rfl

  obtain ⟨P₀, hP₀, hP₀0⟩ := exists_three_torsion (Ω := Ω) E h3
  rcases P₀ with _ | ⟨x₀, y₀, h₀⟩
  · exact absurd rfl hP₀0
  obtain ⟨hx₀, hy₀, h₀', hP₀M⟩ := hlift h₀ hP₀
  obtain ⟨q₀, hq₀⟩ := IsAlgClosed.exists_pow_nat_eq (psi2 E (.some x₀ y₀ h₀)) (n := 3) (by norm_num)
  have hq₀C : q₀ ∈ cubeRoots (Ω := Ω) E := ⟨_, hP₀, hP₀0, hq₀⟩
  set c : M := ⟨q₀, hCM hq₀C⟩ with hc_def
  have hc : c ^ 3 = 2 * (⟨y₀, hy₀⟩ : M) + (E.baseChange M).a₁ * ⟨x₀, hx₀⟩ + (E.baseChange M).a₃ :=
    Subtype.ext hq₀
  have hjM : (E.baseChange M).j ∈ A := by
    have : (E.baseChange M).j = algebraMap F M E.j := E.map_j (algebraMap F M)
    rw [this]; exact hjA
  obtain ⟨α, κ, hΔ, hκu, hκr, hκs, hκt, hκE⟩ :=
    WeierstrassCurve.exists_variableChange_eq_deuring_of_isUnit_three A h3A (E.baseChange M) hjM h₀'
      hP₀M hc
  refine ⟨⟨α, 0, 1, 0, 0⟩, κ, hκE, hΔ, ?_⟩

  intro σ hσ hσI hfix hg x hx

  have hfixc : ∀ {x y : Ω} (h : (E.baseChange Ω).toAffine.Nonsingular x y),
      (3 : ℕ) • Point.some x y h = 0 → ∀ (hx : x ∈ M) (hy : y ∈ M),
      σ ⟨x, hx⟩ = ⟨x, hx⟩ ∧ σ ⟨y, hy⟩ = ⟨y, hy⟩ := by
    intro x y h hP hx hy
    obtain ⟨hx', hy', h', hP'⟩ := hlift h hP
    have := hfix _ hP'
    rw [Point.map_some] at this
    exact Point.some.inj this
  obtain ⟨hσx₀, hσy₀⟩ := hfixc h₀ hP₀ hx₀ hy₀
  have hd0 : (2 * (⟨y₀, hy₀⟩ : M) + (E.baseChange M).a₁ * ⟨x₀, hx₀⟩ + (E.baseChange M).a₃) ≠ 0 := by
    rw [← hc]
    intro h
    apply psi2_ne_zero E h₀ hP₀
    rw [← hq₀]
    have : c = 0 := pow_eq_zero_iff (n := 3) (by norm_num) |>.mp h
    have hq : q₀ = 0 := congrArg Subtype.val this
    rw [hq]; ring
  have hc0 : c ≠ 0 := by intro h; apply hd0; rw [← hc, h]; ring
  have hσa₁ : σ (E.baseChange M).a₁ = (E.baseChange M).a₁ := σ.commutes E.a₁
  have hσa₂ : σ (E.baseChange M).a₂ = (E.baseChange M).a₂ := σ.commutes E.a₂
  have hσa₃ : σ (E.baseChange M).a₃ = (E.baseChange M).a₃ := σ.commutes E.a₃
  have hσa₄ : σ (E.baseChange M).a₄ = (E.baseChange M).a₄ := σ.commutes E.a₄
  have hσc3 : σ (c ^ 3) = c ^ 3 := by
    rw [hc, map_add, map_add, map_mul, map_mul, map_ofNat, hσa₁, hσa₃, hσx₀, hσy₀]

  have hσc : σ c = c := by
    obtain ⟨g, hgM, hg1⟩ := hg
    have hσc0 : σ c ≠ 0 := fun h => hc0 (by rw [← map_zero σ] at h; exact σ.injective h)
    let ε : Mˣ := Units.mk0 (σ c) hσc0 * (Units.mk0 c hc0)⁻¹
    have hε : (ε : M) = σ c / c := by simp [ε, div_eq_mul_inv]
    have hκσ : κ.map (σ : M →+* M) = ⟨ε, 0, 0, 0⟩ * κ := by
      apply VariableChange.ext
      · apply Units.ext
        simp only [VariableChange.map, VariableChange.mul_def, Units.coe_map, Units.val_mul, hε]
        show σ (κ.u : M) = σ c / c * κ.u
        rw [hκu, div_mul_cancel₀ _ hc0]
      · simp only [VariableChange.map, VariableChange.mul_def]
        show σ κ.r = 0 * (κ.u : M) ^ 2 + κ.r
        rw [hκr, hσx₀]; ring
      · simp only [VariableChange.map, VariableChange.mul_def]
        show σ κ.s = (κ.u : M) * 0 + κ.s
        rw [hκs, map_div₀]
        simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, hσa₁, hσa₂, hσa₃, hσa₄, hσx₀, hσy₀]
        ring
      · simp only [VariableChange.map, VariableChange.mul_def]
        show σ κ.t = 0 * (κ.u : M) ^ 3 + 0 * κ.s * (κ.u : M) ^ 2 + κ.t
        rw [hκt, hσy₀]; ring
    have hgu : ((g.u : A) : M) = c / σ c := by
      have hgM' := hgM
      rw [hκσ, mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul] at hgM'
      have hu := congrArg (fun C : VariableChange M => (C.u : M)) hgM'
      simp only [VariableChange.map, VariableChange.inv_def, Units.coe_map, Units.val_inv_eq_inv_val,
        MonoidHom.coe_coe] at hu
      rw [hε, inv_div] at hu
      exact hu
    have hgu1 : residue A (g.u : A) = 1 := by
      have := congrArg (fun C : VariableChange (ResidueField A) => (C.u : ResidueField A)) hg1
      simp [VariableChange.map] at this
      exact this
    have hmem : (g.u : A) - 1 ∈ IsLocalRing.maximalIdeal A := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hgu1, map_one, sub_self]
    have hζ1 : A.valuation (c / σ c - 1) < 1 := by
      have := (A.valuation_lt_one_iff _).mp hmem
      rwa [show (((g.u : A) - 1 : A) : M) = c / σ c - 1 by rw [← hgu]; rfl] at this
    have hζA : A.valuation (c / σ c) ≤ 1 := by rw [← hgu]; exact A.valuation_le_one _
    have hζ3 : (c / σ c) ^ 3 = 1 := by rw [div_pow, ← map_pow, hσc3, div_self (pow_ne_zero 3 hc0)]
    have h1 : c / σ c = 1 := eq_one_of_cube_eq_one A h3A hζA hζ3 hζ1
    rw [div_eq_one_iff_eq hσc0] at h1
    exact h1.symm

  have hLfix : ∀ z : M, (z : Ω) ∈ L → σ z = z := by
    intro z hz
    let ι : L →ₐ[F] M := IntermediateField.inclusion hLM
    letI : Algebra L M := (ι : L →+* M).toAlgebra
    haveI : IsScalarTower F L M := IsScalarTower.of_algebraMap_eq (fun w => (ι.commutes w).symm)
    let τ : L ≃ₐ[F] L := σ.restrictNormal L
    have hτ : ∀ w : L, ι (τ w) = σ (ι w) := fun w => AlgEquiv.restrictNormal_commutes σ L w
    have hτ1 : τ = 1 := by
      apply hLfaith
      intro P hP
      apply Point.map_injective ι
      have h1 : Point.map ι (Point.map (τ : L →ₐ[F] L) P) = Point.map (σ : M →ₐ[F] M) (Point.map ι P) := by
        rcases P with _ | ⟨x, y, hxy⟩
        · rfl
        · simp only [Point.map_some]
          congr 1 <;> exact hτ _
      rw [h1]
      exact hfix _ (by rw [← map_nsmul, hP, map_zero])
    have h2 := hτ ⟨z, hz⟩
    rw [hτ1, AlgEquiv.one_apply] at h2
    have h3' : ι ⟨z, hz⟩ = z := Subtype.ext rfl
    rw [h3'] at h2
    exact h2.symm

  have hΔE0 : (E.baseChange M).Δ ≠ 0 := (E.baseChange M).isUnit_Δ.ne_zero
  have hΔκ : A.valuation (((κ.u⁻¹ : Mˣ) : M) ^ 12 * (E.baseChange M).Δ) = 1 := by
    have h1 := congrArg WeierstrassCurve.Δ hκE
    rw [variableChange_Δ, map_Δ] at h1
    rw [h1]
    have h2 : A.valuation ((((⟨α, 0, 1, 0, 0⟩ : WeierstrassCurve A).Δ : A) : M)) = 1 :=
      (A.valuation_eq_one_iff _).mp hΔ
    exact h2
  have hCfix : ∀ z : M, (z : Ω) ∈ cubeRoots (Ω := Ω) E → σ z = z := by
    rintro z ⟨Q, hQ, hQ0, hz3⟩
    rcases Q with _ | ⟨x₁, y₁, h₁⟩
    · exact absurd rfl hQ0
    obtain ⟨hx₁, hy₁, h₁', hQM⟩ := hlift h₁ hQ
    have hzc : z ^ 3 = 2 * (⟨y₁, hy₁⟩ : M) + (E.baseChange M).a₁ * ⟨x₁, hx₁⟩ + (E.baseChange M).a₃ :=
      Subtype.ext hz3

    obtain ⟨α', κ', hΔ', hκ'u, -, -, -, hκ'E⟩ :=
      WeierstrassCurve.exists_variableChange_eq_deuring_of_isUnit_three A h3A (E.baseChange M) hjM h₁'
        hQM hzc
    have hz0 : z ≠ 0 := by rw [← hκ'u]; exact κ'.u.ne_zero

    set μ : M := z / c with hμ
    have hΔκ' : A.valuation (((κ'.u⁻¹ : Mˣ) : M) ^ 12 * (E.baseChange M).Δ) = 1 := by
      have h1 := congrArg WeierstrassCurve.Δ hκ'E
      rw [variableChange_Δ, map_Δ] at h1
      rw [h1]
      exact (A.valuation_eq_one_iff _).mp hΔ'
    have hvμ : A.valuation μ = 1 := by
      apply val_eq_one_of_pow A (n := 12) (by norm_num)
      have hquot : μ ^ 12 = (((κ.u⁻¹ : Mˣ) : M) ^ 12 * (E.baseChange M).Δ) /
          (((κ'.u⁻¹ : Mˣ) : M) ^ 12 * (E.baseChange M).Δ) := by
        rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, hκu, hκ'u, hμ]
        field_simp
      rw [hquot, map_div₀, hΔκ, hΔκ', div_one]

    obtain ⟨hσx₁, hσy₁⟩ := hfixc h₁ hQ hx₁ hy₁
    have hσz3 : σ (z ^ 3) = z ^ 3 := by
      rw [hzc, map_add, map_add, map_mul, map_mul, map_ofNat, hσa₁, hσa₃, hσx₁, hσy₁]
    have hσμ3 : σ (μ ^ 3) = μ ^ 3 := by
      rw [hμ, div_pow, map_div₀, hσz3, hσc3]
    have hσμ : σ μ = μ := eq_of_inertia_of_cube_eq A h3A hσ hσI hvμ hσμ3
    have hzμ : z = μ * c := by rw [hμ, div_mul_cancel₀ _ hc0]
    rw [hzμ, map_mul, hσμ, hσc]

  let Fix : IntermediateField F M :=
    (AlgHom.equalizer (σ : M →ₐ[F] M) (AlgHom.id F M)).toIntermediateField (by
      intro w hw
      rw [AlgHom.mem_equalizer] at hw ⊢
      rw [map_inv₀, hw]; rfl)
  have hmemFix : ∀ w : M, w ∈ Fix ↔ σ w = w := fun w => by
    show w ∈ AlgHom.equalizer _ _ ↔ _
    rw [AlgHom.mem_equalizer]; rfl
  have hle : (L ⊔ IntermediateField.adjoin F (cubeRoots (Ω := Ω) E) : IntermediateField F Ω) ≤
      IntermediateField.lift Fix := by
    refine sup_le ?_ ?_
    · intro w hw
      exact (IntermediateField.mem_lift (⟨w, hLM hw⟩ : M)).mpr ((hmemFix _).mpr (hLfix ⟨w, hLM hw⟩ hw))
    · apply IntermediateField.adjoin_le_iff.mpr
      intro w hw
      exact (IntermediateField.mem_lift (⟨w, hCM hw⟩ : M)).mpr ((hmemFix _).mpr (hCfix ⟨w, hCM hw⟩ hw))
  have hxFix : x ∈ Fix := (IntermediateField.mem_lift x).mp (hle hx)
  exact (hmemFix x).mp hxFix

end Model

theorem main [IsAlgClosed Ω] [Algebra.IsAlgebraic F Ω]
    (E : WeierstrassCurve F) [E.IsElliptic] (h3 : (3 : F) ≠ 0) :
    ∃ S : IntermediateField F Ω, FiniteDimensional F S ∧ IsGalois F S ∧
      ∀ (M : IntermediateField F Ω), S ≤ M →
      ∀ (A : ValuationSubring M), IsUnit (3 : A) → algebraMap F M E.j ∈ A →
      ∃ (W : WeierstrassCurve A) (κ : VariableChange M),
        κ • E.baseChange M = W.map A.subtype ∧ IsUnit W.Δ ∧
        ∀ (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F),
          (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
          (∀ P : (E.baseChange M).toAffine.Point, 3 • P = 0 →
              Point.map (σ : M →ₐ[F] M) P = P) →
          (∃ g : VariableChange A, g.map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹ ∧
              g.map (residue A) = 1) →
          ∀ x : M, (x : Ω) ∈ S → σ x = x := by
  obtain ⟨L, hLgal, hLfaith, hcoords, hfd, hgal⟩ := exists_S (Ω := Ω) E h3
  haveI := hLgal
  exact ⟨L ⊔ IntermediateField.adjoin F (cubeRoots (Ω := Ω) E), hfd, hgal,
    fun M hM A h3A hjA => model_and_faithful h3 L hLfaith hcoords M hM A h3A hjA⟩

end P2MKcDeuringRoute

universe u v in
theorem solution
    {F : Type u} {Ω : Type v} [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic F Ω] [DecidableEq Ω]
    (E : WeierstrassCurve F) [E.IsElliptic] (h3 : (3 : F) ≠ 0) :
    ∃ S : IntermediateField F Ω, FiniteDimensional F S ∧ IsGalois F S ∧
      ∀ (M : IntermediateField F Ω), S ≤ M →
      ∀ (A : ValuationSubring M), IsUnit (3 : A) → algebraMap F M E.j ∈ A →
      ∃ (W : WeierstrassCurve A) (κ : VariableChange M),
        κ • E.baseChange M = W.map A.subtype ∧ IsUnit W.Δ ∧
        ∀ (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F),
          (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
          (∀ P : (E.baseChange M).toAffine.Point, 3 • P = 0 →
              Point.map (σ : M →ₐ[F] M) P = P) →
          (∃ g : VariableChange A, g.map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹ ∧
              g.map (residue A) = 1) →
          ∀ x : M, (x : Ω) ∈ S → σ x = x :=
  P2MKcDeuringRoute.main E h3

end
end S_WeierstrassCurve_exists_isGalois_goodModel_inertia_faithful_of_three_ne_zero
end P2MW
export P2MW.S_WeierstrassCurve_exists_isGalois_goodModel_inertia_faithful_of_three_ne_zero (solution)
