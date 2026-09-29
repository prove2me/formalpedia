-- Prove2me | solution 1 for WeierstrassCurve.exists_subfield_model_frobenius_eq_smul_rationalEndSubring_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/30976f58-11f8-5082-9f82-26a0c3c1a563

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq
import Theorems.Thm_WeierstrassCurve_rationalEndSubring_baseChange_eq_of_frobenius_eq_smul
import Theorems.Thm_WeierstrassCurve_exists_iterate_frobenius_eq_smul_of_forall_nsmul_char_eq_zero
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_subfield_model_frobenius_eq_smul_rationalEndSubring_equiv
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.frobPoint_zero WeierstrassCurve.frobCardHom_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option linter.unusedSectionVars false

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_exists_subfield_model_frobenius_eq_smul_rationalEndSubring_equiv.WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map map_j exists_variableChange_of_j_eq ofJ_j ofJ Affine.Point.zero_def toAffine Affine.Point instIsEllipticMap Affine.Point.map Affine.Point.map_some baseChange j rationalEndSubring Affine.Point.vcFun Affine.Point.vcInvFun Affine.Point.vcFun_zero Affine.Point.vcInvFun_zero Affine.Point.variableChangeEquiv exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq rationalEndSubring_baseChange_eq_of_frobenius_eq_smul exists_iterate_frobenius_eq_smul_of_forall_nsmul_char_eq_zero Affine.Point.vcInvFun_add"
namespace ADGlue
p2m_open "WeierstrassCurve"

def fixedSubfield {k : Type*} [Field k] (τ : k →+* k) : Subfield k where
  carrier := {x | τ x = x}
  mul_mem' {a b} ha hb := by simp only [Set.mem_setOf_eq] at *; rw [map_mul, ha, hb]
  one_mem' := by simp
  add_mem' {a b} ha hb := by simp only [Set.mem_setOf_eq] at *; rw [map_add, ha, hb]
  zero_mem' := by simp
  neg_mem' {a} ha := by simp only [Set.mem_setOf_eq] at *; rw [map_neg, ha]
  inv_mem' a ha := by simp only [Set.mem_setOf_eq] at *; rw [map_inv₀, ha]

theorem mem_fixedSubfield {k : Type*} [Field k] (τ : k →+* k) (x : k) : x ∈ fixedSubfield τ ↔ τ x = x := Iff.rfl

theorem exists_fintype_card_fixedSubfield {k : Type*} [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (m : ℕ) (hm : 0 < m) :
    ∃ inst : Fintype ↥(fixedSubfield (iterateFrobenius k p m)),
      @Fintype.card ↥(fixedSubfield (iterateFrobenius k p m)) inst = p ^ m := by
  classical
  have hN1 : 1 < p ^ m := Nat.one_lt_pow hm.ne' (Fact.out : p.Prime).one_lt
  set P : Polynomial k := Polynomial.X ^ (p ^ m) - Polynomial.X with hP
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero k hN1
  have hmem : ∀ x : k, x ∈ fixedSubfield (iterateFrobenius k p m) ↔ x ∈ P.rootSet k := by
    intro x
    rw [mem_fixedSubfield, iterateFrobenius_def, Polynomial.mem_rootSet_of_ne hP0]
    simp [hP, sub_eq_zero, eq_comm]
  let e : ↥(fixedSubfield (iterateFrobenius k p m)) ≃ ↥(P.rootSet k) := Equiv.subtypeEquivRight hmem
  letI : Fintype ↥(fixedSubfield (iterateFrobenius k p m)) := Fintype.ofEquiv _ e.symm
  refine ⟨inferInstance, ?_⟩
  rw [Fintype.card_congr e, Polynomial.card_rootSet_eq_natDegree (galois_poly_separable p (p ^ m) (dvd_pow_self p hm.ne'))
    (IsAlgClosed.splits _), FiniteField.X_pow_card_sub_X_natDegree_eq k hN1]

theorem isAlgebraic_subfield {k : Type*} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    [Algebra.IsAlgebraic (ZMod p) k] (K : Subfield k) : Algebra.IsAlgebraic K k := by
  haveI : CharP K p := (Algebra.charP_iff K k p).mpr inferInstance
  refine ⟨fun x => ?_⟩
  obtain ⟨P, hP0, hPx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := ZMod p) x
  let f : ZMod p →+* K := ZMod.castHom (dvd_refl p) K
  refine ⟨P.map f, (Polynomial.map_ne_zero_iff f.injective).mpr hP0, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_map,
    Subsingleton.elim ((algebraMap (↥K) k).comp f) (algebraMap (ZMod p) k)]
  exact hPx

theorem map_eq_of_pow {F : Type*} [Field F] {k : Type*} [Field k] [DecidableEq k] [Algebra F k]
    (W : WeierstrassCurve F) (σ τ : k →ₐ[F] k) (hστ : ∀ x : k, σ x = τ x) (P : (W⁄k).Point) :
    WeierstrassCurve.Affine.Point.map (W' := W) σ P = WeierstrassCurve.Affine.Point.map (W' := W) τ P := by
  have : σ = τ := AlgHom.ext hστ
  subst this; rfl

theorem iterate_map {F : Type*} [Field F] {k : Type*} [Field k] [DecidableEq k] [Algebra F k]
    (W : WeierstrassCurve F) (σ : k →ₐ[F] k) (n : ℕ) (P : (W⁄k).Point) :
    (WeierstrassCurve.Affine.Point.map (W' := W) σ)^[n] P = WeierstrassCurve.Affine.Point.map (W' := W) (σ ^ n) P := by
  induction n generalizing P with
  | zero =>
    rw [Function.iterate_zero, id, pow_zero]
    rcases P with _ | ⟨x, y, h⟩
    · rw [← WeierstrassCurve.Affine.Point.zero_def, _root_.map_zero]
    · rw [WeierstrassCurve.Affine.Point.map_some]; rfl
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp_apply, ih, pow_succ']
    rcases P with _ | ⟨x, y, h⟩
    · rw [← WeierstrassCurve.Affine.Point.zero_def, _root_.map_zero, _root_.map_zero, _root_.map_zero]
    · simp only [WeierstrassCurve.Affine.Point.map_some, AlgHom.mul_apply]

theorem pow_pow_eq_self_of_pow_eq_self {k : Type*} [Monoid k] (x : k) (q : ℕ) (hx : x ^ q = x) (n : ℕ) : x ^ q ^ n = x := by
  induction n with
  | zero => simp
  | succ m ih => rw [pow_succ, pow_mul, ih, hx]

theorem iterate_pow_eq {k : Type*} [Monoid k] (q n : ℕ) (x : k) : (fun y : k => y ^ q)^[n] x = x ^ q ^ n := by
  induction n generalizing x with
  | zero => simp
  | succ m ih => rw [Function.iterate_succ, Function.comp_apply, ih, pow_succ', pow_mul]

theorem main {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k]
    (p : ℕ) [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k] [Algebra.IsAlgebraic (ZMod p) k]
    (X : WeierstrassCurve k) [X.IsElliptic]
    (hss : ∀ P : X.toAffine.Point, p • P = 0 → P = 0) :
    ∃ (K : Subfield k) (_ : Fintype K) (W : WeierstrassCurve K) (_ : W.IsElliptic)
      (σ : k →ₐ[K] k) (a : ℤ),
      (∀ x : k, σ x = x ^ Fintype.card K) ∧
      (∀ P : (W⁄k).Point, WeierstrassCurve.Affine.Point.map (W' := W) σ P = a • P) ∧
      Nonempty (↥(WeierstrassCurve.rationalEndSubring k X) ≃+* ↥(WeierstrassCurve.rationalEndSubring k W)) := by
  classical

  obtain ⟨j, hjX⟩ : ∃ j : k, X.j = j := ⟨_, rfl⟩

  let K₀ : IntermediateField (ZMod p) k := IntermediateField.adjoin (ZMod p) {j}
  haveI : FiniteDimensional (ZMod p) K₀ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic (R := ZMod p) j).isIntegral
  haveI : Finite K₀ := Module.finite_of_finite (ZMod p)
  letI : Fintype K₀ := Fintype.ofFinite K₀
  haveI : CharP K₀ p := (Algebra.charP_iff K₀ k p).mpr inferInstance
  haveI : Algebra.IsAlgebraic K₀ k := isAlgebraic_subfield p K₀.toSubfield

  let j₀ : K₀ := ⟨j, IntermediateField.mem_adjoin_simple_self (ZMod p) j⟩
  let W₀ : WeierstrassCurve K₀ := WeierstrassCurve.ofJ j₀
  haveI hW₀ : W₀.IsElliptic := by change (WeierstrassCurve.ofJ j₀).IsElliptic; infer_instance
  haveI : (W₀.baseChange k).IsElliptic := WeierstrassCurve.instIsEllipticMap W₀ (algebraMap K₀ k)
  have hj : (W₀.baseChange k).j = X.j := by
    change (W₀.map (algebraMap K₀ k)).j = X.j
    rw [WeierstrassCurve.map_j, WeierstrassCurve.ofJ_j, hjX]; rfl
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq (W₀.baseChange k) X hj
  subst hC
  obtain ⟨φ, -⟩ := WeierstrassCurve.exists_ringEquiv_rationalEndSubring_apply_eq_of_variableChange_smul_eq
    (W₀.baseChange k) (C • W₀.baseChange k) C rfl

  obtain ⟨d, -, hcard⟩ := FiniteField.card K₀ p
  let σ₀ : k →ₐ[K₀] k :=
    { iterateFrobenius k p d with
      commutes' := fun x => by
        change (algebraMap K₀ k x) ^ p ^ (d : ℕ) = algebraMap K₀ k x
        rw [← map_pow, ← hcard, FiniteField.pow_card] }
  have hσ₀ : ∀ x : k, σ₀ x = x ^ Fintype.card K₀ := fun x => by
    change x ^ p ^ (d : ℕ) = _; rw [hcard]
  have h₀ : ∀ P : (W₀⁄k).Point, p • P = 0 → P = 0 := by
    intro P hP

    let ψ : (W₀⁄k).Point →+ (C • W₀.baseChange k).toAffine.Point :=
      { toFun := WeierstrassCurve.Affine.Point.vcInvFun C (W₀.baseChange k)
        map_zero' := WeierstrassCurve.Affine.Point.vcInvFun_zero
        map_add' := WeierstrassCurve.Affine.Point.vcInvFun_add C (W₀.baseChange k) }
    have hQ : p • ψ P = 0 := by rw [← map_nsmul, hP, _root_.map_zero]
    have hQ0 := hss (ψ P) hQ
    have h1 := (WeierstrassCurve.Affine.Point.variableChangeEquiv C (W₀.baseChange k).toAffine).apply_symm_apply P
    change WeierstrassCurve.Affine.Point.vcFun C (W₀.baseChange k) (ψ P) = P at h1
    rw [hQ0, WeierstrassCurve.Affine.Point.vcFun_zero] at h1
    exact h1.symm

  obtain ⟨n, hn, a, hiter⟩ := WeierstrassCurve.exists_iterate_frobenius_eq_smul_of_forall_nsmul_char_eq_zero
    k p W₀ σ₀ hσ₀ h₀

  have hdn : 0 < (d : ℕ) * n := Nat.mul_pos d.pos hn
  obtain ⟨instK, hcardK⟩ := exists_fintype_card_fixedSubfield (k := k) p ((d : ℕ) * n) hdn
  let K : Subfield k := fixedSubfield (iterateFrobenius k p ((d : ℕ) * n))
  have hK₀K : K₀.toSubfield ≤ K := by
    intro x hx
    change (iterateFrobenius k p ((d : ℕ) * n)) x = x
    rw [iterateFrobenius_def, pow_mul]
    have hx1 : x ^ p ^ (d : ℕ) = x := by
      have := FiniteField.pow_card (⟨x, hx⟩ : K₀)
      rw [hcard] at this
      exact congrArg Subtype.val this
    exact pow_pow_eq_self_of_pow_eq_self x _ hx1 n
  let i : K₀.toSubfield →+* K := Subfield.inclusion hK₀K
  let W : WeierstrassCurve K := W₀.map i
  have hWY : W.baseChange k = W₀.baseChange k := rfl
  let σ : k →ₐ[K] k :=
    { iterateFrobenius k p ((d : ℕ) * n) with
      commutes' := fun x => x.2 }
  have hσ : ∀ x : k, σ x = x ^ @Fintype.card K instK := fun x => by
    rw [hcardK]; exact iterateFrobenius_def p _ x
  have hσx : ∀ x : k, σ x = (σ₀ ^ n) x := by
    intro x
    rw [AlgHom.coe_pow]
    change x ^ p ^ ((d : ℕ) * n) = (fun y : k => y ^ p ^ (d : ℕ))^[n] x
    rw [iterate_pow_eq, ← pow_mul]
  have ha : ∀ P : (W⁄k).Point, WeierstrassCurve.Affine.Point.map (W' := W) σ P = a • P := by
    intro P
    have h1 := hiter P
    rw [iterate_map] at h1
    refine Eq.trans ?_ h1
    rcases P with _ | ⟨x, y, h⟩
    · rfl
    · rw [WeierstrassCurve.Affine.Point.map_some]
      erw [WeierstrassCurve.Affine.Point.map_some]
      congr 1 <;> exact hσx _
  refine ⟨K, instK, W, inferInstance, σ, a, hσ, ha, ⟨?_⟩⟩
  have hFF := @WeierstrassCurve.rationalEndSubring_baseChange_eq_of_frobenius_eq_smul K _ instK k _ _ _ _ W _ σ hσ a ha
  exact φ.symm.trans (RingEquiv.subringCongr hFF)

end WeierstrassCurve.ADGlue

theorem solution
    {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k]
    (p : ℕ) [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k] [Algebra.IsAlgebraic (ZMod p) k]
    (X : WeierstrassCurve k) [X.IsElliptic]
    (hss : ∀ P : X.toAffine.Point, p • P = 0 → P = 0) :
    ∃ (K : Subfield k) (_ : Fintype K) (W : WeierstrassCurve K) (_ : W.IsElliptic)
      (σ : k →ₐ[K] k) (a : ℤ),
      (∀ x : k, σ x = x ^ Fintype.card K) ∧
      (∀ P : (W⁄k).Point, WeierstrassCurve.Affine.Point.map (W' := W) σ P = a • P) ∧
      Nonempty (↥(WeierstrassCurve.rationalEndSubring k X) ≃+* ↥(WeierstrassCurve.rationalEndSubring k W)) :=
  WeierstrassCurve.ADGlue.main p X hss

end S_WeierstrassCurve_exists_subfield_model_frobenius_eq_smul_rationalEndSubring_equiv
end P2MW
export P2MW.S_WeierstrassCurve_exists_subfield_model_frobenius_eq_smul_rationalEndSubring_equiv (solution)
