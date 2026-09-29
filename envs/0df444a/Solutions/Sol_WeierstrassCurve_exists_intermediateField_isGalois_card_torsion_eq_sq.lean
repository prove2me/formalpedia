-- Prove2me | solution 1 for WeierstrassCurve.exists_intermediateField_isGalois_card_torsion_eq_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/bf7f7e8d-50e6-57f3-8135-29bab68935a4

import Mathlib
import Definitions.Def_WeierstrassCurve_DivPolyMulFormulaCore
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_intermediateField_isGalois_card_torsion_eq_sq
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option linter.unusedSectionVars false

p2m_open "WeierstrassCurve~instIsEllipticBaseChange WeierstrassCurve.Affine WeierstrassCurve.Affine.Point Polynomial"

namespace P2MKcDivField

universe u v

variable {F : Type u} {Ω : Type v} [Field F] [Field Ω] [Algebra F Ω] [DecidableEq Ω]

section FieldHelpers

lemma mem_separableClosure_of_root {z : Ω} (q : Polynomial (separableClosure F Ω))
    (hsep : (q.map (algebraMap (separableClosure F Ω) Ω)).Separable) (hroot : (q.map (algebraMap (separableClosure F Ω) Ω)).IsRoot z) :
    z ∈ (separableClosure F Ω) := by
  rw [mem_separableClosure_iff]
  have hq : q.Separable := (Polynomial.separable_map (algebraMap (separableClosure F Ω) Ω)).mp hsep
  have haeval : aeval z q = 0 := by rwa [aeval_def, eval₂_eq_eval_map]
  have hz : IsSeparable ((separableClosure F Ω)) z := (hq.of_dvd (minpoly.dvd (separableClosure F Ω) z haeval))
  exact IsSeparable.of_algebra_isSeparable_of_isSeparable F hz

lemma separable_of_natDegree_le_card {f : Polynomial Ω} (hf : f ≠ 0) (T : Finset Ω)
    (hT : ∀ t ∈ T, f.IsRoot t) (hdeg : f.natDegree ≤ T.card) : f.Separable := by
  classical
  have hsub : T ⊆ f.roots.toFinset := fun t ht => by
    rw [Multiset.mem_toFinset, mem_roots hf]; exact hT t ht
  have h1 : T.card ≤ f.roots.toFinset.card := Finset.card_le_card hsub
  have h2 : f.roots.toFinset.card ≤ f.roots.card := Multiset.toFinset_card_le _
  have h3 : f.roots.card ≤ f.natDegree := card_roots' f
  have hnodup : f.roots.Nodup := by
    rw [← Multiset.toFinset_card_eq_card_iff_nodup]; omega
  have hsplits : f.Splits := by
    rw [splits_iff_card_roots]; omega
  exact (nodup_roots_iff_of_splits hf hsplits).mp hnodup

end FieldHelpers

section SepPoints

variable (E : WeierstrassCurve F)

noncomputable def sepPoints : AddSubgroup (E.baseChange Ω).toAffine.Point :=
  (Point.map (IntermediateField.val (separableClosure F Ω)) :
    (E.baseChange (separableClosure F Ω)).toAffine.Point →+ (E.baseChange Ω).toAffine.Point).range

variable {E}

lemma some_mem_sepPoints_iff {x y : Ω} (h : (E.baseChange Ω).toAffine.Nonsingular x y) :
    Point.some x y h ∈ sepPoints E ↔ x ∈ (separableClosure F Ω) ∧ y ∈ (separableClosure F Ω) := by
  constructor
  · rintro ⟨P', hP'⟩
    cases P' with
    | zero => exact absurd hP'.symm (Point.some_ne_zero h)
    | some x' y' h' =>
      rw [Point.map_some] at hP'
      obtain ⟨rfl, rfl⟩ := Point.some.inj hP'
      exact ⟨x'.2, y'.2⟩
  · rintro ⟨hx, hy⟩
    have h' : (E.baseChange (separableClosure F Ω)).toAffine.Nonsingular ⟨x, hx⟩ ⟨y, hy⟩ :=
      (Affine.baseChange_nonsingular E (f := IntermediateField.val (separableClosure F Ω))
        Subtype.val_injective ⟨x, hx⟩ ⟨y, hy⟩).mp h
    exact ⟨Point.some _ _ h', by rw [Point.map_some]; rfl⟩

lemma Y_mem_of_X_mem {x y : Ω} (h : (E.baseChange Ω).toAffine.Equation x y) (hx : x ∈ (separableClosure F Ω))
    (hy : y ≠ (E.baseChange Ω).toAffine.negY x y ∨ (2 : F) ≠ 0) : y ∈ (separableClosure F Ω) := by

  set c : Ω := (E.baseChange Ω).a₁ * x + (E.baseChange Ω).a₃ with hc_def
  set f₀ : Ω := x ^ 3 + (E.baseChange Ω).a₂ * x ^ 2 + (E.baseChange Ω).a₄ * x
    + (E.baseChange Ω).a₆ with hf₀_def
  have ha₁ : (E.baseChange Ω).a₁ ∈ (separableClosure F Ω) :=
    IntermediateField.algebraMap_mem _ E.a₁
  have ha₂ : (E.baseChange Ω).a₂ ∈ (separableClosure F Ω) :=
    IntermediateField.algebraMap_mem _ E.a₂
  have ha₃ : (E.baseChange Ω).a₃ ∈ (separableClosure F Ω) :=
    IntermediateField.algebraMap_mem _ E.a₃
  have ha₄ : (E.baseChange Ω).a₄ ∈ (separableClosure F Ω) :=
    IntermediateField.algebraMap_mem _ E.a₄
  have ha₆ : (E.baseChange Ω).a₆ ∈ (separableClosure F Ω) :=
    IntermediateField.algebraMap_mem _ E.a₆
  have hc : c ∈ (separableClosure F Ω) := add_mem (mul_mem ha₁ hx) ha₃
  have hf₀ : f₀ ∈ (separableClosure F Ω) :=
    add_mem (add_mem (add_mem (pow_mem hx 3) (mul_mem ha₂ (pow_mem hx 2))) (mul_mem ha₄ hx)) ha₆
  have hnegY : (E.baseChange Ω).toAffine.negY x y = -y - c := by
    rw [negY, hc_def]; ring
  have heq : y ^ 2 + c * y = f₀ := by
    rw [equation_iff] at h
    rw [hc_def, hf₀_def]; linear_combination h
  by_cases hyn : y = (E.baseChange Ω).toAffine.negY x y
  ·
    have h2 : (2 : F) ≠ 0 := hy.resolve_left (not_not.mpr hyn)
    have h2Ω : (2 : Ω) ≠ 0 := by
      intro h0
      apply h2
      apply (algebraMap F Ω).injective
      rw [map_ofNat, _root_.map_zero, h0]
    have hyc : y = -c * 2⁻¹ := by
      rw [hnegY] at hyn
      field_simp
      linear_combination hyn
    rw [hyc]
    have h2S : (2 : Ω)⁻¹ ∈ (separableClosure F Ω) := by
      have : (2 : Ω)⁻¹ = algebraMap F Ω (2 : F)⁻¹ := by rw [map_inv₀, map_ofNat]
      rw [this]; exact IntermediateField.algebraMap_mem _ _
    exact mul_mem (neg_mem hc) h2S
  ·
    set y' : Ω := (E.baseChange Ω).toAffine.negY x y with hy'_def
    have hsum : y + y' = -c := by rw [hnegY]; ring
    have hprod : y * y' = -f₀ := by rw [hnegY, ← heq]; ring
    let cS : (separableClosure F Ω) := ⟨c, hc⟩
    let fS : (separableClosure F Ω) := ⟨f₀, hf₀⟩
    let q : Polynomial (separableClosure F Ω) := X ^ 2 + Polynomial.C cS * X - Polynomial.C fS
    have hqmap : q.map (algebraMap (separableClosure F Ω) Ω) =
        (X - Polynomial.C y) * (X - Polynomial.C y') := by
      have hq : q.map (algebraMap (separableClosure F Ω) Ω) =
          X ^ 2 + Polynomial.C c * X - Polynomial.C f₀ := by
        simp only [q, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow,
          Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C]
        rfl
      have h1 : Polynomial.C c = -(Polynomial.C y + Polynomial.C y') := by
        rw [← Polynomial.C_add, hsum, Polynomial.C_neg, neg_neg]
      have h2 : Polynomial.C f₀ = -(Polynomial.C y * Polynomial.C y') := by
        rw [← Polynomial.C_mul, hprod, Polynomial.C_neg, neg_neg]
      rw [hq, h1, h2]
      ring
    refine mem_separableClosure_of_root q ?_ ?_
    · rw [hqmap]
      exact separable_X_sub_C.mul separable_X_sub_C
        (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hyn).isUnit)
    · rw [hqmap, IsRoot, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul]

lemma card_le_two_mul_card_image_xOrZero (U : Finset (E.baseChange Ω).toAffine.Point)
    (hU : ∀ P ∈ U, P ≠ 0) : U.card ≤ 2 * (U.image Point.xOrZero).card := by
  classical
  refine Finset.card_le_mul_card_image U 2 fun b hb => ?_
  obtain ⟨P₁, hP₁U, rfl⟩ := Finset.mem_image.mp hb
  have hP₁ := hU P₁ hP₁U

  have hsub : (U.filter fun P => P.xOrZero = P₁.xOrZero) ⊆ {P₁, -P₁} := by
    intro P hP
    rw [Finset.mem_filter] at hP
    obtain ⟨hPU, hPx⟩ := hP
    have hP0 := hU P hPU
    rcases P with _ | ⟨x, y, hxy⟩
    · exact absurd rfl hP0
    rcases P₁ with _ | ⟨x₁, y₁, hxy₁⟩
    · exact absurd rfl hP₁
    simp only [xOrZero_some] at hPx
    subst hPx
    rw [Finset.mem_insert, Finset.mem_singleton, neg_some]
    by_cases hyy : y = (E.baseChange Ω).toAffine.negY x y₁
    · right; subst hyy; rfl
    · left
      have := Y_eq_of_Y_ne hxy.1 hxy₁.1 rfl hyy
      subst this; rfl
  calc (U.filter fun P => P.xOrZero = P₁.xOrZero).card ≤ ({P₁, -P₁} : Finset _).card :=
        Finset.card_le_card hsub
    _ ≤ 2 := Finset.card_le_two

end SepPoints

section Torsion

variable (E : WeierstrassCurve F) [E.IsElliptic] [IsAlgClosed Ω]

scoped instance instIsEllipticBaseChange : (E.baseChange Ω).IsElliptic :=
  show (E.map (algebraMap F Ω)).IsElliptic from inferInstance

lemma finite_and_ncard_torsion {m : ℕ} (hm : (m : Ω) ≠ 0) :
    Set.Finite {P : (E.baseChange Ω).toAffine.Point | m • P = 0} ∧
      Set.ncard {P : (E.baseChange Ω).toAffine.Point | m • P = 0} = m ^ 2 := by
  obtain ⟨e⟩ := nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := Ω) E hm
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
  haveI : NeZero m := ⟨hm0⟩
  have hset : {P : (E.baseChange Ω).toAffine.Point | m • P = 0} =
      (Submodule.torsionBy ℤ (E.baseChange Ω).toAffine.Point (m : ℤ) : Set _) := by
    ext P
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, Submodule.mem_torsionBy_iff, natCast_zsmul]
  have hfin : Finite (Submodule.torsionBy ℤ (E.baseChange Ω).toAffine.Point (m : ℤ)) :=
    Finite.of_equiv _ e.toEquiv
  have hcard : Nat.card (Submodule.torsionBy ℤ (E.baseChange Ω).toAffine.Point (m : ℤ)) = m ^ 2 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zmod, sq]
  rw [hset]
  refine ⟨Set.toFinite _, ?_⟩
  rw [← hcard, ← Nat.card_coe_set_eq]
  rfl

noncomputable def torsFinset {m : ℕ} (hm : (m : Ω) ≠ 0) : Finset (E.baseChange Ω).toAffine.Point :=
  (finite_and_ncard_torsion E hm).1.toFinset

variable {E}

lemma mem_torsFinset {m : ℕ} (hm : (m : Ω) ≠ 0) (P : (E.baseChange Ω).toAffine.Point) :
    P ∈ torsFinset E hm ↔ m • P = 0 := by
  rw [torsFinset, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

lemma card_torsFinset {m : ℕ} (hm : (m : Ω) ≠ 0) : (torsFinset E hm).card = m ^ 2 := by
  rw [torsFinset, ← Set.ncard_eq_toFinset_card _ (finite_and_ncard_torsion E hm).1]
  exact (finite_and_ncard_torsion E hm).2

omit [E.IsElliptic] [IsAlgClosed Ω] in

lemma natCast_ne_zero_of_ne_zero {m : ℕ} (hm : (m : F) ≠ 0) : (m : Ω) ≠ 0 := by
  intro h0
  apply hm
  apply (algebraMap F Ω).injective
  rw [map_natCast, _root_.map_zero, h0]

omit [E.IsElliptic] [IsAlgClosed Ω] in

lemma natCast_ne_zero_of_dvd {m d : ℕ} (hm : (m : F) ≠ 0) (hd : d ∣ m) : (d : F) ≠ 0 := by
  obtain ⟨k, rfl⟩ := hd
  intro h0
  apply hm
  rw [Nat.cast_mul, h0, zero_mul]

omit [E.IsElliptic] [IsAlgClosed Ω] in
lemma lowTorsionFree_of_lt_addOrderOf {x y : Ω} (h : (E.baseChange Ω).toAffine.Nonsingular x y)
    {m : ℕ} (hm : m < addOrderOf (Point.some x y h)) : LowTorsionFree m h :=
  fun k hk1 hkm => nsmul_ne_zero_of_lt_addOrderOf (by omega) (by omega)

omit [E.IsElliptic] [IsAlgClosed Ω] in

lemma ΨSq_eval_eq_zero_of_addOrderOf_prime {ℓ : ℕ} (hℓ : ℓ.Prime) (h3 : 3 ≤ ℓ) {x y : Ω}
    (h : (E.baseChange Ω).toAffine.Nonsingular x y) (hord : addOrderOf (Point.some x y h) = ℓ) :
    ((E.baseChange Ω).ΨSq ℓ).eval x = 0 := by
  have hfree : LowTorsionFree (ℓ - 1) h := lowTorsionFree_of_lt_addOrderOf h (by omega)
  have hmf : MFred (ℓ - 1) h := mfred_all h (ℓ - 1) (by omega) hfree
  have hkill : (ℓ - 1 + 1) • (Point.some x y h : (E.baseChange Ω).toAffine.Point) = 0 := by
    rw [Nat.sub_add_cancel (by omega), ← hord]; exact addOrderOf_nsmul_eq_zero _
  rcases ΨSq_eval_eq_zero_or_of_succ_nsmul_eq_zero h hmf hkill with h1 | h2
  · rwa [show ((ℓ - 1 : ℕ) : ℤ) + 1 = (ℓ : ℤ) by omega] at h1
  · exfalso
    by_cases hℓ3 : ℓ = 3
    · subst hℓ3
      rw [show ((3 - 1 : ℕ) : ℤ) - 1 = 1 by norm_num, ΨSq_one, eval_one] at h2
      exact one_ne_zero h2
    · have h5 : 5 ≤ ℓ := hℓ.five_le_of_ne_two_of_ne_three (by omega) hℓ3
      have hfree' : LowTorsionFree (ℓ - 3) h := hfree.mono (by omega)
      have hmf' : MFred (ℓ - 3) h := mfred_all h (ℓ - 3) (by omega) hfree'
      have h2' : ((E.baseChange Ω).ΨSq (((ℓ - 3 : ℕ) : ℤ) + 1)).eval x = 0 := by
        rwa [show (((ℓ - 3 : ℕ) : ℤ) + 1) = ((ℓ - 1 : ℕ) : ℤ) - 1 by omega]
      have hzero := nsmul_succ_eq_zero_of_ΨSq_eval_eq_zero (by omega : 2 ≤ ℓ - 3) h hfree' hmf' h2'
      exact hfree (ℓ - 3 + 1) (by omega) (by omega) hzero

omit [E.IsElliptic] [IsAlgClosed Ω] in

lemma isRoot_of_nsmul_eq {ℓ : ℕ} (hℓ1 : 1 ≤ ℓ) {x' y' : Ω}
    (h' : (E.baseChange Ω).toAffine.Nonsingular x' y') (hfree : LowTorsionFree ℓ h')
    {xQ yQ : Ω} (hQ : (E.baseChange Ω).toAffine.Nonsingular xQ yQ)
    (hmul : ℓ • (Point.some x' y' h' : (E.baseChange Ω).toAffine.Point) = Point.some xQ yQ hQ ∨
      ℓ • (Point.some x' y' h' : (E.baseChange Ω).toAffine.Point) = -Point.some xQ yQ hQ) :
    ((E.baseChange Ω).Φ ℓ - Polynomial.C xQ * (E.baseChange Ω).ΨSq ℓ).IsRoot x' := by
  obtain ⟨-, hform⟩ := mfred_all h' ℓ hℓ1 hfree
  have hx : (ℓ • (Point.some x' y' h' : (E.baseChange Ω).toAffine.Point)).xOrZero = xQ := by
    rcases hmul with hmul | hmul <;> rw [hmul]
    · rfl
    · rw [neg_some]; rfl
  rw [hx] at hform
  rw [IsRoot, eval_sub, eval_mul, eval_C, ← hform]
  ring

omit [E.IsElliptic] [IsAlgClosed Ω] in

lemma mem_separableClosure_of_root_F {z : Ω} (q : Polynomial F)
    (hsep : (q.map (algebraMap F Ω)).Separable) (hroot : (q.map (algebraMap F Ω)).IsRoot z) :
    z ∈ separableClosure F Ω := by
  rw [mem_separableClosure_iff]
  have hq : q.Separable := (Polynomial.separable_map (algebraMap F Ω)).mp hsep
  have haeval : aeval z q = 0 := by rwa [aeval_def, eval₂_eq_eval_map]
  exact hq.of_dvd (minpoly.dvd F z haeval)

omit [E.IsElliptic] [IsAlgClosed Ω] in

lemma Y_ne_negY_of_two_nsmul_ne_zero {x y : Ω} (h : (E.baseChange Ω).toAffine.Nonsingular x y)
    (h2 : (2 : ℕ) • (Point.some x y h : (E.baseChange Ω).toAffine.Point) ≠ 0) :
    y ≠ (E.baseChange Ω).toAffine.negY x y := fun hy =>
  h2 (by rw [two_nsmul]; exact add_self_of_Y_eq hy)

lemma mem_sepPoints_of_addOrderOf_prime {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓF : (ℓ : F) ≠ 0)
    (P : (E.baseChange Ω).toAffine.Point) (hord : addOrderOf P = ℓ) : P ∈ sepPoints E := by
  classical
  have hℓΩ : (ℓ : Ω) ≠ 0 := natCast_ne_zero_of_ne_zero hℓF
  have hP0 : P ≠ 0 := fun h0 => hℓ.one_lt.ne' (by rw [← hord, h0, addOrderOf_zero])
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP0
  have hℓP : ℓ • (Point.some x y h : (E.baseChange Ω).toAffine.Point) = 0 := by
    rw [← hord]; exact addOrderOf_nsmul_eq_zero _
  rw [some_mem_sepPoints_iff]
  by_cases hℓ2 : ℓ = 2
  ·
    subst hℓ2
    have h2F : (2 : F) ≠ 0 := by exact_mod_cast hℓF
    have hx : x ∈ separableClosure F Ω := by
      refine mem_separableClosure_of_root_F E.twoTorsionPolynomial.toPoly ?_ ?_
      ·
        have hsplit : ((E.twoTorsionPolynomial.toPoly).map (algebraMap F Ω)).Splits :=
          IsAlgClosed.splits _
        have ha : E.twoTorsionPolynomial.a ≠ 0 := by
          show (4 : F) ≠ 0
          have : (4 : F) = 2 * 2 := by norm_num
          rw [this]; exact mul_ne_zero h2F h2F
        have hdisc : E.twoTorsionPolynomial.discr ≠ 0 :=
          E.twoTorsionPolynomial_discr_ne_zero (Ne.isUnit h2F) E.isUnit_Δ
        have hnodup := (Cubic.discr_ne_zero_iff_roots_nodup ha hsplit).mp hdisc
        rw [Cubic.roots, Cubic.map_toPoly] at hnodup
        refine (nodup_roots_iff_of_splits ?_ hsplit).mp hnodup
        exact Polynomial.map_ne_zero (Cubic.ne_zero_of_a_ne_zero ha)
      ·
        have hroot : ((E.baseChange Ω).Ψ₂Sq).eval x = 0 :=
          (Ψ₂Sq_eval_eq_zero_iff_two_smul' h).mpr hℓP
        rw [Ψ₂Sq_eq] at hroot
        have hmap : (E.baseChange Ω).twoTorsionPolynomial =
            Cubic.map (algebraMap F Ω) E.twoTorsionPolynomial := by
          simp only [twoTorsionPolynomial, Cubic.map, WeierstrassCurve.baseChange, map_b₂, map_b₄,
            map_b₆, map_ofNat, map_mul]
        rw [hmap, Cubic.map_toPoly] at hroot
        exact hroot
    exact ⟨hx, Y_mem_of_X_mem h.1 hx (Or.inr h2F)⟩
  ·
    have h3 : 3 ≤ ℓ := by have := hℓ.two_le; omega
    have hodd : ¬Even (ℓ : ℤ) := by
      rw [Int.even_coe_nat, Nat.not_even_iff_odd]
      exact hℓ.odd_of_ne_two hℓ2

    set U := (torsFinset E hℓΩ).filter (fun P => P ≠ 0) with hU_def
    have hUcard : U.card = ℓ ^ 2 - 1 := by
      have h0mem : (0 : (E.baseChange Ω).toAffine.Point) ∈ torsFinset E hℓΩ := by
        rw [mem_torsFinset]; exact nsmul_zero _
      rw [hU_def, Finset.filter_ne', Finset.card_erase_of_mem h0mem, card_torsFinset]
    have hUne : ∀ P ∈ U, P ≠ 0 := fun P hP => (Finset.mem_filter.mp hP).2
    set Xs := U.image Point.xOrZero with hXs_def
    have hXcard : (ℓ ^ 2 - 1) / 2 ≤ Xs.card := by
      have := card_le_two_mul_card_image_xOrZero U hUne
      rw [hUcard, ← hXs_def] at this
      omega

    have hT : ((E.baseChange Ω).preΨ ℓ).natDegree = (ℓ ^ 2 - 1) / 2 := by
      rw [natDegree_preΨ _ (by exact_mod_cast hℓΩ), if_neg hodd, Int.natAbs_natCast]
    have hT0 : (E.baseChange Ω).preΨ ℓ ≠ 0 := preΨ_ne_zero _ (by exact_mod_cast hℓΩ)
    have hroots : ∀ t ∈ Xs, ((E.baseChange Ω).preΨ ℓ).IsRoot t := by
      intro t ht
      obtain ⟨P', hP'U, rfl⟩ := Finset.mem_image.mp ht
      have hP'0 := hUne P' hP'U
      have hP'ℓ : ℓ • P' = 0 := (mem_torsFinset hℓΩ P').mp (Finset.mem_filter.mp hP'U).1
      rcases P' with _ | ⟨x', y', h'⟩
      · exact absurd rfl hP'0
      have hord' : addOrderOf (Point.some x' y' h' : (E.baseChange Ω).toAffine.Point) = ℓ :=
        haveI : Fact ℓ.Prime := ⟨hℓ⟩
        addOrderOf_eq_prime hP'ℓ hP'0
      have hΨ := ΨSq_eval_eq_zero_of_addOrderOf_prime hℓ h3 h' hord'
      rw [ΨSq_of_odd _ hodd, eval_pow] at hΨ
      rw [xOrZero_some, IsRoot]
      exact pow_eq_zero_iff two_ne_zero |>.mp hΨ
    have hsepΩ : ((E.baseChange Ω).preΨ ℓ).Separable :=
      separable_of_natDegree_le_card hT0 Xs hroots (hT ▸ hXcard)
    have hpre : (E.preΨ ℓ).map (algebraMap F Ω) = (E.baseChange Ω).preΨ ℓ :=
      (E.map_preΨ (algebraMap F Ω) ℓ).symm
    have hx : x ∈ separableClosure F Ω := by
      refine mem_separableClosure_of_root_F (E.preΨ ℓ) ?_ ?_
      · rwa [hpre]
      · rw [hpre]
        have hmem : (Point.some x y h : (E.baseChange Ω).toAffine.Point) ∈ U := by
          rw [hU_def, Finset.mem_filter, mem_torsFinset]
          exact ⟨hℓP, Point.some_ne_zero h⟩
        exact hroots x (Finset.mem_image.mpr ⟨_, hmem, rfl⟩)
    refine ⟨hx, Y_mem_of_X_mem h.1 hx (Or.inl (Y_ne_negY_of_two_nsmul_ne_zero h ?_))⟩
    exact nsmul_ne_zero_of_lt_addOrderOf two_ne_zero (by rw [hord]; omega)

lemma mem_sepPoints_of_descent (P : (E.baseChange Ω).toAffine.Point) {d ℓ d' : ℕ}
    (hd : addOrderOf P = d) (hdF : (d : F) ≠ 0) (hℓ : ℓ.Prime) (hdℓ : d = ℓ * d')
    (hmin : ∀ q : ℕ, q.Prime → q ∣ d → ℓ ≤ q) (h3 : 3 ≤ d')
    (hQ : ℓ • P ∈ sepPoints E) : P ∈ sepPoints E := by
  classical
  have hℓF : (ℓ : F) ≠ 0 := natCast_ne_zero_of_dvd hdF ⟨d', hdℓ⟩
  have hℓΩ : (ℓ : Ω) ≠ 0 := natCast_ne_zero_of_ne_zero hℓF
  have hℓ0 : ℓ ≠ 0 := hℓ.ne_zero
  have hdP : d • P = 0 := hd ▸ addOrderOf_nsmul_eq_zero P

  have hP0 : P ≠ 0 := by
    intro h0
    rw [h0, addOrderOf_zero] at hd
    have h1 : ℓ = 1 := Nat.eq_one_of_mul_eq_one_right (hdℓ ▸ hd).symm
    exact hℓ.one_lt.ne' h1
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP0
  set Pt : (E.baseChange Ω).toAffine.Point := Point.some x y h with hPt_def

  have hordQ : addOrderOf (ℓ • Pt) = d' := by
    rw [addOrderOf_nsmul_of_dvd hℓ0 (by rw [hd, hdℓ]; exact dvd_mul_right ℓ d'), hd, hdℓ,
      Nat.mul_div_cancel_left _ hℓ.pos]
  have hQ0 : ℓ • Pt ≠ 0 := by
    intro h0; rw [h0, addOrderOf_zero] at hordQ; omega
  obtain ⟨xQ, yQ, hQ', hQeq⟩ : ∃ (xQ yQ : Ω) (hQ' : (E.baseChange Ω).toAffine.Nonsingular xQ yQ),
      ℓ • Pt = Point.some xQ yQ hQ' := by
    rcases hq : ℓ • Pt with _ | ⟨xQ, yQ, hQ'⟩
    · exact absurd hq hQ0
    · exact ⟨xQ, yQ, hQ', rfl⟩
  rw [hQeq, some_mem_sepPoints_iff] at hQ
  obtain ⟨hxQ, hyQ⟩ := hQ

  set hp : Polynomial Ω := (E.baseChange Ω).Φ ℓ - Polynomial.C xQ * (E.baseChange Ω).ΨSq ℓ
    with hp_def
  have hΦdeg : ((E.baseChange Ω).Φ ℓ).natDegree = ℓ ^ 2 := by
    rw [natDegree_Φ, Int.natAbs_natCast]
  have hpdeg : hp.natDegree = ℓ ^ 2 := by
    rw [hp_def, natDegree_sub_eq_left_of_natDegree_lt, hΦdeg]
    rw [hΦdeg]
    calc (Polynomial.C xQ * (E.baseChange Ω).ΨSq ℓ).natDegree
        ≤ ((E.baseChange Ω).ΨSq ℓ).natDegree := natDegree_C_mul_le _ _
      _ = ℓ ^ 2 - 1 := by rw [natDegree_ΨSq _ (by exact_mod_cast hℓΩ), Int.natAbs_natCast]
      _ < ℓ ^ 2 := by
          have : 1 ≤ ℓ ^ 2 := Nat.one_le_pow _ _ hℓ.pos
          omega
  have hp0 : hp ≠ 0 := fun h0 => by
    rw [h0, natDegree_zero] at hpdeg
    exact pow_ne_zero 2 hℓ0 hpdeg.symm

  have hfreeCoset : ∀ ε : (E.baseChange Ω).toAffine.Point, (ε = Pt ∨ ε = -Pt) →
      ∀ T : (E.baseChange Ω).toAffine.Point, ℓ • T = 0 →
      ∀ (x' y' : Ω) (h' : (E.baseChange Ω).toAffine.Nonsingular x' y'),
        ε + T = Point.some x' y' h' → LowTorsionFree ℓ h' := by
    intro ε hε T hT x' y' h' hP' k hk1 hkℓ hk0
    have hℓP' : ℓ • (Point.some x' y' h' : (E.baseChange Ω).toAffine.Point) ≠ 0 := by
      rw [← hP', nsmul_add, hT, add_zero]
      rcases hε with rfl | rfl
      · exact hQ0
      · rw [neg_nsmul, neg_ne_zero]; exact hQ0
    have hdP' : d • (Point.some x' y' h' : (E.baseChange Ω).toAffine.Point) = 0 := by
      rw [← hP', nsmul_add]
      have hdT : d • T = 0 := by rw [hdℓ, mul_nsmul, hT, nsmul_zero]
      rw [hdT, add_zero]
      rcases hε with rfl | rfl
      · exact hdP
      · rw [neg_nsmul, hdP, _root_.neg_zero]
    set o := addOrderOf (Point.some x' y' h' : (E.baseChange Ω).toAffine.Point) with ho_def
    have hod : o ∣ d := addOrderOf_dvd_of_nsmul_eq_zero hdP'
    have hok : o ∣ k := addOrderOf_dvd_of_nsmul_eq_zero hk0
    have ho0 : o ≠ 0 := fun h0 => by rw [h0, zero_dvd_iff] at hok; omega
    have ho1 : o ≠ 1 := fun h1 => Point.some_ne_zero h' (AddMonoid.addOrderOf_eq_one_iff.mp h1)
    have hole : o ≤ k := Nat.le_of_dvd (by omega) hok
    have hq := Nat.minFac_prime ho1
    have hℓq : ℓ ≤ o.minFac := hmin _ hq (dvd_trans (Nat.minFac_dvd o) hod)
    have hqo : o.minFac ≤ o := Nat.minFac_le (by omega)
    have hoℓ : o = ℓ := by omega
    exact hℓP' (by rw [← hoℓ, ho_def]; exact addOrderOf_nsmul_eq_zero _)

  set U : Finset (E.baseChange Ω).toAffine.Point :=
    (torsFinset E hℓΩ).image (fun T => Pt + T) ∪ (torsFinset E hℓΩ).image (fun T => -Pt + T)
    with hU_def
  have hUne : ∀ P' ∈ U, P' ≠ 0 := by
    intro P' hP' h0
    rw [hU_def, Finset.mem_union, Finset.mem_image, Finset.mem_image] at hP'
    rcases hP' with ⟨T, hT, rfl⟩ | ⟨T, hT, rfl⟩ <;> rw [mem_torsFinset] at hT <;> apply hQ0
    · rw [add_eq_zero_iff_eq_neg.mp h0, neg_nsmul, hT, _root_.neg_zero]
    · rw [neg_add_eq_zero.mp h0, hT]
  have hdisj : Disjoint ((torsFinset E hℓΩ).image (fun T => Pt + T))
      ((torsFinset E hℓΩ).image (fun T => -Pt + T)) := by
    rw [Finset.disjoint_left]
    intro P' h1 h2
    rw [Finset.mem_image] at h1 h2
    obtain ⟨T, hT, rfl⟩ := h1
    obtain ⟨T', hT', hEq⟩ := h2
    rw [mem_torsFinset] at hT hT'
    have e1 : Pt + Pt = T' - T := by
      calc Pt + Pt = Pt + Pt + (-Pt + T') - (Pt + T) := by rw [hEq]; abel
        _ = T' - T := by abel
    have h2Pt : (ℓ * 2) • Pt = 0 := by
      rw [mul_nsmul', two_nsmul, e1, nsmul_sub, hT, hT', sub_zero]
    have hdvd : d ∣ ℓ * 2 := by rw [← hd]; exact addOrderOf_dvd_of_nsmul_eq_zero h2Pt
    rw [hdℓ] at hdvd
    have hd'2 : d' ≤ 2 := Nat.le_of_dvd two_pos (Nat.dvd_of_mul_dvd_mul_left hℓ.pos hdvd)
    omega
  have hUcard : U.card = 2 * ℓ ^ 2 := by
    rw [hU_def, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (add_right_injective Pt),
      Finset.card_image_of_injective _ (add_right_injective (-Pt)), card_torsFinset]
    ring
  set Xs := U.image Point.xOrZero with hXs_def
  have hXcard : ℓ ^ 2 ≤ Xs.card := by
    have := card_le_two_mul_card_image_xOrZero U hUne
    rw [hUcard, ← hXs_def] at this
    omega
  have hroots : ∀ t ∈ Xs, hp.IsRoot t := by
    intro t ht
    obtain ⟨P', hP'U, rfl⟩ := Finset.mem_image.mp ht
    have hP'0 := hUne P' hP'U
    obtain ⟨ε, hε, T, hT, hP'eq⟩ : ∃ ε : (E.baseChange Ω).toAffine.Point, (ε = Pt ∨ ε = -Pt) ∧
        ∃ T : (E.baseChange Ω).toAffine.Point, ℓ • T = 0 ∧ ε + T = P' := by
      rw [hU_def, Finset.mem_union, Finset.mem_image, Finset.mem_image] at hP'U
      rcases hP'U with ⟨T, hT, rfl⟩ | ⟨T, hT, rfl⟩ <;> rw [mem_torsFinset] at hT
      · exact ⟨Pt, Or.inl rfl, T, hT, rfl⟩
      · exact ⟨-Pt, Or.inr rfl, T, hT, rfl⟩
    rcases P' with _ | ⟨x', y', h'⟩
    · exact absurd rfl hP'0
    have hfree := hfreeCoset ε hε T hT x' y' h' hP'eq
    rw [xOrZero_some]
    refine isRoot_of_nsmul_eq hℓ.one_lt.le h' hfree hQ' ?_
    rw [← hP'eq, nsmul_add, hT, add_zero]
    rcases hε with rfl | rfl
    · left; exact hQeq
    · right; rw [neg_nsmul, hQeq]
  have hsep : hp.Separable := separable_of_natDegree_le_card hp0 Xs hroots (hpdeg ▸ hXcard)

  have hx : x ∈ separableClosure F Ω := by
    have hbc : (E.baseChange (separableClosure F Ω)).map
        (algebraMap (separableClosure F Ω) Ω) = E.baseChange Ω := by
      rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_map, ← IsScalarTower.algebraMap_eq]
      rfl
    let hS : Polynomial (separableClosure F Ω) :=
      (E.baseChange (separableClosure F Ω)).Φ ℓ
        - Polynomial.C (⟨xQ, hxQ⟩ : separableClosure F Ω) * (E.baseChange (separableClosure F Ω)).ΨSq ℓ
    have hmap : hS.map (algebraMap (separableClosure F Ω) Ω) = hp := by
      rw [hp_def, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, ← map_Φ, ← map_ΨSq, hbc]
      rfl
    refine mem_separableClosure_of_root hS (hmap ▸ hsep) ?_
    rw [hmap]
    have hmem : Pt ∈ U := by
      rw [hU_def, Finset.mem_union]
      left
      rw [Finset.mem_image]
      exact ⟨0, (mem_torsFinset hℓΩ 0).mpr (nsmul_zero _), add_zero _⟩
    exact hroots x (Finset.mem_image.mpr ⟨Pt, hmem, rfl⟩)
  refine (some_mem_sepPoints_iff h).mpr
    ⟨hx, Y_mem_of_X_mem h.1 hx (Or.inl (Y_ne_negY_of_two_nsmul_ne_zero h ?_))⟩
  refine nsmul_ne_zero_of_lt_addOrderOf two_ne_zero ?_
  rw [hd, hdℓ]
  nlinarith [hℓ.two_le]

lemma mem_sepPoints_of_addOrderOf_eq_four (P : (E.baseChange Ω).toAffine.Point)
    (hord : addOrderOf P = 4) (h2F : (2 : F) ≠ 0) : P ∈ sepPoints E := by
  classical

  obtain ⟨q, hq, hq2, hqF⟩ : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ (q : F) ≠ 0 := by
    by_cases h3 : (3 : F) ≠ 0
    · exact ⟨3, Nat.prime_three, by norm_num, by exact_mod_cast h3⟩
    · refine ⟨5, Nat.prime_five, by norm_num, ?_⟩
      rw [not_not] at h3
      have h5 : ((5 : ℕ) : F) = 3 + 2 := by norm_num
      rw [h5, h3, zero_add]
      exact h2F
  have hqΩ : (q : Ω) ≠ 0 := natCast_ne_zero_of_ne_zero hqF
  have h4F : ((4 : ℕ) : F) ≠ 0 := by
    have : ((4 : ℕ) : F) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2F h2F
  have hcop2 : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2)
  have hcop4 : Nat.Coprime 4 q := by
    have := Nat.Coprime.pow_left 2 hcop2
    simpa using this

  obtain ⟨R, hRq, hR0⟩ : ∃ R : (E.baseChange Ω).toAffine.Point, q • R = 0 ∧ R ≠ 0 := by
    have hcard : 1 < (torsFinset E hqΩ).card := by
      rw [card_torsFinset]
      have := hq.two_le
      nlinarith
    obtain ⟨R, hR, hR0⟩ := Finset.exists_mem_ne hcard 0
    exact ⟨R, (mem_torsFinset hqΩ R).mp hR, hR0⟩
  have hordR : addOrderOf R = q := by
    haveI : Fact q.Prime := ⟨hq⟩
    exact addOrderOf_eq_prime hRq hR0
  have hRsep : R ∈ sepPoints E := mem_sepPoints_of_addOrderOf_prime hq hqF R hordR

  have hordPR : addOrderOf (P + R) = 2 * (2 * q) := by
    rw [AddCommute.addOrderOf_add_eq_mul_addOrderOf_of_coprime (AddCommute.all _ _)
      (by rw [hord, hordR]; exact hcop4), hord, hordR]
    ring
  have hord2P : addOrderOf ((2 : ℕ) • P) = 2 := by
    rw [addOrderOf_nsmul_of_dvd two_ne_zero (by rw [hord]; norm_num), hord]
  have hord2R : addOrderOf ((2 : ℕ) • R) = q := by
    rw [Nat.Coprime.addOrderOf_nsmul (by rw [hordR]; exact hcop2.symm), hordR]
  have hord2PR : addOrderOf ((2 : ℕ) • (P + R)) = 2 * q := by
    rw [nsmul_add, AddCommute.addOrderOf_add_eq_mul_addOrderOf_of_coprime (AddCommute.all _ _)
      (by rw [hord2P, hord2R]; exact hcop2), hord2P, hord2R]
  have hord4R : addOrderOf ((4 : ℕ) • R) = q := by
    rw [Nat.Coprime.addOrderOf_nsmul (by rw [hordR]; exact hcop4.symm), hordR]
  have h4PR : (2 : ℕ) • ((2 : ℕ) • (P + R)) = (4 : ℕ) • R := by
    rw [← mul_nsmul', show 2 * 2 = 4 by norm_num, nsmul_add]
    have h4P : (4 : ℕ) • P = 0 := by rw [← hord]; exact addOrderOf_nsmul_eq_zero P
    rw [h4P, zero_add]

  have hmin2 : ∀ (m q' : ℕ), q'.Prime → q' ∣ m → 2 ≤ q' := fun _ _ hq' _ => hq'.two_le
  have hq3 : 3 ≤ q := by
    have := hq.two_le
    omega

  have h4Rsep : (4 : ℕ) • R ∈ sepPoints E :=
    mem_sepPoints_of_addOrderOf_prime hq hqF _ hord4R
  have h2PRsep : (2 : ℕ) • (P + R) ∈ sepPoints E := by
    refine mem_sepPoints_of_descent (E := E) _ hord2PR ?_ Nat.prime_two rfl (hmin2 _) hq3 ?_
    · rw [Nat.cast_mul]; exact mul_ne_zero h2F hqF
    · rw [h4PR]; exact h4Rsep
  have hPRsep : P + R ∈ sepPoints E := by
    refine mem_sepPoints_of_descent (E := E) _ hordPR ?_ Nat.prime_two rfl (hmin2 _) (by omega) h2PRsep
    rw [Nat.cast_mul, Nat.cast_mul]
    exact mul_ne_zero h2F (mul_ne_zero h2F hqF)
  have : P = (P + R) - R := by abel
  rw [this]
  exact sub_mem hPRsep hRsep

theorem mem_sepPoints_of_nsmul_eq_zero {n : ℕ} (hn : (n : F) ≠ 0)
    (P : (E.baseChange Ω).toAffine.Point) (hP : n • P = 0) : P ∈ sepPoints E := by
  classical

  suffices key : ∀ d : ℕ, ∀ P : (E.baseChange Ω).toAffine.Point,
      addOrderOf P = d → (d : F) ≠ 0 → P ∈ sepPoints E from
    key _ P rfl (natCast_ne_zero_of_dvd hn (addOrderOf_dvd_of_nsmul_eq_zero hP))
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro P hd hdF
    have hd0 : d ≠ 0 := by rintro rfl; exact hdF Nat.cast_zero
    by_cases hd1 : d = 1
    · subst hd1
      rw [AddMonoid.addOrderOf_eq_one_iff.mp hd]
      exact zero_mem _
    by_cases hprime : d.Prime
    · exact mem_sepPoints_of_addOrderOf_prime hprime hdF P hd
    by_cases hd4 : d = 4
    · subst hd4
      refine mem_sepPoints_of_addOrderOf_eq_four P hd ?_
      intro h2
      apply hdF
      have : ((4 : ℕ) : F) = 2 * 2 := by norm_num
      rw [this, h2, zero_mul]

    set ℓ := d.minFac with hℓ_def
    have hℓ : ℓ.Prime := Nat.minFac_prime hd1
    have hℓd : ℓ ∣ d := Nat.minFac_dvd d
    obtain ⟨d', hdℓ⟩ := hℓd
    have hd'0 : d' ≠ 0 := by rintro rfl; exact hd0 (by rw [hdℓ, mul_zero])
    have hd'1 : d' ≠ 1 := by rintro rfl; exact hprime (by rw [hdℓ, mul_one]; exact hℓ)
    have hd'2 : d' ≠ 2 := by
      rintro rfl

      have hℓ2 : ℓ ≤ 2 := by
        rw [hℓ_def]
        exact Nat.minFac_le_of_dvd le_rfl ⟨ℓ, by rw [hdℓ, mul_comm]⟩
      have hℓ2' : ℓ = 2 := le_antisymm hℓ2 hℓ.two_le
      exact hd4 (by rw [hdℓ, hℓ2'])
    have h3 : 3 ≤ d' := by omega
    have hmin : ∀ q : ℕ, q.Prime → q ∣ d → ℓ ≤ q := fun q hq hqd =>
      hℓ_def ▸ Nat.minFac_le_of_dvd hq.two_le hqd

    have hordQ : addOrderOf (ℓ • P) = d' := by
      rw [addOrderOf_nsmul_of_dvd hℓ.ne_zero (by rw [hd, hdℓ]; exact dvd_mul_right ℓ d'), hd, hdℓ,
        Nat.mul_div_cancel_left _ hℓ.pos]
    have hd'lt : d' < d := by
      rw [hdℓ]
      have := hℓ.two_le
      nlinarith [Nat.pos_of_ne_zero hd'0]
    have hQ : ℓ • P ∈ sepPoints E :=
      ih d' hd'lt _ hordQ (natCast_ne_zero_of_dvd hdF ⟨ℓ, by rw [hdℓ, mul_comm]⟩)
    exact mem_sepPoints_of_descent P hd hdF hℓ hdℓ hmin h3 hQ

end Torsion

section DivisionField

variable (E : WeierstrassCurve F) [E.IsElliptic] [IsAlgClosed Ω] [Algebra.IsAlgebraic F Ω]

def ptCoords : (E.baseChange Ω).toAffine.Point → Finset Ω
  | .zero => ∅
  | .some x y _ => {x, y}

variable {E}

omit [E.IsElliptic] [IsAlgClosed Ω] [Algebra.IsAlgebraic F Ω] in
lemma mem_ptCoords_some_left {x y : Ω} (h : (E.baseChange Ω).toAffine.Nonsingular x y) :
    x ∈ ptCoords E (Point.some x y h) := by
  show x ∈ ({x, y} : Finset Ω); simp

omit [E.IsElliptic] [IsAlgClosed Ω] [Algebra.IsAlgebraic F Ω] in
lemma mem_ptCoords_some_right {x y : Ω} (h : (E.baseChange Ω).toAffine.Nonsingular x y) :
    y ∈ ptCoords E (Point.some x y h) := by
  show y ∈ ({x, y} : Finset Ω); simp

variable (E) in

theorem exists_divisionField {n : ℕ} (hn : (n : F) ≠ 0) :
    ∃ L : IntermediateField F Ω, FiniteDimensional F L ∧ IsGalois F L ∧
      Nat.card {P : (E.baseChange L).toAffine.Point // n • P = 0} = n ^ 2 ∧
      ∀ σ : L ≃ₐ[F] L,
        (∀ P : (E.baseChange L).toAffine.Point, n • P = 0 → Point.map (σ : L →ₐ[F] L) P = P) →
        σ = 1 := by
  classical
  have hnΩ : (n : Ω) ≠ 0 := natCast_ne_zero_of_ne_zero hn

  set T := torsFinset E hnΩ with hT_def
  set Coords : Finset Ω := T.biUnion (ptCoords E) with hCoords_def
  have hsep : ∀ P ∈ T, P ∈ sepPoints E := fun P hP =>
    mem_sepPoints_of_nsmul_eq_zero hn P ((mem_torsFinset hnΩ P).mp hP)
  have hCoordsSep : ∀ z ∈ (Coords : Set Ω), z ∈ separableClosure F Ω := by
    intro z hz
    rw [Finset.mem_coe, hCoords_def, Finset.mem_biUnion] at hz
    obtain ⟨P, hPT, hzP⟩ := hz
    have hPsep := hsep P hPT
    rcases P with _ | ⟨x, y, h⟩
    · exact absurd hzP (Finset.notMem_empty z)
    · rw [some_mem_sepPoints_iff] at hPsep
      have hz' : z ∈ ({x, y} : Finset Ω) := hzP
      rw [Finset.mem_insert, Finset.mem_singleton] at hz'
      rcases hz' with rfl | rfl
      · exact hPsep.1
      · exact hPsep.2

  have hcoT : ∀ {x y : Ω} (h : (E.baseChange Ω).toAffine.Nonsingular x y),
      Point.some x y h ∈ T → x ∈ (Coords : Set Ω) ∧ y ∈ (Coords : Set Ω) := by
    intro x y h hP
    rw [Finset.mem_coe, Finset.mem_coe, hCoords_def, Finset.mem_biUnion, Finset.mem_biUnion]
    exact ⟨⟨_, hP, mem_ptCoords_some_left h⟩, ⟨_, hP, mem_ptCoords_some_right h⟩⟩

  let L : IntermediateField F Ω := IntermediateField.adjoin F (Coords : Set Ω)
  haveI hfin : Finite ((Coords : Set Ω)) := (Finset.finite_toSet Coords).to_subtype
  have hLfd : FiniteDimensional F L :=
    IntermediateField.finiteDimensional_adjoin fun z hz =>
      (mem_separableClosure_iff.mp (hCoordsSep z hz)).isIntegral
  have hLsep : Algebra.IsSeparable F L :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable F Ω).mpr fun z hz =>
      mem_separableClosure_iff.mp (hCoordsSep z hz)

  haveI : Normal F Ω :=
    normal_iff.mpr fun z => ⟨(Algebra.IsAlgebraic.isAlgebraic z).isIntegral, IsAlgClosed.splits _⟩
  have hLnormal : Normal F L := by
    refine IntermediateField.normal_iff_forall_map_le.mpr fun σ => ?_
    show (IntermediateField.adjoin F (Coords : Set Ω)).map σ ≤ IntermediateField.adjoin F (Coords : Set Ω)
    rw [IntermediateField.adjoin_map]
    refine IntermediateField.adjoin.mono F _ _ ?_
    rintro _ ⟨z, hz, rfl⟩
    rw [Finset.mem_coe, hCoords_def, Finset.mem_biUnion] at hz
    obtain ⟨P, hPT, hzP⟩ := hz
    have hσP : Point.map σ P ∈ T := by
      rw [hT_def, mem_torsFinset] at hPT ⊢
      rw [← map_nsmul, hPT, _root_.map_zero]
    rcases P with _ | ⟨x, y, h⟩
    · exact absurd hzP (Finset.notMem_empty z)
    · rw [Point.map_some] at hσP
      have hz' : z ∈ ({x, y} : Finset Ω) := hzP
      rw [Finset.mem_insert, Finset.mem_singleton] at hz'
      rcases hz' with rfl | rfl
      · exact (hcoT _ hσP).1
      · exact (hcoT _ hσP).2
  have hLgal : IsGalois F L := by
    haveI := hLsep; haveI := hLnormal; exact IsGalois.mk

  let f : (E.baseChange L).toAffine.Point →+ (E.baseChange Ω).toAffine.Point :=
    Point.map (IntermediateField.val L)
  have hfinj : Function.Injective f := Point.map_injective _
  have hcard : Nat.card {P : (E.baseChange L).toAffine.Point // n • P = 0} = n ^ 2 := by
    let g : {P : (E.baseChange L).toAffine.Point // n • P = 0} →
        {P : (E.baseChange Ω).toAffine.Point // n • P = 0} :=
      fun P => ⟨f P.1, by rw [← map_nsmul, P.2, _root_.map_zero]⟩
    have hg : Function.Bijective g := by
      constructor
      · intro P₁ P₂ h12
        exact Subtype.ext (hfinj (congrArg Subtype.val h12))
      · rintro ⟨P, hP⟩
        rcases P with _ | ⟨x, y, h⟩
        · exact ⟨⟨0, nsmul_zero _⟩, Subtype.ext (_root_.map_zero f)⟩
        · have hPT : Point.some x y h ∈ T := (mem_torsFinset hnΩ _).mpr hP
          obtain ⟨hxC, hyC⟩ := hcoT h hPT
          have hxL : x ∈ L := IntermediateField.subset_adjoin F _ hxC
          have hyL : y ∈ L := IntermediateField.subset_adjoin F _ hyC
          have h' : (E.baseChange L).toAffine.Nonsingular ⟨x, hxL⟩ ⟨y, hyL⟩ :=
            (Affine.baseChange_nonsingular E (f := IntermediateField.val L)
              Subtype.val_injective ⟨x, hxL⟩ ⟨y, hyL⟩).mp h
          have hfP : f (Point.some _ _ h') = Point.some x y h := by
            show Point.map _ _ = _
            rw [Point.map_some]; rfl
          refine ⟨⟨Point.some _ _ h', hfinj ?_⟩, Subtype.ext hfP⟩
          rw [map_nsmul, _root_.map_zero, hfP, hP]
    rw [Nat.card_congr (Equiv.ofBijective g hg)]
    change Nat.card ({P : (E.baseChange Ω).toAffine.Point | n • P = 0} : Set _) = n ^ 2
    rw [Nat.card_coe_set_eq]
    exact (finite_and_ncard_torsion E hnΩ).2
  refine ⟨L, hLfd, hLgal, hcard, fun σ hσ => ?_⟩

  apply AlgEquiv.ext
  intro z
  rw [AlgEquiv.one_apply]
  obtain ⟨z, hz⟩ := z
  induction hz using IntermediateField.adjoin_induction with
  | mem w hw =>
    rw [Finset.mem_coe, hCoords_def, Finset.mem_biUnion] at hw
    obtain ⟨P, hPT, hwP⟩ := hw
    rcases P with _ | ⟨x, y, h⟩
    · exact absurd hwP (Finset.notMem_empty w)
    · obtain ⟨hxC, hyC⟩ := hcoT h hPT
      have hxL : x ∈ L := IntermediateField.subset_adjoin F _ hxC
      have hyL : y ∈ L := IntermediateField.subset_adjoin F _ hyC
      have h' : (E.baseChange L).toAffine.Nonsingular ⟨x, hxL⟩ ⟨y, hyL⟩ :=
        (Affine.baseChange_nonsingular E (f := IntermediateField.val L)
          Subtype.val_injective ⟨x, hxL⟩ ⟨y, hyL⟩).mp h
      have hPL : n • (Point.some _ _ h' : (E.baseChange L).toAffine.Point) = 0 := by
        apply hfinj
        rw [map_nsmul, _root_.map_zero]
        show n • Point.map _ _ = 0
        rw [Point.map_some]
        exact (mem_torsFinset hnΩ _).mp hPT
      have hfix := hσ _ hPL
      rw [Point.map_some] at hfix
      obtain ⟨hfx, hfy⟩ := Point.some.inj hfix
      have hw' : w ∈ ({x, y} : Finset Ω) := hwP
      rw [Finset.mem_insert, Finset.mem_singleton] at hw'
      rcases hw' with rfl | rfl
      · exact hfx
      · exact hfy
  | algebraMap a => exact σ.commutes a
  | add a b ha hb iha ihb =>
    have : (⟨a + b, IntermediateField.add_mem _ ha hb⟩ : L) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
    rw [this, map_add, iha, ihb]
  | inv a ha iha =>
    have : (⟨a⁻¹, IntermediateField.inv_mem _ ha⟩ : L) = (⟨a, ha⟩ : L)⁻¹ := rfl
    rw [this, map_inv₀, iha]
  | mul a b ha hb iha ihb =>
    have : (⟨a * b, IntermediateField.mul_mem _ ha hb⟩ : L) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [this, map_mul, iha, ihb]

end DivisionField

end P2MKcDivField
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_intermediateField_isGalois_card_torsion_eq_sq.P2MKcDivField"

open P2MKcDivField in
universe u' v' in
theorem solution
    {F : Type u'} {Ω : Type v'} [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic F Ω] [DecidableEq Ω]
    (E : WeierstrassCurve F) [E.IsElliptic] {n : ℕ} (hn : (n : F) ≠ 0) :
    ∃ L : IntermediateField F Ω, FiniteDimensional F L ∧ IsGalois F L ∧
      Nat.card {P : (E.baseChange L).toAffine.Point // n • P = 0} = n ^ 2 ∧
      ∀ σ : L ≃ₐ[F] L,
        (∀ P : (E.baseChange L).toAffine.Point, n • P = 0 → Point.map (σ : L →ₐ[F] L) P = P) →
        σ = 1 :=
  exists_divisionField E hn

end S_WeierstrassCurve_exists_intermediateField_isGalois_card_torsion_eq_sq
end P2MW
export P2MW.S_WeierstrassCurve_exists_intermediateField_isGalois_card_torsion_eq_sq (solution)
