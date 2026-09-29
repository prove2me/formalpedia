-- Prove2me | solution 1 for WeierstrassCurve.exists_isDualPair_of_mem_rationalHomSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/ccde22d2-c571-5e68-8e47-2b6eaba9e6e7

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_DualIsogenyAPI
import Definitions.Def_DualIsogenyExistence
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_exists_frobenius_comp_rational_of_comp_eq_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_rational_verschiebung_of_charP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_isDualPair_of_mem_rationalHomSet
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY a₃ a₁ map mk Affine.Point.some Affine.degree_polynomial Affine.Point.some.inj toAffine Affine.Point Affine.nonsingular_neg Affine.monic_polynomial baseChange j evalEvalBC IsRationallyRepresented rationalHomSet zero_mem_rationalHomSet id_mem_rationalHomSet add_mem_rationalHomSet surjective_of_mem_rationalHomSet card_torsion_of_isAlgClosed exists_frobenius_comp_rational_of_comp_eq_of_mem_rationalHomSet exists_rational_verschiebung_of_charP"
namespace DualRational
p2m_open "WeierstrassCurve"

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k]

noncomputable def bc (x y : k) : F[X][Y] →+* k :=
  (evalEvalRingHom x y).comp (mapRingHom (mapRingHom (algebraMap F k)))

theorem evalEvalBC_eq (p : F[X][Y]) (x y : k) : WeierstrassCurve.evalEvalBC k p x y = bc x y p := rfl

@[scoped simp] theorem bc_CC (x y : k) (a : F) : bc x y (C (C a)) = algebraMap F k a := by
  simp [bc]

@[scoped simp] theorem bc_CX (x y : k) : bc x y (C (X : F[X]) : F[X][Y]) = x := by
  simp [bc]

@[scoped simp] theorem bc_X (x y : k) : bc x y (X : F[X][Y]) = y := by
  simp [bc]

theorem bc_eq_sum (x y : k) (p : F[X][Y]) {Dx Dy : ℕ} (hDy : p.natDegree ≤ Dy)
    (hDx : ∀ j, (p.coeff j).natDegree ≤ Dx) :
    bc x y p = ∑ j ∈ Finset.range (Dy + 1), ∑ i ∈ Finset.range (Dx + 1),
      algebraMap F k ((p.coeff j).coeff i) * x ^ i * y ^ j := by
  have h1 : bc x y p = ((p.map (mapRingHom (algebraMap F k))).eval (C y)).eval x := rfl
  have hdeg : (p.map (mapRingHom (algebraMap F k))).natDegree < Dy + 1 :=
    lt_of_le_of_lt (natDegree_map_le) (Nat.lt_succ_of_le hDy)
  rw [h1, eval_eq_sum_range' hdeg, eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_mul, eval_pow, eval_C, coeff_map, coe_mapRingHom]
  have hdeg' : ((p.coeff j).map (algebraMap F k)).natDegree < Dx + 1 :=
    lt_of_le_of_lt (natDegree_map_le) (Nat.lt_succ_of_le (hDx j))
  rw [eval_eq_sum_range' hdeg', Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_map]

noncomputable def substClear (p n d m e : F[X][Y]) (Dx Dy : ℕ) : F[X][Y] :=
  ∑ j ∈ Finset.range (Dy + 1), ∑ i ∈ Finset.range (Dx + 1),
    C (C ((p.coeff j).coeff i)) * n ^ i * d ^ (Dx - i) * m ^ j * e ^ (Dy - j)

theorem bc_substClear (x y : k) (p n d m e : F[X][Y]) {Dx Dy : ℕ} (hDy : p.natDegree ≤ Dy)
    (hDx : ∀ j, (p.coeff j).natDegree ≤ Dx) (hd : bc x y d ≠ 0) (he : bc x y e ≠ 0) :
    bc x y (substClear p n d m e Dx Dy) =
      bc x y d ^ Dx * bc x y e ^ Dy * bc (bc x y n / bc x y d) (bc x y m / bc x y e) p := by
  rw [bc_eq_sum _ _ p hDy hDx, substClear, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ Dx := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hj' : j ≤ Dy := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  simp only [map_mul, map_pow, bc_CC]
  rw [div_pow, div_pow]
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hi'
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hj'
  rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left, pow_add, pow_add]
  field_simp

noncomputable def degX (p : F[X][Y]) : ℕ :=
  (Finset.range (p.natDegree + 1)).sup fun j => (p.coeff j).natDegree

theorem natDegree_coeff_le_degX (p : F[X][Y]) (j : ℕ) : (p.coeff j).natDegree ≤ degX p := by
  by_cases hj : j ≤ p.natDegree
  · exact Finset.le_sup (f := fun j => (p.coeff j).natDegree)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hj), natDegree_zero]
    exact Nat.zero_le _

section Frob

variable (p : ℕ) [ExpChar F p]

noncomputable def frobPoly (s : ℕ) (P : F[X][Y]) : F[X][Y] :=
  P.map (mapRingHom (iterateFrobenius F p s))

theorem frobPoly_coeff_coeff (s : ℕ) (P : F[X][Y]) (j i : ℕ) :
    ((frobPoly p s P).coeff j).coeff i = ((P.coeff j).coeff i) ^ p ^ s := by
  rw [frobPoly, coeff_map, coe_mapRingHom, coeff_map, iterateFrobenius_def]

theorem natDegree_frobPoly_le (s : ℕ) (P : F[X][Y]) : (frobPoly p s P).natDegree ≤ P.natDegree :=
  natDegree_map_le

theorem natDegree_coeff_frobPoly_le (s : ℕ) (P : F[X][Y]) (j : ℕ) :
    ((frobPoly p s P).coeff j).natDegree ≤ degX P := by
  rw [frobPoly, coeff_map, coe_mapRingHom]
  exact natDegree_map_le.trans (natDegree_coeff_le_degX P j)

theorem bc_pow [ExpChar k p] (x y : k) (P : F[X][Y]) (s : ℕ) :
    bc x y P ^ p ^ s = bc (x ^ p ^ s) (y ^ p ^ s) (frobPoly p s P) := by
  have hL : bc x y P ^ p ^ s = iterateFrobenius k p s (bc x y P) := (iterateFrobenius_def ..).symm
  rw [hL, bc_eq_sum x y P le_rfl (natDegree_coeff_le_degX P), map_sum,
    bc_eq_sum (x ^ p ^ s) (y ^ p ^ s) (frobPoly p s P) (natDegree_frobPoly_le p s P)
      (natDegree_coeff_frobPoly_le p s P)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, map_pow, map_pow, iterateFrobenius_def, iterateFrobenius_def,
    iterateFrobenius_def, frobPoly_coeff_coeff, map_pow]

end Frob

variable [DecidableEq k]

abbrev Pt (k : Type*) [Field k] [Algebra F k] (W : WeierstrassCurve F) :=
  (W.baseChange k).toAffine.Point

section Generic

variable (W : WeierstrassCurve F)

def Good (B : Set k) (P : Pt k W) : Prop :=
  ∃ (x y : k) (h : (W.baseChange k).toAffine.Nonsingular x y), P = .some x y h ∧ x ∉ B

omit [DecidableEq k] in
theorem exists_some_of_eq {Q : Pt k W} {x₁ y₁ : k} {h₁ : (W.baseChange k).toAffine.Nonsingular x₁ y₁}
    (hQ : Q = .some x₁ y₁ h₁) {x₂ y₂ : k} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    ∃ h₂, Q = .some x₂ y₂ h₂ := by
  subst hx hy; exact ⟨h₁, hQ⟩

omit [DecidableEq k] in
theorem finite_setOf_equation (x : k) :
    {y : k | (W.baseChange k).toAffine.Equation x y}.Finite := by
  have hne : ((W.baseChange k).toAffine.polynomial.map (evalRingHom x)) ≠ 0 :=
    (WeierstrassCurve.Affine.monic_polynomial.map _).ne_zero
  refine (Polynomial.finite_setOf_isRoot hne).subset ?_
  intro y hy
  simp only [Set.mem_setOf_eq, IsRoot.def, map_evalRingHom_eval]
  exact hy

omit [DecidableEq k] in
theorem finite_not_good {B : Set k} (hB : B.Finite) : {P : Pt k W | ¬ Good W B P}.Finite := by
  have hfin : (insert (0 : Pt k W) (⋃ x ∈ B, ⋃ y ∈ {y : k | (W.baseChange k).toAffine.Equation x y},
      {P : Pt k W | ∃ h : (W.baseChange k).toAffine.Nonsingular x y, P = .some x y h})).Finite := by
    refine Set.Finite.insert _ (Set.Finite.biUnion hB fun x _ => ?_)
    refine Set.Finite.biUnion (finite_setOf_equation (k := k) W x) fun y _ => ?_
    refine Set.Subsingleton.finite ?_
    rintro P ⟨h1, rfl⟩ Q ⟨h2, rfl⟩
    rfl
  refine hfin.subset ?_
  intro P hP
  simp only [Set.mem_setOf_eq, Good, not_exists, not_and, not_not] at hP
  rcases P with _ | ⟨x, y, h⟩
  · exact Set.mem_insert _ _
  · refine Set.mem_insert_of_mem _ ?_
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨x, hP x y h rfl, y, h.left, h, rfl⟩

omit [DecidableEq k] in
theorem infinite_point [IsAlgClosed k] [W.IsElliptic] : Infinite (Pt k W) := by
  haveI : (W.baseChange k).IsElliptic :=
    (inferInstance : (W.map (algebraMap F k)).IsElliptic)
  have hy : ∀ x : k, ∃ y : k, (W.baseChange k).toAffine.Nonsingular x y := by
    intro x
    have hdeg : ((W.baseChange k).toAffine.polynomial.map (evalRingHom x)).degree ≠ 0 := by
      rw [WeierstrassCurve.Affine.monic_polynomial.degree_map,
        WeierstrassCurve.Affine.degree_polynomial]
      norm_num
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg
    refine ⟨y, ((W.baseChange k).toAffine.equation_iff_nonsingular).mp ?_⟩
    rw [IsRoot.def, map_evalRingHom_eval] at hy
    exact hy
  choose f hf using hy
  refine Infinite.of_injective (fun x : k => (Affine.Point.some x (f x) (hf x) : Pt k W)) ?_
  intro x x' hxx'
  exact (WeierstrassCurve.Affine.Point.some.inj hxx').left

def xc : Pt k W → k
  | .zero => 0
  | .some x _ _ => x

end Generic

variable {W₁ W₂ W₃ : WeierstrassCurve F}

def Repr (α : Pt k W₁ →+ Pt k W₂) (nX dX nY dY : F[X][Y]) (B : Set k) : Prop :=
  ∀ (x y : k) (h : (W₁.baseChange k).toAffine.Nonsingular x y), x ∉ B →
    bc x y dX ≠ 0 ∧ bc x y dY ≠ 0 ∧
      ∃ h', α (.some x y h) = .some (bc x y nX / bc x y dX) (bc x y nY / bc x y dY) h'

theorem isRationallyRepresented_iff (α : Pt k W₁ →+ Pt k W₂) :
    IsRationallyRepresented k W₁ W₂ α ↔
      ∃ (nX dX nY dY : F[X][Y]) (B : Set k), B.Finite ∧ Repr α nX dX nY dY B := Iff.rfl

theorem ker_subset_not_good {α : Pt k W₁ →+ Pt k W₂} {nX dX nY dY : F[X][Y]} {B : Set k}
    (hrep : Repr α nX dX nY dY B) : {P | α P = 0} ⊆ {P | ¬ Good W₁ B P} := by
  rintro P (hP : α P = 0) ⟨x, y, h, rfl, hx⟩
  obtain ⟨-, -, h', hP'⟩ := hrep x y h hx
  rw [hP'] at hP
  exact absurd hP (by rintro ⟨⟩)

theorem finite_ker {α : Pt k W₁ →+ Pt k W₂} (hα : IsRationallyRepresented k W₁ W₂ α) :
    {P | α P = 0}.Finite := by
  obtain ⟨nX, dX, nY, dY, B, hB, hrep⟩ := hα
  exact (finite_not_good W₁ hB).subset (ker_subset_not_good hrep)

omit [DecidableEq k] in

theorem finite_preimage {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (hker : {a | f a = 0}.Finite) {T : Set B} (hT : T.Finite) : (f ⁻¹' T).Finite := by
  have hT' : f ⁻¹' T = ⋃ t ∈ T, f ⁻¹' {t} := by
    ext a; simp
  rw [hT']
  refine hT.biUnion fun t _ => ?_
  by_cases ht : ∃ a, f a = t
  · obtain ⟨a, rfl⟩ := ht
    refine (hker.image fun c => a + c).subset ?_
    intro b hb
    refine ⟨b - a, ?_, by simp⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hb
    simp [map_sub, hb]
  · refine Set.finite_empty.subset ?_
    intro b hb
    exact ht ⟨b, hb⟩

theorem neg_mem_rationalHomSet {α : Pt k W₁ →+ Pt k W₂} (hα : α ∈ rationalHomSet k W₁ W₂) :
    -α ∈ rationalHomSet k W₁ W₂ := by
  rcases hα with rfl | ⟨nX, dX, nY, dY, B, hB, hrep⟩
  · rw [neg_zero]; exact zero_mem_rationalHomSet k W₁ W₂
  refine Or.inr ⟨nX, dX, -(nY * dX) - C (C W₂.a₁) * nX * dY - C (C W₂.a₃) * dX * dY, dY * dX,
    B, hB, ?_⟩
  intro x y h hx
  obtain ⟨hdX, hdY, h', hP⟩ := hrep x y h hx
  simp only [evalEvalBC_eq] at hdX hdY hP ⊢
  refine ⟨hdX, by rw [map_mul]; exact mul_ne_zero hdY hdX, ?_⟩
  have hneg : (-α) (.some x y h) =
      .some (bc x y nX / bc x y dX)
        ((W₂.baseChange k).toAffine.negY (bc x y nX / bc x y dX) (bc x y nY / bc x y dY))
        ((Affine.nonsingular_neg ..).mpr h') := by
    rw [AddMonoidHom.neg_apply, hP]; rfl
  refine exists_some_of_eq W₂ hneg rfl ?_
  simp only [Affine.negY, map_sub, map_neg, map_mul, bc_CC]
  change -(bc x y nY / bc x y dY) - algebraMap F k W₂.a₁ * (bc x y nX / bc x y dX)
      - algebraMap F k W₂.a₃ = _
  field_simp

theorem sub_mem_rationalHomSet [IsAlgClosed k] [W₁.IsElliptic] [W₂.IsElliptic]
    {α β : Pt k W₁ →+ Pt k W₂} (hα : α ∈ rationalHomSet k W₁ W₂)
    (hβ : β ∈ rationalHomSet k W₁ W₂) : α - β ∈ rationalHomSet k W₁ W₂ := by
  rw [sub_eq_add_neg]
  exact add_mem_rationalHomSet k W₁ W₂ hα (neg_mem_rationalHomSet hβ)

theorem zsmul_mem_rationalHomSet [IsAlgClosed k] [W₁.IsElliptic] [W₂.IsElliptic]
    {α : Pt k W₁ →+ Pt k W₂} (hα : α ∈ rationalHomSet k W₁ W₂) (c : ℤ) :
    c • α ∈ rationalHomSet k W₁ W₂ := by
  induction c using Int.induction_on with
  | zero => rw [zero_zsmul]; exact zero_mem_rationalHomSet k W₁ W₂
  | succ n ih => rw [add_zsmul, one_zsmul]; exact add_mem_rationalHomSet k W₁ W₂ ih hα
  | pred n ih => rw [sub_zsmul, one_zsmul]; exact sub_mem_rationalHomSet ih hα

section Torsion

variable [IsAlgClosed k] (W : WeierstrassCurve F) [W.IsElliptic]

theorem exists_ne_zero_smul_eq_zero {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓk : (ℓ : k) ≠ 0) :
    ∃ Q : Pt k W, Q ≠ 0 ∧ (ℓ : ℤ) • Q = 0 := by
  have hcard : Nat.card (Submodule.torsionBy ℤ (Pt k W) (ℓ : ℤ)) = ℓ ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed (K := k) W hℓk
  haveI : Finite (Submodule.torsionBy ℤ (Pt k W) (ℓ : ℤ)) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hcard]; exact pow_ne_zero 2 hℓ.ne_zero
  have hnt : Nontrivial (Submodule.torsionBy ℤ (Pt k W) (ℓ : ℤ)) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    exact Nat.one_lt_pow two_ne_zero hℓ.one_lt
  obtain ⟨⟨Q, hQ⟩, hQ0⟩ := exists_ne (0 : Submodule.torsionBy ℤ (Pt k W) (ℓ : ℤ))
  refine ⟨Q, fun h => hQ0 (Subtype.ext h), ?_⟩
  exact (Submodule.mem_torsionBy_iff _ _).mp hQ

theorem smul_id_ne_zero {n : ℤ} (hn : n ≠ 0) : (n • AddMonoidHom.id (Pt k W)) ≠ 0 := by
  intro hzero
  obtain ⟨ℓ, hℓle, hℓ⟩ := Nat.exists_infinite_primes (max n.natAbs (ringChar k) + 1)
  have hℓn : n.natAbs < ℓ := lt_of_lt_of_le (Nat.lt_succ_of_le (le_max_left _ _)) hℓle
  have hℓc : ringChar k < ℓ := lt_of_lt_of_le (Nat.lt_succ_of_le (le_max_right _ _)) hℓle
  have hℓk : (ℓ : k) ≠ 0 := by
    intro h0
    have hdvd : ringChar k ∣ ℓ := (CharP.cast_eq_zero_iff k (ringChar k) ℓ).mp h0
    rcases (Nat.dvd_prime hℓ).mp hdvd with h1 | h2
    · exact CharP.ringChar_ne_one h1
    · exact absurd h2 hℓc.ne
  obtain ⟨Q, hQ0, hQℓ⟩ := exists_ne_zero_smul_eq_zero (k := k) W hℓ hℓk
  have hQn : n • Q = 0 := by
    have := DFunLike.congr_fun hzero Q
    rwa [AddMonoidHom.zsmul_apply, AddMonoidHom.id_apply, AddMonoidHom.zero_apply] at this
  have hnd : ¬ (ℓ : ℤ) ∣ n := by
    intro hd
    rw [Int.natCast_dvd] at hd
    exact absurd (Nat.le_of_dvd (Int.natAbs_pos.mpr hn) hd) (not_le.mpr hℓn)
  have hcop : IsCoprime (ℓ : ℤ) n :=
    (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hℓ).irreducible).mpr hnd
  obtain ⟨a, b, hab⟩ := hcop
  apply hQ0
  calc Q = (a * (ℓ : ℤ) + b * n) • Q := by rw [hab, one_smul]
    _ = 0 := by rw [add_smul, mul_smul, mul_smul, hQℓ, hQn, smul_zero, smul_zero, add_zero]

theorem finite_torsion {n : ℤ} (hn : n ≠ 0) : {P : Pt k W | n • P = 0}.Finite := by
  have hid : (n • AddMonoidHom.id (Pt k W)) ∈ rationalHomSet k W W :=
    zsmul_mem_rationalHomSet (id_mem_rationalHomSet k W) n
  have hrep : IsRationallyRepresented k W W (n • AddMonoidHom.id (Pt k W)) :=
    hid.resolve_left (smul_id_ne_zero (k := k) W hn)
  refine (finite_ker hrep).subset ?_
  intro P hP
  show (n • AddMonoidHom.id (Pt k W)) P = 0
  rw [AddMonoidHom.zsmul_apply, AddMonoidHom.id_apply]
  exact hP

end Torsion

def Stage (μ : Pt k W₂ →+ Pt k W₁) (m : ℕ) : Prop :=
  ∃ (nX dX nY dY : F[X][Y]) (B : Set k), B.Finite ∧
    ∀ (x y : k) (h : (W₂.baseChange k).toAffine.Nonsingular x y), x ∉ B →
      bc x y dX ≠ 0 ∧ bc x y dY ≠ 0 ∧
        ∃ (x' y' : k) (h' : (W₁.baseChange k).toAffine.Nonsingular x' y'),
          μ (.some x y h) = .some x' y' h' ∧
            x' ^ m = bc x y nX / bc x y dX ∧ y' ^ m = bc x y nY / bc x y dY

def Ver (W : WeierstrassCurve F) (p : ℕ) : Prop :=
  ∃ (nX dX nY dY : F[X][Y]) (B : Set k), B.Finite ∧
    ∀ (x y : k) (h : (W.baseChange k).toAffine.Nonsingular x y), x ∉ B →
      bc (x ^ p) (y ^ p) dX ≠ 0 ∧ bc (x ^ p) (y ^ p) dY ≠ 0 ∧
        ∃ h', (p : ℤ) • (Affine.Point.some x y h : Pt k W) =
          .some (bc (x ^ p) (y ^ p) nX / bc (x ^ p) (y ^ p) dX)
            (bc (x ^ p) (y ^ p) nY / bc (x ^ p) (y ^ p) dY) h'

theorem stage_one_mem {μ : Pt k W₂ →+ Pt k W₁} (hμ : Stage (k := k) μ 1) :
    μ ∈ rationalHomSet k W₂ W₁ := by
  obtain ⟨nX, dX, nY, dY, B, hB, hrep⟩ := hμ
  refine Or.inr ⟨nX, dX, nY, dY, B, hB, fun x y h hx => ?_⟩
  obtain ⟨hdX, hdY, x', y', h', hP, hx', hy'⟩ := hrep x y h hx
  rw [pow_one] at hx' hy'
  exact ⟨hdX, hdY, exists_some_of_eq W₁ hP hx' hy'⟩

theorem ver_one (W : WeierstrassCurve F) : Ver (k := k) W 1 := by
  refine ⟨C (X : F[X]), 1, (X : F[X][Y]), 1, ∅, Set.finite_empty, fun x y h _ => ?_⟩
  simp only [pow_one, map_one, Nat.cast_one, one_smul, bc_CX, bc_X, div_one]
  exact ⟨one_ne_zero, one_ne_zero, h, trivial⟩

theorem ver_ringExpChar [IsAlgClosed k] (W : WeierstrassCurve F) [W.IsElliptic] :
    Ver (k := k) W (ringExpChar F) := by
  rcases CharP.char_is_prime_or_zero F (ringChar F) with hp | h0
  · haveI := Fact.mk hp
    have hq : ringExpChar F = ringChar F := by
      rw [ringExpChar]; exact Nat.max_eq_left hp.one_lt.le
    rw [hq]
    obtain ⟨nX, dX, nY, dY, B, hB, hrep⟩ :=
      WeierstrassCurve.exists_rational_verschiebung_of_charP (F := F) (ringChar F) k W
    refine ⟨nX, dX, nY, dY, B, hB, fun x y h hx => ?_⟩
    obtain ⟨h1, h2, h', hP⟩ := hrep x y h hx
    refine ⟨h1, h2, h', ?_⟩
    rw [natCast_zsmul]
    exact hP
  · have hq : ringExpChar F = 1 := by
      rw [ringExpChar, h0]; rfl
    rw [hq]
    exact ver_one W

section Step

variable (p : ℕ) [ExpChar F p] [ExpChar k p]

theorem stage_step {μ : Pt k W₂ →+ Pt k W₁} {s : ℕ} (hμ : Stage (k := k) μ (p * p ^ s))
    (hV : Ver (k := k) W₁ p) (hker : {Q | μ Q = 0}.Finite) :
    Stage (k := k) ((p : ℤ) • μ) (p ^ s) := by
  obtain ⟨nX, dX, nY, dY, B, hB, hrep⟩ := hμ
  obtain ⟨vX, eX, vY, eY, Bv, hBv, hv⟩ := hV
  have hT : {Q : Pt k W₁ | ¬ Good W₁ Bv Q}.Finite := finite_not_good W₁ hBv
  have hB' : (B ∪ xc W₂ '' (μ ⁻¹' {Q : Pt k W₁ | ¬ Good W₁ Bv Q})).Finite :=
    hB.union ((finite_preimage μ hker hT).image _)
  set Dx := max (degX vX) (degX eX) with hDx
  set Dy := max vX.natDegree eX.natDegree with hDy
  set Dx' := max (degX vY) (degX eY) with hDx'
  set Dy' := max vY.natDegree eY.natDegree with hDy'
  refine ⟨substClear (frobPoly p s vX) nX dX nY dY Dx Dy, substClear (frobPoly p s eX) nX dX nY dY Dx Dy,
    substClear (frobPoly p s vY) nX dX nY dY Dx' Dy', substClear (frobPoly p s eY) nX dX nY dY Dx' Dy',
    B ∪ xc W₂ '' (μ ⁻¹' {Q : Pt k W₁ | ¬ Good W₁ Bv Q}), hB', ?_⟩
  intro x y h hx
  have hx₁ : x ∉ B := fun h' => hx (Or.inl h')
  obtain ⟨hdX, hdY, x', y', h', hμP, hx', hy'⟩ := hrep x y h hx₁
  have hgood : Good W₁ Bv (μ (.some x y h)) := by
    by_contra hng
    exact hx (Or.inr ⟨.some x y h, hng, rfl⟩)
  obtain ⟨x'', y'', h'', hμP2, hxv⟩ := hgood
  rw [hμP] at hμP2
  obtain ⟨hxe, hye⟩ := Affine.Point.some.inj hμP2
  subst hxe hye
  obtain ⟨heX, heY, h₃, hpP⟩ := hv x' y' h' hxv

  have bX : ∀ j, ((frobPoly p s vX).coeff j).natDegree ≤ Dx :=
    fun j => (natDegree_coeff_frobPoly_le p s vX j).trans (le_max_left _ _)
  have bX' : ∀ j, ((frobPoly p s eX).coeff j).natDegree ≤ Dx :=
    fun j => (natDegree_coeff_frobPoly_le p s eX j).trans (le_max_right _ _)
  have bY : ∀ j, ((frobPoly p s vY).coeff j).natDegree ≤ Dx' :=
    fun j => (natDegree_coeff_frobPoly_le p s vY j).trans (le_max_left _ _)
  have bY' : ∀ j, ((frobPoly p s eY).coeff j).natDegree ≤ Dx' :=
    fun j => (natDegree_coeff_frobPoly_le p s eY j).trans (le_max_right _ _)
  have EnX := bc_substClear x y (frobPoly p s vX) nX dX nY dY (Dx := Dx) (Dy := Dy)
    ((natDegree_frobPoly_le p s vX).trans (le_max_left _ _)) bX hdX hdY
  have EdX := bc_substClear x y (frobPoly p s eX) nX dX nY dY (Dx := Dx) (Dy := Dy)
    ((natDegree_frobPoly_le p s eX).trans (le_max_right _ _)) bX' hdX hdY
  have EnY := bc_substClear x y (frobPoly p s vY) nX dX nY dY (Dx := Dx') (Dy := Dy')
    ((natDegree_frobPoly_le p s vY).trans (le_max_left _ _)) bY hdX hdY
  have EdY := bc_substClear x y (frobPoly p s eY) nX dX nY dY (Dx := Dx') (Dy := Dy')
    ((natDegree_frobPoly_le p s eY).trans (le_max_right _ _)) bY' hdX hdY

  have hfrob : ∀ P : F[X][Y], bc (x' ^ p) (y' ^ p) P ^ p ^ s =
      bc (bc x y nX / bc x y dX) (bc x y nY / bc x y dY) (frobPoly p s P) := by
    intro P
    rw [bc_pow p, ← pow_mul, ← pow_mul, hx', hy']
  have c1 : bc x y dX ^ Dx * bc x y dY ^ Dy ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hdX) (pow_ne_zero _ hdY)
  have c2 : bc x y dX ^ Dx' * bc x y dY ^ Dy' ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hdX) (pow_ne_zero _ hdY)
  have hfeX : bc (bc x y nX / bc x y dX) (bc x y nY / bc x y dY) (frobPoly p s eX) ≠ 0 := by
    rw [← hfrob]; exact pow_ne_zero _ heX
  have hfeY : bc (bc x y nX / bc x y dX) (bc x y nY / bc x y dY) (frobPoly p s eY) ≠ 0 := by
    rw [← hfrob]; exact pow_ne_zero _ heY
  have hval : ((p : ℤ) • μ) (.some x y h) = .some _ _ h₃ := by
    rw [AddMonoidHom.zsmul_apply, hμP]; exact hpP
  refine ⟨?_, ?_, _, _, h₃, hval, ?_, ?_⟩
  · rw [EdX]; exact mul_ne_zero c1 hfeX
  · rw [EdY]; exact mul_ne_zero c2 hfeY
  · rw [div_pow, hfrob, hfrob, EnX, EdX]; exact (mul_div_mul_left _ _ c1).symm
  · rw [div_pow, hfrob, hfrob, EnY, EdY]; exact (mul_div_mul_left _ _ c2).symm

variable [IsAlgClosed k] [W₁.IsElliptic]

theorem stage_iterate (hV : Ver (k := k) W₁ p) (hp : 0 < p) :
    ∀ (t : ℕ) (μ : Pt k W₂ →+ Pt k W₁), Stage (k := k) μ (p ^ t) → {Q | μ Q = 0}.Finite →
      Stage (k := k) (((p ^ t : ℕ) : ℤ) • μ) 1
  | 0, μ, hμ, _ => by
    rw [pow_zero, Nat.cast_one, one_smul]
    rwa [pow_zero] at hμ
  | t + 1, μ, hμ, hker => by
    rw [pow_succ'] at hμ
    have hstep := stage_step p hμ hV hker
    have hker' : {Q | ((p : ℤ) • μ) Q = 0}.Finite := by
      have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
      refine (finite_preimage μ hker (finite_torsion (k := k) W₁ hp0)).subset ?_
      intro Q hQ
      simp only [Set.mem_setOf_eq, AddMonoidHom.zsmul_apply] at hQ
      exact hQ
    have hIH := stage_iterate hV hp t ((p : ℤ) • μ) hstep hker'
    rw [smul_smul] at hIH
    convert hIH using 3
    rfl

end Step

theorem main [IsAlgClosed k] (W₁ W₂ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic]
    {ρ : Pt k W₁ →+ Pt k W₂} (hρ : ρ ∈ rationalHomSet k W₁ W₂) (hρ0 : ρ ≠ 0) :
    ∃ σ ∈ rationalHomSet k W₂ W₁, ∃ n : ℤ, 0 < n ∧ AddMonoidHom.IsDualPair ρ σ n := by

  have hrepρ : IsRationallyRepresented k W₁ W₂ ρ := hρ.resolve_left hρ0
  have hkerfin : {P | ρ P = 0}.Finite := finite_ker hrepρ
  haveI : Finite ρ.ker := by
    rw [← SetLike.coe_sort_coe, Set.finite_coe_iff]
    exact hkerfin.subset fun P hP => AddMonoidHom.mem_ker.mp hP
  set n₀ : ℕ := Nat.card ρ.ker with hn₀def
  have hn₀ : 0 < n₀ := Nat.card_pos
  have hn₀z : (n₀ : ℤ) ≠ 0 := by exact_mod_cast hn₀.ne'
  have hker : ∀ a, ρ a = 0 → (n₀ : ℤ) • a = 0 := by
    intro a ha
    have h := card_nsmul_eq_zero' (G := ρ.ker) (x := ⟨a, AddMonoidHom.mem_ker.mpr ha⟩)
    rw [natCast_zsmul]
    have h' := congrArg (fun z : ρ.ker => (z : Pt k W₁)) h
    simp at h'
    exact h'

  have hsurj : Function.Surjective ρ := WeierstrassCurve.surjective_of_mem_rationalHomSet k hρ hρ0
  obtain ⟨σ₀, hpair₀⟩ :=
    AddMonoidHom.exists_isDualPair_of_surjective_of_ker_le ρ hsurj (n₀ : ℤ) hker

  have hψ : ((n₀ : ℤ) • AddMonoidHom.id (Pt k W₁)) ∈ rationalHomSet k W₁ W₁ :=
    zsmul_mem_rationalHomSet (id_mem_rationalHomSet k W₁) _
  have hψ0 : ((n₀ : ℤ) • AddMonoidHom.id (Pt k W₁)) ≠ 0 := smul_id_ne_zero (k := k) W₁ hn₀z
  have hμ : σ₀.comp ρ = (n₀ : ℤ) • AddMonoidHom.id (Pt k W₁) := by
    ext P
    rw [AddMonoidHom.comp_apply, hpair₀.comp_left P, AddMonoidHom.zsmul_apply,
      AddMonoidHom.id_apply]
  obtain ⟨t, nX, dX, nY, dY, B, hB, hS⟩ :=
    WeierstrassCurve.exists_frobenius_comp_rational_of_comp_eq_of_mem_rationalHomSet k W₁ W₂ W₁
      hρ hψ hψ0 hμ
  have hstage : Stage (k := k) σ₀ (ringExpChar F ^ t) :=
    ⟨nX, dX, nY, dY, B, hB, fun x y h hx => hS x y h hx⟩

  have hkerσ : {Q | σ₀ Q = 0}.Finite :=
    (finite_torsion (k := k) W₂ hn₀z).subset fun Q hQ => hpair₀.ker_le_torsion_left hQ
  haveI : ExpChar k (ringExpChar F) := expChar_of_injective_ringHom (algebraMap F k).injective _
  have hq : 0 < ringExpChar F := lt_of_lt_of_le Nat.one_pos (le_max_right _ _)
  have hfinal := stage_iterate (k := k) (W₁ := W₁) (W₂ := W₂) (ringExpChar F)
    (ver_ringExpChar (k := k) W₁) hq t σ₀ hstage hkerσ

  refine ⟨(((ringExpChar F ^ t : ℕ) : ℤ)) • σ₀, stage_one_mem hfinal,
    ((ringExpChar F ^ t : ℕ) : ℤ) * n₀, ?_, ⟨fun a => ?_, fun b => ?_⟩⟩
  · exact mul_pos (by exact_mod_cast pow_pos hq t) (by exact_mod_cast hn₀)
  · rw [AddMonoidHom.zsmul_apply, hpair₀.comp_left, smul_smul]
  · rw [AddMonoidHom.zsmul_apply, map_zsmul, hpair₀.comp_right, smul_smul]

end WeierstrassCurve.DualRational
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_isDualPair_of_mem_rationalHomSet.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_isDualPair_of_mem_rationalHomSet.WeierstrassCurve.DualRational"
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_isDualPair_of_mem_rationalHomSet.WeierstrassCurve"

theorem solution {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k] (W₁ W₂ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic] {ρ : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point} (hρ : ρ ∈ WeierstrassCurve.rationalHomSet k W₁ W₂) (hρ0 : ρ ≠ 0) : ∃ σ ∈ WeierstrassCurve.rationalHomSet k W₂ W₁, ∃ n : ℤ, 0 < n ∧ AddMonoidHom.IsDualPair ρ σ n :=
  WeierstrassCurve.DualRational.main W₁ W₂ hρ hρ0

end S_WeierstrassCurve_exists_isDualPair_of_mem_rationalHomSet
end P2MW
export P2MW.S_WeierstrassCurve_exists_isDualPair_of_mem_rationalHomSet (solution)
