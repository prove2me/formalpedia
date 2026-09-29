-- Prove2me | solution 1 for WeierstrassCurve.relIndex_annihilator_eq_sq_natCard_and_mem_of_forall_apply_torsion_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/60dd141a-199a-5568-94b2-b935cc1c1de7

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_DualIsogenyAPI
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_isDualPair_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_QuaternionAlgebra_IsOrder_finrank_eq_four
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_relIndex_annihilator_eq_sq_natCard_and_mem_of_forall_apply_torsion_eq_zero
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Quaternion
open QuaternionAlgebra

noncomputable section

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY a₃ a₁ map mk Affine.Point.some Affine.degree_polynomial Affine.Point.some.inj reduction toAffine Affine.Point Affine.nonsingular_neg Affine.monic_polynomial baseChange evalEvalBC IsRationallyRepresented rationalHomSet rationalEndSubring zero_mem_rationalHomSet id_mem_rationalHomSet comp_mem_rationalHomSet add_mem_rationalHomSet surjective_of_mem_rationalHomSet exists_isDualPair_of_mem_rationalHomSet exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero card_torsion_of_isAlgClosed"
namespace HomModuleAtPrime
p2m_open "WeierstrassCurve"

section Points

open Polynomial
open scoped Polynomial.Bivariate

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k]

def bc (x y : k) : F[X][Y] →+* k :=
  (evalEvalRingHom x y).comp (mapRingHom (mapRingHom (algebraMap F k)))

theorem evalEvalBC_eq (p : F[X][Y]) (x y : k) : WeierstrassCurve.evalEvalBC k p x y = bc x y p := rfl

@[scoped simp] theorem bc_CC (x y : k) (a : F) : bc x y (C (C a)) = algebraMap F k a := by
  simp [bc]

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

end Generic

variable {W₁ W₂ : WeierstrassCurve F}

theorem finite_ker {α : Pt k W₁ →+ Pt k W₂} (hα : IsRationallyRepresented k W₁ W₂ α) :
    {P | α P = 0}.Finite := by
  obtain ⟨nX, dX, nY, dY, B, hB, hrep⟩ := hα
  refine (finite_not_good W₁ hB).subset ?_
  rintro P (hP : α P = 0) ⟨x, y, h, rfl, hx⟩
  obtain ⟨-, -, h', hP'⟩ := hrep x y h hx
  rw [hP'] at hP
  exact absurd hP (by rintro ⟨⟩)

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

theorem nsmul_mem_rationalHomSet [IsAlgClosed k] [W₁.IsElliptic] [W₂.IsElliptic]
    {α : Pt k W₁ →+ Pt k W₂} (hα : α ∈ rationalHomSet k W₁ W₂) (c : ℕ) :
    c • α ∈ rationalHomSet k W₁ W₂ := by
  rw [← natCast_zsmul]; exact zsmul_mem_rationalHomSet hα c

theorem mem_rationalHomSet_of_mem_end [IsAlgClosed k] {W : WeierstrassCurve F} [W.IsElliptic]
    {φ : AddMonoid.End (Pt k W)} (hφ : φ ∈ rationalEndSubring k W) :
    (φ : Pt k W →+ Pt k W) ∈ rationalHomSet k W W := by
  induction hφ using Subring.closure_induction with
  | mem x hx => exact hx
  | zero => exact zero_mem_rationalHomSet k W W
  | one => exact id_mem_rationalHomSet k W
  | add x y _ _ hx hy => exact add_mem_rationalHomSet k W W hx hy
  | neg x _ hx => exact neg_mem_rationalHomSet hx
  | mul x y _ _ hx hy => exact comp_mem_rationalHomSet k W W W hy hx

theorem eq_zero_of_finite_range [IsAlgClosed k] [W₁.IsElliptic] [W₂.IsElliptic]
    {α : Pt k W₁ →+ Pt k W₂} (hα : α ∈ rationalHomSet k W₁ W₂) (hfin : (Set.range α).Finite) :
    α = 0 := by
  by_contra hα0
  have hsurj := WeierstrassCurve.surjective_of_mem_rationalHomSet k hα hα0
  haveI := infinite_point (k := k) W₂
  rw [hsurj.range_eq] at hfin
  exact Set.infinite_univ hfin

theorem exists_ne_zero_smul_eq_zero [IsAlgClosed k] (W : WeierstrassCurve F) [W.IsElliptic]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓk : (ℓ : k) ≠ 0) :
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

theorem smul_id_ne_zero [IsAlgClosed k] (W : WeierstrassCurve F) [W.IsElliptic] {n : ℤ} (hn : n ≠ 0) :
    (n • AddMonoidHom.id (Pt k W)) ≠ 0 := by
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

end Points

section Torsion

variable {κ : Type*} [Field κ] [DecidableEq κ]

def tors (W : WeierstrassCurve κ) (ℓ : ℕ) : AddSubgroup (Pt κ W) :=
  (Submodule.torsionBy ℤ (Pt κ W) (ℓ : ℤ)).toAddSubgroup

variable {W X₀ : WeierstrassCurve κ} {ℓ : ℕ}

theorem mem_tors_iff {P : Pt κ W} : P ∈ tors W ℓ ↔ (ℓ : ℤ) • P = 0 :=
  Submodule.mem_torsionBy_iff _ _

theorem natCard_tors [IsAlgClosed κ] (W : WeierstrassCurve κ) [W.IsElliptic] (hℓκ : (ℓ : κ) ≠ 0) :
    Nat.card (tors W ℓ) = ℓ ^ 2 :=
  WeierstrassCurve.card_torsion_of_isAlgClosed (K := κ) W hℓκ

theorem finite_tors [IsAlgClosed κ] (W : WeierstrassCurve κ) [W.IsElliptic] (hℓ : ℓ ≠ 0)
    (hℓκ : (ℓ : κ) ≠ 0) : Finite (tors W ℓ) := by
  refine Nat.finite_of_card_ne_zero ?_
  rw [natCard_tors W hℓκ]; exact pow_ne_zero 2 hℓ

theorem nsmul_eq_zero_of_mem_tors {P : Pt κ W} (hP : P ∈ tors W ℓ) : ℓ • P = 0 := by
  rw [← natCast_zsmul]; exact mem_tors_iff.mp hP

scoped instance moduleTors (W : WeierstrassCurve κ) (ℓ : ℕ) : Module (ZMod ℓ) (tors W ℓ) :=
  AddCommGroup.zmodModule fun x => Subtype.ext (by
    change ℓ • (x : Pt κ W) = 0
    exact nsmul_eq_zero_of_mem_tors x.2)

theorem finrank_tors [IsAlgClosed κ] (W : WeierstrassCurve κ) [W.IsElliptic] [Fact ℓ.Prime]
    (hℓκ : (ℓ : κ) ≠ 0) : Module.finrank (ZMod ℓ) (tors W ℓ) = 2 := by
  have hℓ : ℓ.Prime := Fact.out
  haveI := finite_tors W hℓ.ne_zero hℓκ
  haveI : Module.Finite (ZMod ℓ) (tors W ℓ) := Module.Finite.of_finite
  have h := Module.natCard_eq_pow_finrank (K := ZMod ℓ) (V := tors W ℓ)
  rw [natCard_tors W hℓκ, Nat.card_zmod] at h
  exact (Nat.pow_right_injective hℓ.two_le h).symm

def res (W X₀ : WeierstrassCurve κ) (ℓ : ℕ) : (Pt κ W →+ Pt κ X₀) →+ (tors W ℓ →+ tors X₀ ℓ) where
  toFun ρ := (ρ.comp (tors W ℓ).subtype).codRestrict (tors X₀ ℓ) fun P => by
    rw [mem_tors_iff, AddMonoidHom.coe_comp, Function.comp_apply, AddSubgroup.coe_subtype,
      ← map_zsmul, mem_tors_iff.mp P.2, map_zero]
  map_zero' := by ext; rfl
  map_add' _ _ := by ext; rfl

@[scoped simp] theorem res_apply (ρ : Pt κ W →+ Pt κ X₀) (P : tors W ℓ) : ((res W X₀ ℓ ρ P : tors X₀ ℓ) : Pt κ X₀) = ρ P :=
  rfl

theorem res_eq_zero_iff (ρ : Pt κ W →+ Pt κ X₀) :
    res W X₀ ℓ ρ = 0 ↔ ∀ P : Pt κ W, (ℓ : ℤ) • P = 0 → ρ P = 0 := by
  constructor
  · intro h P hP
    have := DFunLike.congr_fun h ⟨P, mem_tors_iff.mpr hP⟩
    exact congrArg Subtype.val this
  · intro h
    ext P
    exact h P (mem_tors_iff.mp P.2)

theorem res_nsmul_eq_zero (ρ : Pt κ W →+ Pt κ X₀) : res W X₀ ℓ (ℓ • ρ) = 0 := by
  rw [res_eq_zero_iff]
  intro P hP
  rw [AddMonoidHom.nsmul_apply, ← natCast_zsmul, ← map_zsmul, hP, map_zero]

theorem exists_eq_nsmul_of_res_eq_zero [IsAlgClosed κ] [W.IsElliptic] [X₀.IsElliptic] (hℓκ : (ℓ : κ) ≠ 0)
    {ρ : Pt κ W →+ Pt κ X₀} (hρ : ρ ∈ rationalHomSet κ W X₀) (h0 : res W X₀ ℓ ρ = 0) :
    ∃ β ∈ rationalHomSet κ W X₀, ρ = ℓ • β := by
  obtain ⟨β, hβ, hβeq⟩ := WeierstrassCurve.exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero κ W X₀
    hℓκ hρ ((res_eq_zero_iff ρ).mp h0)
  refine ⟨β, hβ, ?_⟩
  ext P
  rw [hβeq P, AddMonoidHom.nsmul_apply, natCast_zsmul]

end Torsion

section TateModL

variable {κ : Type*} [Field κ] [IsAlgClosed κ] [DecidableEq κ]

def homGrp (W X₀ : WeierstrassCurve κ) [W.IsElliptic] [X₀.IsElliptic] : AddSubgroup (Pt κ W →+ Pt κ X₀) where
  carrier := rationalHomSet κ W X₀
  zero_mem' := zero_mem_rationalHomSet κ W X₀
  add_mem' ha hb := add_mem_rationalHomSet κ W X₀ ha hb
  neg_mem' ha := neg_mem_rationalHomSet ha

variable {W X₀ : WeierstrassCurve κ} [W.IsElliptic] [X₀.IsElliptic]

theorem mem_homGrp {ρ : Pt κ W →+ Pt κ X₀} : ρ ∈ homGrp W X₀ ↔ ρ ∈ rationalHomSet κ W X₀ := Iff.rfl

theorem closure_rationalHomSet : AddSubgroup.closure (rationalHomSet κ W X₀) = homGrp W X₀ :=
  le_antisymm ((AddSubgroup.closure_le _).mpr fun _ h => h) fun _ h => AddSubgroup.subset_closure h

variable {ℓ : ℕ}

theorem natCard_addMonoidHom_tors [Fact ℓ.Prime] (hℓκ : (ℓ : κ) ≠ 0) :
    Nat.card (tors W ℓ →+ tors X₀ ℓ) = ℓ ^ 4 := by
  have hℓ : ℓ.Prime := Fact.out
  haveI := finite_tors W hℓ.ne_zero hℓκ
  haveI := finite_tors X₀ hℓ.ne_zero hℓκ
  haveI : Module.Finite (ZMod ℓ) (tors W ℓ) := Module.Finite.of_finite
  haveI : Module.Finite (ZMod ℓ) (tors X₀ ℓ) := Module.Finite.of_finite
  rw [Nat.card_congr (AddMonoidHom.toZModLinearMapEquiv ℓ (M := tors W ℓ) (M₁ := tors X₀ ℓ)).toEquiv,
    Module.natCard_eq_pow_finrank (K := ZMod ℓ), Module.finrank_linearMap, finrank_tors W hℓκ,
    finrank_tors X₀ hℓκ, Nat.card_zmod]

theorem finite_addMonoidHom_tors [Fact ℓ.Prime] (hℓκ : (ℓ : κ) ≠ 0) : Finite (tors W ℓ →+ tors X₀ ℓ) := by
  have hℓ : ℓ.Prime := Fact.out
  refine Nat.finite_of_card_ne_zero ?_
  rw [natCard_addMonoidHom_tors hℓκ]; exact pow_ne_zero 4 hℓ.ne_zero

variable {a b : ℚ}

theorem exists_mem_rationalHomSet_res_eq [Fact ℓ.Prime] (hℓκ : (ℓ : κ) ≠ 0)
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b])
    (hθ : Function.Injective θ) (hθΛ : Set.range θ = (Λ : Set ℍ[ℚ, a, b]))
    (hW : ∃ σ ∈ rationalHomSet κ W X₀, σ ≠ 0) (f : tors W ℓ →+ tors X₀ ℓ) :
    ∃ ρ ∈ rationalHomSet κ W X₀, res W X₀ ℓ ρ = f := by
  have hℓ : ℓ.Prime := Fact.out
  classical

  obtain ⟨σ, hσ, hσ0⟩ := hW
  obtain ⟨τ, hτ, n, hn, hdual⟩ := WeierstrassCurve.exists_isDualPair_of_mem_rationalHomSet κ W X₀ hσ hσ0
  have hτ0 : τ ≠ 0 := by
    intro h0
    apply smul_id_ne_zero (k := κ) W hn.ne'
    ext P
    rw [AddMonoidHom.zsmul_apply, AddMonoidHom.id_apply, AddMonoidHom.zero_apply, ← hdual.comp_left P, h0,
      AddMonoidHom.zero_apply]
  have hτs : Function.Surjective τ := WeierstrassCurve.surjective_of_mem_rationalHomSet κ hτ hτ0

  let cR : homGrp W X₀ →+ ↥(rationalEndSubring κ X₀) :=
    { toFun := fun ρ => ⟨(ρ.1).comp τ, Subring.subset_closure
          (comp_mem_rationalHomSet κ X₀ W X₀ hτ ρ.2)⟩
      map_zero' := by ext P; rfl
      map_add' := fun _ _ => by ext P; rfl }
  have cR_apply : ∀ (ρ : homGrp W X₀) (P : Pt κ X₀),
      ((cR ρ : ↥(rationalEndSubring κ X₀)) : AddMonoid.End (Pt κ X₀)) P = ρ.1 (τ P) := fun _ _ => rfl

  let Φ : homGrp W X₀ →ₗ[ℤ] ℍ[ℚ, a, b] := (θ.toAddMonoidHom.comp cR).toIntLinearMap
  have Φ_apply : ∀ ρ : homGrp W X₀, Φ ρ = θ (cR ρ) := fun _ => rfl
  have hΦ : Function.Injective Φ := by
    intro ρ ρ' h
    rw [Φ_apply, Φ_apply] at h
    have h2 := hθ h
    apply Subtype.ext
    ext Q
    obtain ⟨P, rfl⟩ := hτs Q
    have := congrArg (fun e : ↥(rationalEndSubring κ X₀) => (e : AddMonoid.End (Pt κ X₀)) P) h2
    simpa only [cR_apply] using this
  set K : Submodule ℤ ℍ[ℚ, a, b] := LinearMap.range Φ with hK
  have hKΛ : K ≤ Λ := by
    rintro _ ⟨ρ, rfl⟩
    rw [Φ_apply, ← SetLike.mem_coe, ← hθΛ]
    exact ⟨_, rfl⟩

  haveI : IsAddTorsionFree ℍ[ℚ, a, b] := .of_module_rat _
  have hninj : Function.Injective ((n : ℤ) • (LinearMap.id : ℍ[ℚ, a, b] →ₗ[ℤ] ℍ[ℚ, a, b])) := by
    intro x y hxy
    exact smul_right_injective ℍ[ℚ, a, b] hn.ne' hxy
  have hnΛK : Λ.map ((n : ℤ) • (LinearMap.id : ℍ[ℚ, a, b] →ₗ[ℤ] ℍ[ℚ, a, b])) ≤ K := by
    rintro _ ⟨μ, hμ, rfl⟩
    have hμ' : μ ∈ Set.range θ := by rw [hθΛ]; exact hμ
    obtain ⟨α, rfl⟩ := hμ'
    have hα : (α : AddMonoid.End (Pt κ X₀)) ∈ rationalEndSubring κ X₀ := α.2
    have hαr : ((α : AddMonoid.End (Pt κ X₀)) : Pt κ X₀ →+ Pt κ X₀) ∈ rationalHomSet κ X₀ X₀ :=
      mem_rationalHomSet_of_mem_end hα
    refine ⟨⟨((α : AddMonoid.End (Pt κ X₀)) : Pt κ X₀ →+ Pt κ X₀).comp σ,
      comp_mem_rationalHomSet κ W X₀ X₀ hσ hαr⟩, ?_⟩
    rw [Φ_apply]
    change θ (cR _) = (n : ℤ) • θ α
    rw [← map_zsmul]
    congr 1
    apply Subtype.ext
    ext P
    rw [cR_apply]
    change (α : AddMonoid.End (Pt κ X₀)) (σ (τ P)) = (((n : ℤ) • α : ↥(rationalEndSubring κ X₀)) :
      AddMonoid.End (Pt κ X₀)) P
    rw [hdual.comp_right P, map_zsmul]
    rfl

  haveI : Module.Finite ℤ Λ := Module.Finite.iff_fg.mpr hΛ.fg
  have hΛ4 : Module.finrank ℤ Λ = 4 := hΛ.finrank_eq_four
  haveI : Module.Finite ℤ K := Module.Finite.of_injective (Submodule.inclusion hKΛ)
    (Submodule.inclusion_injective hKΛ)
  have hK4 : Module.finrank ℤ K = 4 := by
    refine le_antisymm (hΛ4 ▸ Submodule.finrank_mono hKΛ) ?_
    have h1 : Module.finrank ℤ (Λ.map ((n : ℤ) • (LinearMap.id : ℍ[ℚ, a, b] →ₗ[ℤ] ℍ[ℚ, a, b]))) = 4 := by
      rw [← hΛ4]
      exact (Submodule.equivMapOfInjective _ hninj Λ).symm.finrank_eq
    rw [← h1]
    exact Submodule.finrank_mono hnΛK
  let bK : Module.Basis (Fin 4) ℤ K := Module.finBasisOfFinrankEq ℤ K hK4
  let eΦ : homGrp W X₀ ≃ₗ[ℤ] K := LinearEquiv.ofInjective Φ hΦ

  let lift : (Fin 4 → ZMod ℓ) → K := fun v => ∑ i, ((v i).val : ℤ) • bK i
  let Ψ : (Fin 4 → ZMod ℓ) → (tors W ℓ →+ tors X₀ ℓ) := fun v => res W X₀ ℓ (eΦ.symm (lift v)).1
  have hΨmem : ∀ v, Ψ v ∈ (res W X₀ ℓ) '' (rationalHomSet κ W X₀) := fun v =>
    ⟨(eΦ.symm (lift v)).1, (eΦ.symm (lift v)).2, rfl⟩
  have hΨ : Function.Injective Ψ := by
    intro v v' hvv'
    have h0 : res W X₀ ℓ ((eΦ.symm (lift v)).1 - (eΦ.symm (lift v')).1) = 0 := by
      rw [map_sub, sub_eq_zero]; exact hvv'
    have hmem : (eΦ.symm (lift v)).1 - (eΦ.symm (lift v')).1 ∈ rationalHomSet κ W X₀ :=
      sub_mem_rationalHomSet (eΦ.symm (lift v)).2 (eΦ.symm (lift v')).2
    obtain ⟨β, hβ, hβeq⟩ := exists_eq_nsmul_of_res_eq_zero hℓκ hmem h0

    have h1 : eΦ.symm (lift v) - eΦ.symm (lift v') = (ℓ : ℤ) • (⟨β, hβ⟩ : homGrp W X₀) := by
      apply Subtype.ext
      change (eΦ.symm (lift v)).1 - (eΦ.symm (lift v')).1 = (ℓ : ℤ) • β
      rw [hβeq, natCast_zsmul]
    have h2 : lift v - lift v' = (ℓ : ℤ) • eΦ ⟨β, hβ⟩ := by
      have := congrArg eΦ h1
      rwa [map_sub, map_zsmul, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
    funext i
    have h3 := congrArg (fun x => bK.repr x i) h2
    simp only [lift, map_sub, map_zsmul, map_sum, Module.Basis.repr_self, Finsupp.coe_sub, Finsupp.coe_smul,
      Finsupp.coe_finsetSum, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, Finsupp.single_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h3

    have h4 : ((v i).val : ZMod ℓ) = ((v' i).val : ZMod ℓ) := by
      have h5 : (((v i).val : ℤ) : ZMod ℓ) = (((v' i).val : ℤ) : ZMod ℓ) := by
        rw [← sub_eq_zero, ← Int.cast_sub, h3, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]
      exact_mod_cast h5
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h4

  haveI := finite_addMonoidHom_tors (W := W) (X₀ := X₀) hℓκ
  have hcard : (Set.range Ψ).ncard = ℓ ^ 4 := by
    rw [Set.ncard_range_of_injective hΨ, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hsub : Set.range Ψ ⊆ (res W X₀ ℓ) '' (rationalHomSet κ W X₀) := by
    rintro _ ⟨v, rfl⟩; exact hΨmem v
  have huniv : (res W X₀ ℓ) '' (rationalHomSet κ W X₀) = Set.univ := by
    refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ Set.finite_univ
    rw [Set.ncard_univ, natCard_addMonoidHom_tors hℓκ, ← hcard]
    exact Set.ncard_le_ncard hsub (Set.finite_univ.subset (Set.subset_univ _))
  have hf : f ∈ (res W X₀ ℓ) '' (rationalHomSet κ W X₀) := by rw [huniv]; trivial
  obtain ⟨ρ, hρ, hρf⟩ := hf
  exact ⟨ρ, hρ, hρf⟩

end TateModL

section LinearAlgebra

variable {F V V₀ : Type*} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup V₀] [Module F V₀]

theorem mem_of_forall_jointKer [FiniteDimensional F V] [FiniteDimensional F V₀] (S : Submodule F (V →ₗ[F] V₀))
    (hS : ∀ g : V₀ →ₗ[F] V₀, ∀ f ∈ S, g.comp f ∈ S)
    (f : V →ₗ[F] V₀) (hf : ∀ v, (∀ g ∈ S, g v = 0) → f v = 0) : f ∈ S := by
  classical
  set m := Module.finrank F S
  let bs : Module.Basis (Fin m) F S := Module.finBasis F S
  let s : Fin m → (V →ₗ[F] V₀) := fun i => (bs i : V →ₗ[F] V₀)
  have hs : ∀ i, s i ∈ S := fun i => (bs i).2
  let T : V →ₗ[F] (Fin m → V₀) := LinearMap.pi s
  have hT : ∀ v i, T v i = s i v := fun v i => rfl

  have hker : LinearMap.ker T ≤ LinearMap.ker f := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    apply hf
    intro g hg
    have hg' : (⟨g, hg⟩ : S) = ∑ i, bs.repr ⟨g, hg⟩ i • bs i := (bs.sum_repr ⟨g, hg⟩).symm
    have : g = ∑ i, bs.repr ⟨g, hg⟩ i • s i := by
      have := congrArg (fun x : S => (x : V →ₗ[F] V₀)) hg'
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using this
    rw [this, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [LinearMap.smul_apply, ← hT, hv]
    simp

  let f₂ : LinearMap.range T →ₗ[F] V₀ :=
    ((LinearMap.ker T).liftQ f hker).comp T.quotKerEquivRange.symm.toLinearMap
  have hf₂ : ∀ v, f₂ ⟨T v, LinearMap.mem_range_self T v⟩ = f v := by
    intro v
    have h1 : T.quotKerEquivRange.symm ⟨T v, LinearMap.mem_range_self T v⟩ =
        Submodule.Quotient.mk v := LinearMap.quotKerEquivRange_symm_apply_image T v _
    change ((LinearMap.ker T).liftQ f hker) (T.quotKerEquivRange.symm ⟨T v, _⟩) = f v
    rw [h1, Submodule.liftQ_apply]
  obtain ⟨G, hG⟩ := LinearMap.exists_extend f₂
  have hfG : f = G.comp T := by
    ext v
    have := congrArg (fun h : LinearMap.range T →ₗ[F] V₀ => h ⟨T v, LinearMap.mem_range_self T v⟩) hG
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at this
    rw [LinearMap.comp_apply, this, hf₂]

  have hsum : G.comp T = ∑ i, (G.comp (LinearMap.single F (fun _ : Fin m => V₀) i)).comp (s i) := by
    ext v
    rw [LinearMap.comp_apply, LinearMap.sum_apply]
    have hTv : T v = ∑ i, Pi.single i (s i v) := by
      rw [Finset.univ_sum_single]
      rfl
    rw [hTv, map_sum]
    rfl
  rw [hfG, hsum]
  exact Submodule.sum_mem _ fun i _ => hS _ _ (hs i)

def restr (U : Submodule F V) : (V →ₗ[F] V₀) →ₗ[F] (U →ₗ[F] V₀) := LinearMap.lcomp F V₀ U.subtype

theorem restr_apply (U : Submodule F V) (f : V →ₗ[F] V₀) (u : U) : restr (V₀ := V₀) U f u = f u := rfl

theorem mem_ker_restr_iff (U : Submodule F V) (f : V →ₗ[F] V₀) :
    f ∈ LinearMap.ker (restr (V₀ := V₀) U) ↔ ∀ u ∈ U, f u = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h u hu
    exact congrArg (fun g : U →ₗ[F] V₀ => g ⟨u, hu⟩) h
  · intro h
    ext u
    exact h u u.2

theorem restr_surjective (U : Submodule F V) : Function.Surjective (restr (V₀ := V₀) U) := by
  intro h
  obtain ⟨g, hg⟩ := LinearMap.exists_extend h
  exact ⟨g, hg⟩

theorem finrank_ker_restr [FiniteDimensional F V] [FiniteDimensional F V₀] (U : Submodule F V) :
    Module.finrank F (LinearMap.ker (restr (V₀ := V₀) U)) + Module.finrank F U * Module.finrank F V₀ =
      Module.finrank F V * Module.finrank F V₀ := by
  have h := LinearMap.finrank_range_add_finrank_ker (restr (V₀ := V₀) U)
  rw [LinearMap.range_eq_top.mpr (restr_surjective U), finrank_top, Module.finrank_linearMap,
    Module.finrank_linearMap] at h
  omega

theorem natCard_ker_restr_mul [Finite F] [FiniteDimensional F V] [FiniteDimensional F V₀] (U : Submodule F V) :
    Nat.card (LinearMap.ker (restr (V₀ := V₀) U)) * Nat.card U ^ Module.finrank F V₀ =
      Nat.card (V →ₗ[F] V₀) := by
  rw [Module.natCard_eq_pow_finrank (K := F) (V := LinearMap.ker (restr (V₀ := V₀) U)),
    Module.natCard_eq_pow_finrank (K := F) (V := U), Module.natCard_eq_pow_finrank (K := F) (V := V →ₗ[F] V₀),
    ← pow_mul, ← pow_add, finrank_ker_restr, Module.finrank_linearMap]

theorem exists_mem_ker_restr_apply_ne_zero [Nontrivial V₀] (U : Submodule F V) {v : V} (hv : v ∉ U) :
    ∃ f ∈ LinearMap.ker (restr (V₀ := V₀) U), f v ≠ 0 := by
  obtain ⟨φ, hφv, hφU⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
  obtain ⟨w, hw⟩ := exists_ne (0 : V₀)
  refine ⟨(LinearMap.toSpanSingleton F V₀ w).comp φ, ?_, ?_⟩
  · rw [mem_ker_restr_iff]
    intro u hu
    have : φ u = 0 := by
      have h := (Submodule.eq_bot_iff _).mp hφU (φ u) (Submodule.mem_map_of_mem hu)
      exact h
    rw [LinearMap.comp_apply, this, map_zero]
  · rw [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
    exact smul_ne_zero hφv hw

end LinearAlgebra

section Assembly

variable {κ : Type*} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
variable {W X₀ : WeierstrassCurve κ} [W.IsElliptic] [X₀.IsElliptic] {ℓ : ℕ} {a b : ℚ}

def resL (W X₀ : WeierstrassCurve κ) (ℓ : ℕ) (ρ : Pt κ W →+ Pt κ X₀) : tors W ℓ →ₗ[ZMod ℓ] tors X₀ ℓ :=
  (res W X₀ ℓ ρ).toZModLinearMap ℓ

@[scoped simp] theorem resL_apply (ρ : Pt κ W →+ Pt κ X₀) (P : tors W ℓ) : ((resL W X₀ ℓ ρ P : tors X₀ ℓ) : Pt κ X₀) = ρ P :=
  rfl

theorem resL_add (ρ ρ' : Pt κ W →+ Pt κ X₀) : resL W X₀ ℓ (ρ + ρ') = resL W X₀ ℓ ρ + resL W X₀ ℓ ρ' := by
  ext P; rfl

theorem resL_comp {W X₀ X₁ : WeierstrassCurve κ} (α : Pt κ X₀ →+ Pt κ X₁) (ρ : Pt κ W →+ Pt κ X₀) :
    resL W X₁ ℓ (α.comp ρ) = (resL X₀ X₁ ℓ α).comp (resL W X₀ ℓ ρ) := by
  ext P; rfl

theorem exists_mem_rationalHomSet_resL_eq [Fact ℓ.Prime] (hℓκ : (ℓ : κ) ≠ 0)
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b])
    (hθ : Function.Injective θ) (hθΛ : Set.range θ = (Λ : Set ℍ[ℚ, a, b]))
    (hW : ∃ σ ∈ rationalHomSet κ W X₀, σ ≠ 0) (g : tors W ℓ →ₗ[ZMod ℓ] tors X₀ ℓ) :
    ∃ ρ ∈ rationalHomSet κ W X₀, resL W X₀ ℓ ρ = g := by
  obtain ⟨ρ, hρ, h⟩ := exists_mem_rationalHomSet_res_eq hℓκ hΛ θ hθ hθΛ hW g.toAddMonoidHom
  refine ⟨ρ, hρ, ?_⟩
  ext P
  exact congrArg (fun f : tors W ℓ →+ tors X₀ ℓ => (f P : Pt κ X₀)) h

def torsSub (U : AddSubgroup (Pt κ W)) (ℓ : ℕ) : Submodule (ZMod ℓ) (tors W ℓ) :=
  AddSubgroup.toZModSubmodule ℓ (U.addSubgroupOf (tors W ℓ))

theorem mem_torsSub_iff {U : AddSubgroup (Pt κ W)} {P : tors W ℓ} : P ∈ torsSub U ℓ ↔ (P : Pt κ W) ∈ U := Iff.rfl

theorem natCard_torsSub {U : AddSubgroup (Pt κ W)} (hU : U ≤ tors W ℓ) : Nat.card (torsSub U ℓ) = Nat.card U := by
  refine Nat.card_congr ?_
  exact ((AddSubgroup.addSubgroupOfEquivOfLe hU).toEquiv :)

variable [Fact ℓ.Prime]

theorem le_ker_iff_resL_mem {U : AddSubgroup (Pt κ W)} (hU : U ≤ tors W ℓ) (ρ : Pt κ W →+ Pt κ X₀) :
    U ≤ ρ.ker ↔ resL W X₀ ℓ ρ ∈ LinearMap.ker (restr (V₀ := tors X₀ ℓ) (torsSub U ℓ)) := by
  rw [mem_ker_restr_iff]
  constructor
  · intro h P hP
    apply Subtype.ext
    exact h (mem_torsSub_iff.mp hP)
  · intro h Q hQ
    have := h ⟨Q, hU hQ⟩ (mem_torsSub_iff.mpr hQ)
    exact congrArg Subtype.val this

theorem partA (hℓκ : (ℓ : κ) ≠ 0)
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b])
    (hθ : Function.Injective θ) (hθΛ : Set.range θ = (Λ : Set ℍ[ℚ, a, b]))
    (hW : ∃ σ ∈ rationalHomSet κ W X₀, σ ≠ 0)
    (U : AddSubgroup (Pt κ W)) (hUℓ : ∀ P ∈ U, (ℓ : ℤ) • P = 0) :
    {P : Pt κ W | (ℓ : ℤ) • P = 0 ∧ ∀ ρ ∈ rationalHomSet κ W X₀, U ≤ ρ.ker → ρ P = 0} = (U : Set _) ∧
    (AddSubgroup.closure {ρ | ρ ∈ rationalHomSet κ W X₀ ∧ U ≤ ρ.ker}).relIndex
        (AddSubgroup.closure (rationalHomSet κ W X₀)) = Nat.card U ^ 2 := by
  have hℓ : ℓ.Prime := Fact.out
  haveI := finite_tors W hℓ.ne_zero hℓκ
  haveI := finite_tors X₀ hℓ.ne_zero hℓκ
  haveI : Module.Finite (ZMod ℓ) (tors W ℓ) := Module.Finite.of_finite
  haveI : Module.Finite (ZMod ℓ) (tors X₀ ℓ) := Module.Finite.of_finite
  have hV₀ : Nontrivial (tors X₀ ℓ) := by
    rw [← Finite.one_lt_card_iff_nontrivial, natCard_tors X₀ hℓκ]
    exact Nat.one_lt_pow two_ne_zero hℓ.one_lt
  have hU : U ≤ tors W ℓ := fun P hP => mem_tors_iff.mpr (hUℓ P hP)
  set U' : Submodule (ZMod ℓ) (tors W ℓ) := torsSub U ℓ with hU'
  refine ⟨?_, ?_⟩
  ·
    ext P
    simp only [Set.mem_setOf_eq, SetLike.mem_coe]
    constructor
    · rintro ⟨hP, hann⟩
      by_contra hPU
      have hv : (⟨P, mem_tors_iff.mpr hP⟩ : tors W ℓ) ∉ U' := fun h => hPU (mem_torsSub_iff.mp h)
      obtain ⟨g, hg, hgv⟩ := exists_mem_ker_restr_apply_ne_zero (V₀ := tors X₀ ℓ) U' hv
      obtain ⟨ρ, hρ, hρg⟩ := exists_mem_rationalHomSet_resL_eq hℓκ hΛ θ hθ hθΛ hW g
      have hρU : U ≤ ρ.ker := by
        rw [le_ker_iff_resL_mem hU, hρg]; exact hg
      apply hgv
      apply Subtype.ext
      rw [← hρg]
      exact hann ρ hρ hρU
    · intro hP
      exact ⟨hUℓ P hP, fun ρ _ hρU => hρU hP⟩
  ·
    rw [closure_rationalHomSet]

    let A : AddSubgroup (Pt κ W →+ Pt κ X₀) :=
      { carrier := {ρ | ρ ∈ rationalHomSet κ W X₀ ∧ U ≤ ρ.ker}
        zero_mem' := ⟨zero_mem_rationalHomSet κ W X₀, fun _ _ => rfl⟩
        add_mem' := fun {x y} hx hy => ⟨add_mem_rationalHomSet κ W X₀ hx.1 hy.1, fun P hP => by
          change (x + y) P = 0
          rw [AddMonoidHom.add_apply, show x P = 0 from hx.2 hP, show y P = 0 from hy.2 hP, add_zero]⟩
        neg_mem' := fun {x} hx => ⟨neg_mem_rationalHomSet hx.1, fun P hP => by
          change (-x) P = 0
          rw [AddMonoidHom.neg_apply, show x P = 0 from hx.2 hP, neg_zero]⟩ }
    have hA : AddSubgroup.closure {ρ | ρ ∈ rationalHomSet κ W X₀ ∧ U ≤ ρ.ker} = A :=
      le_antisymm ((AddSubgroup.closure_le _).mpr fun _ h => h) fun _ h => AddSubgroup.subset_closure h
    rw [hA]

    let E := tors W ℓ →ₗ[ZMod ℓ] tors X₀ ℓ
    let r : homGrp W X₀ →+ E :=
      { toFun := fun ρ => resL W X₀ ℓ ρ.1
        map_zero' := by ext P; rfl
        map_add' := fun _ _ => by ext P; rfl }
    have hr : Function.Surjective r := by
      intro g
      obtain ⟨ρ, hρ, h⟩ := exists_mem_rationalHomSet_resL_eq hℓκ hΛ θ hθ hθΛ hW g
      exact ⟨⟨ρ, hρ⟩, h⟩
    let Ann : AddSubgroup E := (LinearMap.ker (restr (V₀ := tors X₀ ℓ) U')).toAddSubgroup
    have hcomap : A.addSubgroupOf (homGrp W X₀) = Ann.comap r := by
      ext ρ
      change (ρ.1 ∈ rationalHomSet κ W X₀ ∧ U ≤ ρ.1.ker) ↔ resL W X₀ ℓ ρ.1 ∈ LinearMap.ker (restr U')
      rw [← le_ker_iff_resL_mem hU]
      exact ⟨fun h => h.2, fun h => ⟨ρ.2, h⟩⟩
    have hidx : A.relIndex (homGrp W X₀) = Ann.index := by
      rw [AddSubgroup.relIndex, hcomap, AddSubgroup.index_comap_of_surjective Ann hr]
    rw [hidx]

    haveI : Finite E := Module.finite_of_finite (ZMod ℓ)
    have h1 : Nat.card Ann * Ann.index = Nat.card E := AddSubgroup.card_mul_index Ann
    have h2 : Nat.card Ann * Nat.card U' ^ 2 = Nat.card E := by
      have := natCard_ker_restr_mul (V₀ := tors X₀ ℓ) U'
      rwa [finrank_tors X₀ hℓκ] at this
    have hAnn : Nat.card Ann ≠ 0 := Nat.card_pos.ne'
    have h3 : Ann.index = Nat.card U' ^ 2 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hAnn) (h1.trans h2.symm)
    rw [h3, natCard_torsSub hU]

theorem partB (hℓκ : (ℓ : κ) ≠ 0)
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b])
    (hθ : Function.Injective θ) (hθΛ : Set.range θ = (Λ : Set ℍ[ℚ, a, b]))
    (hW : ∃ σ ∈ rationalHomSet κ W X₀, σ ≠ 0)
    (M : AddSubgroup (Pt κ W →+ Pt κ X₀)) (hMH : (M : Set _) ⊆ rationalHomSet κ W X₀)
    (hMℓ : ∀ ρ ∈ rationalHomSet κ W X₀, ℓ • ρ ∈ M)
    (hMR : ∀ α ∈ rationalHomSet κ X₀ X₀, ∀ ρ ∈ M, α.comp ρ ∈ M)
    (ρ : Pt κ W →+ Pt κ X₀) (hρ : ρ ∈ rationalHomSet κ W X₀)
    (hρK : ∀ P : Pt κ W, (ℓ : ℤ) • P = 0 → (∀ μ ∈ M, μ P = 0) → ρ P = 0) : ρ ∈ M := by
  have hℓ : ℓ.Prime := Fact.out
  haveI := finite_tors W hℓ.ne_zero hℓκ
  haveI := finite_tors X₀ hℓ.ne_zero hℓκ
  haveI : Module.Finite (ZMod ℓ) (tors W ℓ) := Module.Finite.of_finite
  haveI : Module.Finite (ZMod ℓ) (tors X₀ ℓ) := Module.Finite.of_finite

  let rL : (Pt κ W →+ Pt κ X₀) →+ (tors W ℓ →ₗ[ZMod ℓ] tors X₀ ℓ) :=
    { toFun := resL W X₀ ℓ
      map_zero' := by ext P; rfl
      map_add' := fun _ _ => by ext P; rfl }
  let S : Submodule (ZMod ℓ) (tors W ℓ →ₗ[ZMod ℓ] tors X₀ ℓ) := AddSubgroup.toZModSubmodule ℓ (M.map rL)
  have hS_mem : ∀ {g}, g ∈ S ↔ ∃ μ ∈ M, resL W X₀ ℓ μ = g := fun {g} => by
    change g ∈ M.map rL ↔ _
    rw [AddSubgroup.mem_map]; rfl

  have hS : ∀ g : tors X₀ ℓ →ₗ[ZMod ℓ] tors X₀ ℓ, ∀ f ∈ S, g.comp f ∈ S := by
    intro g f hf
    obtain ⟨μ, hμ, rfl⟩ := hS_mem.mp hf
    have hX₀ : ∃ σ ∈ rationalHomSet κ X₀ X₀, σ ≠ 0 :=
      ⟨AddMonoidHom.id _, id_mem_rationalHomSet κ X₀, fun h => by
        haveI := infinite_point (k := κ) X₀
        obtain ⟨P, hP⟩ := exists_ne (0 : Pt κ X₀)
        exact hP (by simpa using DFunLike.congr_fun h P)⟩
    obtain ⟨α, hα, hαg⟩ := exists_mem_rationalHomSet_resL_eq (W := X₀) hℓκ hΛ θ hθ hθΛ hX₀ g
    refine hS_mem.mpr ⟨α.comp μ, hMR α hα μ hμ, ?_⟩
    rw [resL_comp, hαg]

  have hf : ∀ v, (∀ g ∈ S, g v = 0) → resL W X₀ ℓ ρ v = 0 := by
    intro v hv
    apply Subtype.ext
    apply hρK v.1 (mem_tors_iff.mp v.2)
    intro μ hμ
    have := hv (resL W X₀ ℓ μ) (hS_mem.mpr ⟨μ, hμ, rfl⟩)
    exact congrArg Subtype.val this
  obtain ⟨μ, hμ, hμρ⟩ := hS_mem.mp (mem_of_forall_jointKer S hS _ hf)

  have hμH : μ ∈ rationalHomSet κ W X₀ := hMH hμ
  have hsub : ρ - μ ∈ rationalHomSet κ W X₀ := sub_mem_rationalHomSet hρ hμH
  have h0 : res W X₀ ℓ (ρ - μ) = 0 := by
    ext P
    have := congrArg (fun g : tors W ℓ →ₗ[ZMod ℓ] tors X₀ ℓ => ((g P : tors X₀ ℓ) : Pt κ X₀)) hμρ
    simp only [resL_apply] at this
    change (((ρ - μ) P : Pt κ X₀)) = ((0 : tors X₀ ℓ) : Pt κ X₀)
    rw [AddMonoidHom.sub_apply, this, sub_self]; rfl
  obtain ⟨β, hβ, hβeq⟩ := exists_eq_nsmul_of_res_eq_zero hℓκ hsub h0
  have : ρ = μ + ℓ • β := by rw [← hβeq]; abel
  rw [this]
  exact M.add_mem hμ (hMℓ β hβ)

end Assembly

end WeierstrassCurve.HomModuleAtPrime
p2m_reactivate "P2MW.S_WeierstrassCurve_relIndex_annihilator_eq_sq_natCard_and_mem_of_forall_apply_torsion_eq_zero.WeierstrassCurve P2MW.S_WeierstrassCurve_relIndex_annihilator_eq_sq_natCard_and_mem_of_forall_apply_torsion_eq_zero.WeierstrassCurve.HomModuleAtPrime"
p2m_reactivate "P2MW.S_WeierstrassCurve_relIndex_annihilator_eq_sq_natCard_and_mem_of_forall_apply_torsion_eq_zero.WeierstrassCurve"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_relIndex_annihilator_eq_sq_natCard_and_mem_of_forall_apply_torsion_eq_zero.WeierstrassCurve P2MW.S_WeierstrassCurve_relIndex_annihilator_eq_sq_natCard_and_mem_of_forall_apply_torsion_eq_zero.WeierstrassCurve.HomModuleAtPrime"

open WeierstrassCurve.HomModuleAtPrime in
theorem solution
    {κ : Type*} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (X₀ : WeierstrassCurve κ) [X₀.IsElliptic]
    (a b : ℚ) (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (θ : ↥(WeierstrassCurve.rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b])
    (hθ : Function.Injective θ) (hθΛ : Set.range θ = (Λ : Set ℍ[ℚ, a, b]))
    (W : WeierstrassCurve κ) [W.IsElliptic]
    (hW : ∃ σ ∈ WeierstrassCurve.rationalHomSet κ W X₀, σ ≠ 0)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓκ : (ℓ : κ) ≠ 0) :
    (∀ U : AddSubgroup (W.baseChange κ).toAffine.Point, (∀ P ∈ U, (ℓ : ℤ) • P = 0) →
      {P : (W.baseChange κ).toAffine.Point | (ℓ : ℤ) • P = 0 ∧
          ∀ ρ ∈ WeierstrassCurve.rationalHomSet κ W X₀, U ≤ ρ.ker → ρ P = 0} = (U : Set _) ∧
      (AddSubgroup.closure {ρ | ρ ∈ WeierstrassCurve.rationalHomSet κ W X₀ ∧ U ≤ ρ.ker}).relIndex
          (AddSubgroup.closure (WeierstrassCurve.rationalHomSet κ W X₀)) = Nat.card U ^ 2) ∧
    (∀ M : AddSubgroup ((W.baseChange κ).toAffine.Point →+ (X₀.baseChange κ).toAffine.Point),
      (M : Set _) ⊆ WeierstrassCurve.rationalHomSet κ W X₀ →
      (∀ ρ ∈ WeierstrassCurve.rationalHomSet κ W X₀, ℓ • ρ ∈ M) →
      (∀ α ∈ WeierstrassCurve.rationalHomSet κ X₀ X₀, ∀ ρ ∈ M, α.comp ρ ∈ M) →
      ∀ ρ ∈ WeierstrassCurve.rationalHomSet κ W X₀,
        (∀ P : (W.baseChange κ).toAffine.Point, (ℓ : ℤ) • P = 0 → (∀ μ ∈ M, μ P = 0) → ρ P = 0) →
        ρ ∈ M) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  exact ⟨fun U hU => partA hℓκ hΛ θ hθ hθΛ hW U hU,
    fun M hMH hMℓ hMR ρ hρ hρK => partB hℓκ hΛ θ hθ hθΛ hW M hMH hMℓ hMR ρ hρ hρK⟩

end S_WeierstrassCurve_relIndex_annihilator_eq_sq_natCard_and_mem_of_forall_apply_torsion_eq_zero
end P2MW
export P2MW.S_WeierstrassCurve_relIndex_annihilator_eq_sq_natCard_and_mem_of_forall_apply_torsion_eq_zero (solution)
