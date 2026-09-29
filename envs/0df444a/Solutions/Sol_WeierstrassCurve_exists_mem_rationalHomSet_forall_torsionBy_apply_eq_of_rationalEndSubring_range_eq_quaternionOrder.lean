-- Prove2me | solution 1 for WeierstrassCurve.exists_mem_rationalHomSet_forall_torsionBy_apply_eq_of_rationalEndSubring_range_eq_quaternionOrder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/7f2906da-06d3-54f4-b391-7ab85c250434

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

namespace P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_forall_torsionBy_apply_eq_of_rationalEndSubring_range_eq_quaternionOrder
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
p2m_export "WeierstrassCurve" "Affine Affine.negY a₃ a₁ map reduction toAffine Affine.nonsingular_neg baseChange evalEvalBC rationalHomSet rationalEndSubring zero_mem_rationalHomSet id_mem_rationalHomSet comp_mem_rationalHomSet add_mem_rationalHomSet surjective_of_mem_rationalHomSet exists_isDualPair_of_mem_rationalHomSet exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero card_torsion_of_isAlgClosed"
namespace RedSurjAtPrime
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

omit [DecidableEq k] in
theorem exists_some_of_eq {Q : Pt k W} {x₁ y₁ : k} {h₁ : (W.baseChange k).toAffine.Nonsingular x₁ y₁}
    (hQ : Q = .some x₁ y₁ h₁) {x₂ y₂ : k} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    ∃ h₂, Q = .some x₂ y₂ h₂ := by
  subst hx hy; exact ⟨h₁, hQ⟩

end Generic

variable {W₁ W₂ : WeierstrassCurve F}

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

theorem exists_ne_zero_mem_rationalHomSet_symm [IsAlgClosed k] [W₁.IsElliptic] [W₂.IsElliptic]
    {χ : Pt k W₁ →+ Pt k W₂} (hχ : χ ∈ rationalHomSet k W₁ W₂) (hχ0 : χ ≠ 0) :
    ∃ τ ∈ rationalHomSet k W₂ W₁, τ ≠ 0 := by
  obtain ⟨τ, hτ, n, hn, hdual⟩ := WeierstrassCurve.exists_isDualPair_of_mem_rationalHomSet k W₁ W₂ hχ hχ0
  refine ⟨τ, hτ, fun h0 => ?_⟩
  apply smul_id_ne_zero (k := k) W₁ hn.ne'
  ext P
  rw [AddMonoidHom.zsmul_apply, AddMonoidHom.id_apply, AddMonoidHom.zero_apply, ← hdual.comp_left P, h0,
    AddMonoidHom.zero_apply]

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

theorem exists_eq_nsmul_of_res_eq_zero [IsAlgClosed κ] [W.IsElliptic] [X₀.IsElliptic] (hℓκ : (ℓ : κ) ≠ 0)
    {ρ : Pt κ W →+ Pt κ X₀} (hρ : ρ ∈ rationalHomSet κ W X₀) (h0 : res W X₀ ℓ ρ = 0) :
    ∃ β ∈ rationalHomSet κ W X₀, ρ = ℓ • β := by
  obtain ⟨β, hβ, hβeq⟩ := WeierstrassCurve.exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero κ W X₀
    hℓκ hρ ((res_eq_zero_iff ρ).mp h0)
  refine ⟨β, hβ, ?_⟩
  ext P
  rw [hβeq P, AddMonoidHom.nsmul_apply, natCast_zsmul]

def cores (f : tors W ℓ →+ Pt κ X₀) : tors W ℓ →+ tors X₀ ℓ :=
  f.codRestrict (tors X₀ ℓ) fun P => by
    have hP : (ℓ : ℤ) • P = 0 := Subtype.ext (by
      rw [AddSubgroupClass.coe_zsmul, ZeroMemClass.coe_zero]; exact mem_tors_iff.mp P.2)
    rw [mem_tors_iff, ← map_zsmul, hP, map_zero]

@[scoped simp] theorem cores_apply (f : tors W ℓ →+ Pt κ X₀) (P : tors W ℓ) : ((cores f P : tors X₀ ℓ) : Pt κ X₀) = f P :=
  rfl

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

theorem exists_mem_rationalHomSet_forall_apply_eq [Fact ℓ.Prime] (hℓκ : (ℓ : κ) ≠ 0)
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b])
    (hθ : Function.Injective θ) (hθΛ : Set.range θ = (Λ : Set ℍ[ℚ, a, b]))
    {χ : Pt κ X₀ →+ Pt κ W} (hχ : χ ∈ rationalHomSet κ X₀ W) (hχ0 : χ ≠ 0)
    (f : tors W ℓ →+ Pt κ X₀) :
    ∃ ρ ∈ rationalHomSet κ W X₀, ∀ P : tors W ℓ, ρ (P : Pt κ W) = f P := by
  have hW : ∃ σ ∈ rationalHomSet κ W X₀, σ ≠ 0 := exists_ne_zero_mem_rationalHomSet_symm hχ hχ0
  obtain ⟨ρ, hρ, hρf⟩ := exists_mem_rationalHomSet_res_eq hℓκ hΛ θ hθ hθΛ hW (cores f)
  refine ⟨ρ, hρ, fun P => ?_⟩
  have := DFunLike.congr_fun hρf P
  exact congrArg Subtype.val this

end TateModL

end WeierstrassCurve.RedSurjAtPrime
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_forall_torsionBy_apply_eq_of_rationalEndSubring_range_eq_quaternionOrder.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_forall_torsionBy_apply_eq_of_rationalEndSubring_range_eq_quaternionOrder.WeierstrassCurve.RedSurjAtPrime"
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_forall_torsionBy_apply_eq_of_rationalEndSubring_range_eq_quaternionOrder.WeierstrassCurve"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_forall_torsionBy_apply_eq_of_rationalEndSubring_range_eq_quaternionOrder.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_forall_torsionBy_apply_eq_of_rationalEndSubring_range_eq_quaternionOrder.WeierstrassCurve.RedSurjAtPrime"

open WeierstrassCurve.RedSurjAtPrime in
theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (X₀ W : WeierstrassCurve κ) [X₀.IsElliptic] [W.IsElliptic]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (θ : ↥(WeierstrassCurve.rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b])
    (hθ : Function.Injective θ) (hθΛ : Set.range θ = (Λ : Set ℍ[ℚ, a, b]))
    (χ : X₀.toAffine.Point →+ W.toAffine.Point) (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₀ W) (hχ0 : χ ≠ 0)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓκ : (ℓ : κ) ≠ 0)
    (f : ↥(Submodule.torsionBy ℤ W.toAffine.Point (ℓ : ℤ)) →+ X₀.toAffine.Point) :
    ∃ ρ ∈ WeierstrassCurve.rationalHomSet κ W X₀,
      ∀ P : ↥(Submodule.torsionBy ℤ W.toAffine.Point (ℓ : ℤ)), ρ (P : W.toAffine.Point) = f P := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  exact exists_mem_rationalHomSet_forall_apply_eq (W := W) (X₀ := X₀) hℓκ hΛ θ hθ hθΛ hχ hχ0 f

end S_WeierstrassCurve_exists_mem_rationalHomSet_forall_torsionBy_apply_eq_of_rationalEndSubring_range_eq_quaternionOrder
end P2MW
export P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_forall_torsionBy_apply_eq_of_rationalEndSubring_range_eq_quaternionOrder (solution)
