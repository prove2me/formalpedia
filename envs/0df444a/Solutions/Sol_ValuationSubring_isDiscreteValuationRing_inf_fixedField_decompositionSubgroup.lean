-- Prove2me | solution 1 for ValuationSubring.isDiscreteValuationRing_inf_fixedField_decompositionSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/9ee7ef11-2c24-5191-9c46-3522c1d8192c

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_dvr_subring_of_forall_mem_decompositionSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_isDiscreteValuationRing_inf_fixedField_decompositionSubgroup

set_option autoImplicit false

noncomputable section

namespace P2MMultO

variable (A : ValuationSubring (AlgebraicClosure ℚ))

abbrev decField : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.fixedField (A.decompositionSubgroup ℚ)

def decDVR : ValuationSubring (decField A) := A.comap (algebraMap (decField A) (AlgebraicClosure ℚ))

variable {A}

theorem mem_decField_iff {x : AlgebraicClosure ℚ} :
    x ∈ decField A ↔ ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ → σ x = x := by
  rw [decField, IntermediateField.mem_fixedField_iff]

private def _root_.P2MMultO.val (z : decDVR A) : AlgebraicClosure ℚ := ((z : decField A) : AlgebraicClosure ℚ)

p2m_export "P2MMultO" "val"
theorem val_memA (z : decDVR A) : val z ∈ A := z.2

theorem val_fixed (z : decDVR A) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.decompositionSubgroup ℚ) :
    σ (val z) = val z :=
  mem_decField_iff.mp (z : decField A).2 σ hσ

theorem val_injective : Function.Injective (val (A := A)) := fun _ _ h => Subtype.ext (Subtype.ext h)

@[scoped simp] theorem val_zero : val (0 : decDVR A) = 0 := rfl
@[scoped simp] theorem val_one : val (1 : decDVR A) = 1 := rfl
@[scoped simp] theorem val_mul (x y : decDVR A) : val (x * y) = val x * val y := rfl
@[scoped simp] theorem val_add (x y : decDVR A) : val (x + y) = val x + val y := rfl
@[scoped simp] theorem val_pow (x : decDVR A) (n : ℕ) : val (x ^ n) = val x ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, val_mul, ih, pow_succ]
@[scoped simp] theorem val_natCast (n : ℕ) : val ((n : decDVR A)) = n := by
  induction n with
  | zero => rfl
  | succ n ih => push_cast; rw [val_add, ih, val_one]

theorem val_ne_zero {z : decDVR A} (hz : z ≠ 0) : val z ≠ 0 := fun h => hz (val_injective (by rw [h, val_zero]))

def mkO (x : AlgebraicClosure ℚ) (hxA : x ∈ A)
    (hxD : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ → σ x = x) : decDVR A :=
  ⟨⟨x, mem_decField_iff.mpr hxD⟩, hxA⟩

@[scoped simp] theorem val_mkO (x : AlgebraicClosure ℚ) (hxA : x ∈ A) (hxD) : val (mkO x hxA hxD) = x := rfl

theorem isUnit_of_inv_memA {z : decDVR A} (hz : z ≠ 0) (hinv : (val z)⁻¹ ∈ A) : IsUnit z := by
  have hzF : (z : decField A) ≠ 0 := fun h => hz (Subtype.ext h)
  let w : decDVR A := ⟨(z : decField A)⁻¹, by
    show algebraMap (decField A) (AlgebraicClosure ℚ) ((z : decField A)⁻¹) ∈ A
    rw [map_inv₀]; exact hinv⟩
  refine isUnit_iff_exists_inv.mpr ⟨w, Subtype.ext ?_⟩
  show (z : decField A) * (z : decField A)⁻¹ = 1
  exact mul_inv_cancel₀ hzF

theorem valuation_val_eq_one_of_isUnit {z : decDVR A} (hz : IsUnit z) : A.valuation (val z) = 1 := by
  obtain ⟨u, rfl⟩ := hz
  have h1 : val (u : decDVR A) * val (↑u⁻¹ : decDVR A) = 1 := by rw [← val_mul, Units.mul_inv, val_one]
  have hle1 : A.valuation (val (u : decDVR A)) ≤ 1 := (A.valuation_le_one_iff _).mpr (val_memA _)
  have hle2 : A.valuation (val (↑u⁻¹ : decDVR A)) ≤ 1 := (A.valuation_le_one_iff _).mpr (val_memA _)
  have hprod : A.valuation (val (u : decDVR A)) * A.valuation (val (↑u⁻¹ : decDVR A)) = 1 := by
    rw [← map_mul, h1, map_one]
  by_contra hne
  have hlt : A.valuation (val (u : decDVR A)) < 1 := lt_of_le_of_ne hle1 hne
  have : A.valuation (val (u : decDVR A)) * A.valuation (val (↑u⁻¹ : decDVR A)) < 1 :=
    mul_lt_one_of_lt_of_le hlt hle2
  rw [hprod] at this
  exact lt_irrefl _ this

private theorem _root_.P2MMultO.not_isUnit_of_valuation_lt_one {z : decDVR A} (hz : A.valuation (val z) < 1) : ¬ IsUnit z := by
  intro hu
  rw [valuation_val_eq_one_of_isUnit hu] at hz
  exact lt_irrefl _ hz

p2m_export "P2MMultO" "not_isUnit_of_valuation_lt_one"
variable (ℓ : ℕ) [Fact ℓ.Prime] (hA : ((ℓ : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits)
include hA

omit hA in
theorem natCast_fixed (n : ℕ) : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ →
    σ ((n : ℕ) : AlgebraicClosure ℚ) = n := fun σ _ => map_natCast σ n

omit [Fact ℓ.Prime] in
theorem not_isUnit_ell : ¬ IsUnit ((ℓ : ℕ) : decDVR A) := by
  apply not_isUnit_of_valuation_lt_one
  rw [val_natCast]
  exact (A.mem_nonunits_iff).mp hA

theorem envelope₂ (x y : decDVR A) :
    ∃ O' : Subring (AlgebraicClosure ℚ), val x ∈ O' ∧ val y ∈ O' ∧ (O' : Set (AlgebraicClosure ℚ)) ⊆ A ∧
      IsDiscreteValuationRing O' ∧ Irreducible ((ℓ : ℕ) : O') := by
  classical
  obtain ⟨O', hS, hOA, -, hdvr, hirr, -⟩ :=
    ValuationSubring.exists_dvr_subring_of_forall_mem_decompositionSubgroup ℓ A hA {val x, val y} (by
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact ⟨val_memA x, val_fixed x⟩
      · rw [Finset.mem_singleton] at ht; subst ht; exact ⟨val_memA y, val_fixed y⟩)
  refine ⟨O', hS (by simp), hS (by simp), hOA, hdvr, hirr⟩

private theorem _root_.P2MMultO.irreducible_ell : Irreducible ((ℓ : ℕ) : decDVR A) := by
  refine ⟨not_isUnit_ell ℓ hA, fun a b hab => ?_⟩
  obtain ⟨O', haO, hbO, hOA, hdvr, hirr⟩ := envelope₂ ℓ hA a b
  let a' : O' := ⟨val a, haO⟩
  let b' : O' := ⟨val b, hbO⟩
  have hab' : ((ℓ : ℕ) : O') = a' * b' := by
    apply Subtype.ext
    show ((ℓ : ℕ) : O').1 = val a * val b
    rw [← val_mul, ← hab, val_natCast]; simp
  have hne0 : ((ℓ : ℕ) : decDVR A) ≠ 0 := hirr_ne_zero
  have ha0 : a ≠ 0 := by rintro rfl; exact hne0 (by rw [hab, zero_mul])
  have hb0 : b ≠ 0 := by rintro rfl; exact hne0 (by rw [hab, mul_zero])

  have key : ∀ (c : decDVR A) (c' : O'), c ≠ 0 → (c' : AlgebraicClosure ℚ) = val c → IsUnit c' → IsUnit c := by
    intro c c' hc0 hcc' hu
    obtain ⟨u, hu⟩ := hu
    apply isUnit_of_inv_memA hc0
    have h1 : ((u : O') : AlgebraicClosure ℚ) * ((↑u⁻¹ : O') : AlgebraicClosure ℚ) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv]; rfl
    rw [hu, hcc'] at h1
    rw [← eq_inv_of_mul_eq_one_right h1]
    exact hOA (↑u⁻¹ : O').2
  rcases hirr.isUnit_or_isUnit hab' with hu | hu
  · exact Or.inl (key a a' ha0 rfl hu)
  · exact Or.inr (key b b' hb0 rfl hu)
  where
    hirr_ne_zero : ((ℓ : ℕ) : decDVR A) ≠ 0 := by
      intro h
      have := congrArg val h
      rw [val_natCast, val_zero] at this
      exact (Fact.out : ℓ.Prime).ne_zero (by exact_mod_cast this)

p2m_export "P2MMultO" "irreducible_ell"

theorem exists_associated_pow (x : decDVR A) (hx : x ≠ 0) : ∃ n : ℕ, Associated (((ℓ : ℕ) : decDVR A) ^ n) x := by
  obtain ⟨O', hxO, -, hOA, hdvr, hirr⟩ := envelope₂ ℓ hA x x
  haveI := hdvr
  let x' : O' := ⟨val x, hxO⟩
  have hx' : x' ≠ 0 := fun h => val_ne_zero hx (congrArg Subtype.val h)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx' hirr

  have hval : val x * ((u : O') : AlgebraicClosure ℚ) = (ℓ : AlgebraicClosure ℚ) ^ n := by
    have := congrArg Subtype.val hu
    simpa using this
  have huinv : ((u : O') : AlgebraicClosure ℚ) * ((↑u⁻¹ : O') : AlgebraicClosure ℚ) = 1 := by
    rw [← Subring.coe_mul, Units.mul_inv]; rfl
  have hu0 : ((u : O') : AlgebraicClosure ℚ) ≠ 0 := left_ne_zero_of_mul_eq_one huinv

  have hueq : ((u : O') : AlgebraicClosure ℚ) = (ℓ : AlgebraicClosure ℚ) ^ n * (val x)⁻¹ := by
    rw [← hval]; field_simp [val_ne_zero hx]
  have huD : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ →
      σ ((u : O') : AlgebraicClosure ℚ) = ((u : O') : AlgebraicClosure ℚ) := by
    intro σ hσ
    rw [hueq, map_mul, map_pow, map_natCast, map_inv₀, val_fixed x σ hσ]
  let uO : decDVR A := mkO ((u : O') : AlgebraicClosure ℚ) (hOA (u : O').2) huD
  have huO0 : uO ≠ 0 := by
    intro h
    have := congrArg val h
    rw [val_zero] at this
    exact hu0 this
  have huOunit : IsUnit uO := by
    apply isUnit_of_inv_memA huO0
    have : (val uO)⁻¹ = ((↑u⁻¹ : O') : AlgebraicClosure ℚ) := by
      show (((u : O') : AlgebraicClosure ℚ))⁻¹ = _
      exact (eq_inv_of_mul_eq_one_right huinv).symm
    rw [this]; exact hOA (↑u⁻¹ : O').2
  obtain ⟨w, hw⟩ := huOunit
  refine ⟨n, w⁻¹, ?_⟩

  have hxu : x * uO = ((ℓ : ℕ) : decDVR A) ^ n := by
    apply val_injective
    rw [val_mul, val_mkO, hval, val_pow, val_natCast]
  rw [← hxu, ← hw, mul_assoc, Units.mul_inv, mul_one]

private theorem _root_.P2MMultO.isDiscreteValuationRing : IsDiscreteValuationRing (decDVR A) :=
  IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨((ℓ : ℕ) : decDVR A), irreducible_ell ℓ hA, fun {x} hx => exists_associated_pow ℓ hA x hx⟩

p2m_export "P2MMultO" "isDiscreteValuationRing"
end P2MMultO
p2m_reactivate "P2MW.S_ValuationSubring_isDiscreteValuationRing_inf_fixedField_decompositionSubgroup.P2MMultO"

end
p2m_reactivate "P2MW.S_ValuationSubring_isDiscreteValuationRing_inf_fixedField_decompositionSubgroup.P2MMultO"

noncomputable section
namespace P2MMultOR

open P2MMultO

variable (A : ValuationSubring (AlgebraicClosure ℚ))

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

def decRing : Subring ℚ̄ := A.toSubring ⊓ (decField A).toSubring

variable {A} in
theorem mem_decRing_iff {x : ℚ̄} : x ∈ decRing A ↔ x ∈ A ∧ x ∈ decField A := by
  rw [decRing, Subring.mem_inf]
  exact Iff.rfl

def decRingEquiv : ↥(decDVR A) ≃+* ↥(decRing A) where
  toFun z := ⟨val z, mem_decRing_iff.mpr ⟨val_memA z, (z : decField A).2⟩⟩
  invFun x := ⟨⟨(x : ℚ̄), (mem_decRing_iff.mp x.2).2⟩, (ValuationSubring.mem_comap).mpr (mem_decRing_iff.mp x.2).1⟩
  left_inv z := rfl
  right_inv x := rfl
  map_mul' a b := Subtype.ext (val_mul a b)
  map_add' a b := Subtype.ext (val_add a b)

theorem coe_decRingEquiv (z : decDVR A) : ((decRingEquiv A z : decRing A) : ℚ̄) = val z := rfl

theorem decRingEquiv_symm_coe (x : decRing A) : val ((decRingEquiv A).symm x) = (x : ℚ̄) := by
  rw [← coe_decRingEquiv, RingEquiv.apply_symm_apply]

variable {A} in

def mkO (x : ℚ̄) (hxA : x ∈ A) (hfix : ∀ σ : Gal, σ ∈ A.decompositionSubgroup ℚ → σ x = x) : decRing A :=
  ⟨x, mem_decRing_iff.mpr ⟨hxA, mem_decField_iff.mpr hfix⟩⟩

@[scoped simp] theorem coe_mkO (x : ℚ̄) (hxA : x ∈ A) (hfix : ∀ σ : Gal, σ ∈ A.decompositionSubgroup ℚ → σ x = x) :
    ((mkO x hxA hfix : decRing A) : ℚ̄) = x := rfl

theorem coe_memA (x : decRing A) : (x : ℚ̄) ∈ A := (mem_decRing_iff.mp x.2).1

theorem coe_mem_decField (x : decRing A) : (x : ℚ̄) ∈ decField A := (mem_decRing_iff.mp x.2).2

theorem coe_fixed (x : decRing A) (σ : Gal) (hσ : σ ∈ A.decompositionSubgroup ℚ) : σ (x : ℚ̄) = x :=
  mem_decField_iff.mp (coe_mem_decField A x) σ hσ

private theorem _root_.P2MMultOR.mem_or_inv_mem {x : ℚ̄} (hx : x ∈ decField A) : x ∈ decRing A ∨ x⁻¹ ∈ decRing A := by
  rcases A.mem_or_inv_mem x with h | h
  · exact Or.inl (mem_decRing_iff.mpr ⟨h, hx⟩)
  · exact Or.inr (mem_decRing_iff.mpr ⟨h, IntermediateField.inv_mem _ hx⟩)

p2m_export "P2MMultOR" "mem_or_inv_mem"

private theorem _root_.P2MMultOR.not_isUnit_of_valuation_lt_one (x : decRing A) (hx : A.valuation (x : ℚ̄) < 1) : ¬ IsUnit x := by
  intro hu
  have hu' : IsUnit ((decRingEquiv A).symm x) := hu.map (decRingEquiv A).symm
  have hx' : A.valuation (val ((decRingEquiv A).symm x)) < 1 := by rwa [decRingEquiv_symm_coe]
  exact P2MMultO.not_isUnit_of_valuation_lt_one (A := A) hx' hu'

p2m_export "P2MMultOR" "not_isUnit_of_valuation_lt_one"
theorem isLocalRing (ℓ : ℕ) [Fact ℓ.Prime] (hA : ((ℓ : ℕ) : ℚ̄) ∈ A.nonunits) : IsLocalRing (decRing A) :=
  haveI := P2MMultO.isDiscreteValuationRing (A := A) ℓ hA
  IsLocalRing.of_surjective' (decRingEquiv A).toRingHom (decRingEquiv A).surjective

theorem isPrincipalIdealRing (ℓ : ℕ) [Fact ℓ.Prime] (hA : ((ℓ : ℕ) : ℚ̄) ∈ A.nonunits) :
    IsPrincipalIdealRing (decRing A) :=
  haveI := P2MMultO.isDiscreteValuationRing (A := A) ℓ hA
  IsPrincipalIdealRing.of_surjective (decRingEquiv A).toRingHom (decRingEquiv A).surjective

private theorem _root_.P2MMultOR.irreducible_ell (ℓ : ℕ) [Fact ℓ.Prime] (hA : ((ℓ : ℕ) : ℚ̄) ∈ A.nonunits) :
    Irreducible ((ℓ : ℕ) : decRing A) := by
  have h := P2MMultO.irreducible_ell (A := A) ℓ hA
  have : ((ℓ : ℕ) : decRing A) = decRingEquiv A ((ℓ : ℕ) : decDVR A) := by rw [map_natCast]
  rw [this]
  exact (MulEquiv.irreducible_iff (decRingEquiv A).toMulEquiv).mpr h

p2m_export "P2MMultOR" "irreducible_ell"

private theorem _root_.P2MMultOR.isDiscreteValuationRing (ℓ : ℕ) [Fact ℓ.Prime] (hA : ((ℓ : ℕ) : ℚ̄) ∈ A.nonunits) :
    IsDiscreteValuationRing (decRing A) := by
  haveI := isLocalRing A ℓ hA
  haveI := isPrincipalIdealRing A ℓ hA
  refine { (inferInstance : IsPrincipalIdealRing (decRing A)), (inferInstance : IsLocalRing (decRing A)) with
    not_a_field' := ?_ }
  intro hbot
  have hmem : ((ℓ : ℕ) : decRing A) ∈ IsLocalRing.maximalIdeal (decRing A) :=
    (IsLocalRing.mem_maximalIdeal _).mpr (irreducible_ell A ℓ hA).not_isUnit
  rw [hbot, Ideal.mem_bot] at hmem
  exact (irreducible_ell A ℓ hA).ne_zero hmem

p2m_export "P2MMultOR" "isDiscreteValuationRing"

scoped instance instAlgebraField : Algebra (decRing A) (decField A) :=
  (({ toFun := fun x => ⟨(x : ℚ̄), coe_mem_decField A x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl } : decRing A →+* decField A)).toAlgebra

theorem algebraMap_field_coe (x : decRing A) : ((algebraMap (decRing A) (decField A) x : decField A) : ℚ̄) = x := rfl

scoped instance instTowerField : IsScalarTower (decRing A) (decField A) ℚ̄ :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

scoped instance instIsFractionRing : IsFractionRing (decRing A) (decField A) where
  map_units y := by
    apply IsUnit.mk0
    intro h0
    have : ((y.1 : decRing A) : ℚ̄) = 0 := by
      have := congrArg (fun z : decField A => (z : ℚ̄)) h0
      exact this
    exact nonZeroDivisors.ne_zero y.2 (Subtype.ext this)
  surj k := by
    by_cases hk0 : (k : ℚ̄) = 0
    · refine ⟨(0, 1), ?_⟩
      have : k = 0 := Subtype.ext hk0
      rw [this]; simp
    rcases mem_or_inv_mem A k.2 with h | h
    · refine ⟨(⟨k, h⟩, 1), ?_⟩
      show k * algebraMap (decRing A) (decField A) 1 = algebraMap (decRing A) (decField A) ⟨k, h⟩
      rw [map_one, mul_one]
      exact Subtype.ext rfl
    · have hne : (⟨(k : ℚ̄)⁻¹, h⟩ : decRing A) ∈ nonZeroDivisors (decRing A) :=
        mem_nonZeroDivisors_of_ne_zero (fun h0 => hk0 (inv_eq_zero.mp (congrArg (fun z : decRing A => (z : ℚ̄)) h0)))
      refine ⟨(1, ⟨⟨(k : ℚ̄)⁻¹, h⟩, hne⟩), ?_⟩
      show k * algebraMap (decRing A) (decField A) ⟨(k : ℚ̄)⁻¹, h⟩ = algebraMap (decRing A) (decField A) 1
      rw [map_one]
      apply Subtype.ext
      show (k : ℚ̄) * (k : ℚ̄)⁻¹ = 1
      exact mul_inv_cancel₀ hk0
  exists_of_eq {a b} h := ⟨1, by
    have : ((a : ℚ̄)) = b := by
      have := congrArg (fun z : decField A => (z : ℚ̄)) h
      exact this
    rw [Subtype.ext this]⟩

end P2MMultOR
p2m_reactivate "P2MW.S_ValuationSubring_isDiscreteValuationRing_inf_fixedField_decompositionSubgroup.P2MMultO P2MW.S_ValuationSubring_isDiscreteValuationRing_inf_fixedField_decompositionSubgroup.P2MMultOR"
end
p2m_reactivate "P2MW.S_ValuationSubring_isDiscreteValuationRing_inf_fixedField_decompositionSubgroup.P2MMultO P2MW.S_ValuationSubring_isDiscreteValuationRing_inf_fixedField_decompositionSubgroup.P2MMultOR"

set_option maxHeartbeats 1600000 in

theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ) [Fact ℓ.Prime] (hA : A.LiesOverPrime ℓ) :
    IsDiscreteValuationRing ↥((A.toSubring) ⊓ (IntermediateField.fixedField (A.decompositionSubgroup ℚ)).toSubring) ∧
      Irreducible ((ℓ : ℕ) : ↥((A.toSubring) ⊓ (IntermediateField.fixedField (A.decompositionSubgroup ℚ)).toSubring)) ∧
      ∀ x : ↥((A.toSubring) ⊓ (IntermediateField.fixedField (A.decompositionSubgroup ℚ)).toSubring),
        A.valuation (x : AlgebraicClosure ℚ) < 1 → ¬ IsUnit x :=
  ⟨P2MMultOR.isDiscreteValuationRing A ℓ hA, P2MMultOR.irreducible_ell A ℓ hA,
    fun x hx => P2MMultOR.not_isUnit_of_valuation_lt_one A x hx⟩

end S_ValuationSubring_isDiscreteValuationRing_inf_fixedField_decompositionSubgroup
end P2MW
export P2MW.S_ValuationSubring_isDiscreteValuationRing_inf_fixedField_decompositionSubgroup (solution)
