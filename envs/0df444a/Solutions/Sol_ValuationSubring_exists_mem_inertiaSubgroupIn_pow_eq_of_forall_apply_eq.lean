-- Prove2me | solution 1 for ValuationSubring.exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/a1ffc943-0946-5376-adf5-a07e819f39bf

import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_GaloisRep_LocalConditions
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.FieldTheory.KummerExtension
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Int.GCD
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Theorems.Thm_ValuationSubring_exists_pow_eq_of_kummer_descent
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq

set_option autoImplicit false

section
open GaloisRep Finset IsLocalRing

namespace WCOTTameR

theorem eq_of_pow_eq_one_of_sub_mem {R : Type} [CommRing R] [IsLocalRing R] {m : ℕ} (hm : m ≠ 0)
    (hmu : IsUnit ((m : ℕ) : R)) (x y : R) (hx : x ^ m = 1) (hy : y ^ m = 1)
    (hxy : x - y ∈ IsLocalRing.maximalIdeal R) : x = y := by
  have htel : (∑ i ∈ range m, x ^ i * y ^ (m - 1 - i)) * (x - y) = 0 := by
    rw [geom_sum₂_mul, hx, hy, sub_self]
  have hres : IsLocalRing.residue R x = IsLocalRing.residue R y := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hxy
  have hyu : IsUnit y := IsUnit.of_pow_eq_one hy hm
  have hS : IsUnit (∑ i ∈ range m, x ^ i * y ^ (m - 1 - i)) := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff]
    have hr : IsLocalRing.residue R (∑ i ∈ range m, x ^ i * y ^ (m - 1 - i)) =
        (m : IsLocalRing.ResidueField R) * IsLocalRing.residue R y ^ (m - 1) := by
      rw [map_sum]
      simp only [map_mul, map_pow, hres]
      exact geom_sum₂_self _ _
    rw [hr]
    have h1 : IsUnit (m : IsLocalRing.ResidueField R) := by
      simpa using hmu.map (IsLocalRing.residue R)
    exact (h1.mul ((hyu.map (IsLocalRing.residue R)).pow (m - 1))).ne_zero
  exact sub_eq_zero.mp ((hS.mul_right_eq_zero).mp htel)

variable {L : Type} [Field L]

theorem mem_of_pow_eq_one (A : ValuationSubring L) {μ : L} {m : ℕ} (hm : m ≠ 0) (hμ : μ ^ m = 1) :
    μ ∈ A := by
  rcases A.mem_or_inv_mem μ with h | h
  · exact h
  · have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [zero_pow hm] at hμ
      exact zero_ne_one hμ
    have h1 : μ ^ (m - 1) = μ⁻¹ := by
      rw [pow_sub₀ μ hμ0 (Nat.one_le_iff_ne_zero.mpr hm), hμ, pow_one, one_mul]
    have h2 : μ = μ⁻¹ ^ (m - 1) := by rw [inv_pow, h1, inv_inv]
    rw [h2]
    exact pow_mem h _

theorem isUnit_natCast_of_coprime (A : ValuationSubring L) {q m : ℕ} (hq : A.LiesOverPrime q)
    (hmq : Nat.Coprime m q) : IsUnit ((m : ℕ) : A) := by
  rw [← IsLocalRing.notMem_maximalIdeal]
  intro hm
  have hqA : ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    simp at hq ⊢
    exact hq
  obtain ⟨u, v, huv⟩ := (Nat.Coprime.cast (R := A) hmq)
  have h1 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← huv]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ hqA)
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

variable {K : Type} [Field K] [Algebra K L]

theorem inertia_fixes_root_of_unity (A : ValuationSubring L) {q : ℕ} (hq : A.LiesOverPrime q)
    {m : ℕ} (hm : m ≠ 0) (hmq : Nat.Coprime m q) (μ : L) (hμ : μ ^ m = 1)
    (σ : L ≃ₐ[K] L) (hσ : σ ∈ A.inertiaSubgroupIn K) : σ μ = μ := by

  obtain ⟨τ, hτI, hτσ⟩ := hσ
  subst hτσ

  have hμA : μ ∈ A := mem_of_pow_eq_one A hm hμ
  have hτμ : ((τ : L ≃ₐ[K] L) μ) ^ m = 1 := by rw [← map_pow, hμ, map_one]
  have hτμA : (τ : L ≃ₐ[K] L) μ ∈ A := mem_of_pow_eq_one A hm hτμ
  set x : A := ⟨(τ : L ≃ₐ[K] L) μ, hτμA⟩
  set y : A := ⟨μ, hμA⟩
  have hx : x ^ m = 1 := Subtype.ext (by
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]; exact hτμ)
  have hy : y ^ m = 1 := Subtype.ext (by
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]; exact hμ)

  have hτy : τ • y = x := rfl
  have hres : IsLocalRing.residue A x = IsLocalRing.residue A y := by
    rw [← hτy, IsLocalRing.ResidueField.residue_smul]
    have hτker : MulSemiringAction.toRingAut (A.decompositionSubgroup K)
        (IsLocalRing.ResidueField A) τ = 1 := hτI
    have := DFunLike.congr_fun (congrArg RingEquiv.toEquiv hτker) (IsLocalRing.residue A y)
    simpa using this
  have hxy : x - y ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hres, sub_self]
  have key := eq_of_pow_eq_one_of_sub_mem hm (isUnit_natCast_of_coprime A hq hmq) x y hx hy hxy
  exact congrArg Subtype.val key

theorem apply_eq_pow_of_isFrobeniusAt (A : ValuationSubring L) (σ : L ≃ₐ[K] L) (q : ℕ)
    (hσ : A.IsFrobeniusAt σ q) (hq : A.LiesOverPrime q) {m : ℕ} (hm : m ≠ 0) (hmq : Nat.Coprime m q)
    (μ : L) (hμ : μ ^ m = 1) : σ μ = μ ^ q := by
  obtain ⟨hσD, hfrob⟩ := hσ
  have hμA : μ ∈ A := mem_of_pow_eq_one A hm hμ
  have hσμ : (σ μ) ^ m = 1 := by rw [← map_pow, hμ, map_one]
  have hσμA : σ μ ∈ A := mem_of_pow_eq_one A hm hσμ
  have hx : (⟨σ μ, hσμA⟩ : A) ^ m = 1 := Subtype.ext (by
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]; exact hσμ)
  have hy : ((⟨μ, hμA⟩ : A) ^ q) ^ m = 1 := Subtype.ext (by
    rw [SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, OneMemClass.coe_one, ← pow_mul, mul_comm, pow_mul]
    change (μ ^ m) ^ q = 1
    rw [hμ, one_pow])
  have hsmul : ((⟨σ, hσD⟩ : A.decompositionSubgroup K) • (⟨μ, hμA⟩ : A)) = ⟨σ μ, hσμA⟩ :=
    Subtype.ext rfl
  have hxy : (⟨σ μ, hσμA⟩ : A) - (⟨μ, hμA⟩ : A) ^ q ∈ IsLocalRing.maximalIdeal A := by
    have h1 := hfrob (IsLocalRing.residue A ⟨μ, hμA⟩)
    rw [← IsLocalRing.ResidueField.residue_smul, hsmul, ← map_pow] at h1
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
    exact h1
  have key := eq_of_pow_eq_one_of_sub_mem hm (isUnit_natCast_of_coprime A hq hmq) _ _ hx hy hxy
  have := congrArg Subtype.val key
  simpa using this

theorem kummer_cocycle_eq (τ : L ≃ₐ[K] L) {m : ℕ}
    (hτμ : ∀ ζ : L, ζ ^ m = 1 → τ ζ = ζ) (c : L)
    (α β : L) (hα : α ^ m = c) (hβ : β ^ m = c) (hα0 : α ≠ 0) (hβ0 : β ≠ 0) :
    τ α / α = τ β / β := by
  have hc0 : c ≠ 0 := by rw [← hα]; exact pow_ne_zero m hα0
  have hζ : (β / α) ^ m = 1 := by rw [div_pow, hα, hβ, div_self hc0]
  have key : τ β = (β / α) * τ α := by
    conv_lhs => rw [← div_mul_cancel₀ β hα0, map_mul, hτμ _ hζ]
  rw [key]; field_simp

theorem apply_pow_eq_cocycle_pow_mul (τ : L ≃ₐ[K] L) {m : ℕ}
    (hτμ : ∀ ζ : L, ζ ^ m = 1 → τ ζ = ζ) (α : L) (hα0 : α ≠ 0)
    (hcocycle : (τ α / α) ^ m = 1) :
    ∀ n : ℕ, (τ ^ n) α = (τ α / α) ^ n * α := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, hτμ _ hcocycle, pow_succ, mul_assoc]
    congr 1
    rw [div_mul_cancel₀ _ hα0]

theorem frob_conj_eq_pow_on_radical (A : ValuationSubring L) {q : ℕ} (hq : A.LiesOverPrime q)
    {m : ℕ} (hm : m ≠ 0) (hmq : Nat.Coprime m q)
    (τ : L ≃ₐ[K] L) (hτ : τ ∈ A.inertiaSubgroupIn K)
    (σ : L ≃ₐ[K] L) (hσ : A.IsFrobeniusAt σ q)
    (α : L) (hα : α ^ m = (q : L)) (hα0 : α ≠ 0) :
    (σ * τ * σ⁻¹) α = (τ ^ q) α := by

  have hτμ : ∀ ζ : L, ζ ^ m = 1 → τ ζ = ζ :=
    fun ζ hζ => inertia_fixes_root_of_unity A hq hm hmq ζ hζ τ hτ

  have hσμ : ∀ ζ : L, ζ ^ m = 1 → σ ζ = ζ ^ q :=
    fun ζ hζ => apply_eq_pow_of_isFrobeniusAt A σ q hσ hq hm hmq ζ hζ

  have hq0 : (q : L) ≠ 0 := hα ▸ pow_ne_zero m hα0

  have hτqL : τ ((q : L)) = q := map_natCast τ q

  set χ := τ α / α with hχdef
  have hχm : χ ^ m = 1 := by
    rw [hχdef, div_pow, ← map_pow, hα, hτqL, div_self hq0]

  have hRHS : (τ ^ q) α = χ ^ q * α := apply_pow_eq_cocycle_pow_mul τ hτμ α hα0 hχm q

  have hLHS : (σ * τ * σ⁻¹) α = χ ^ q * α := by
    have hβm : (σ⁻¹ α) ^ m = (q : L) := by
      rw [← map_pow, hα]; exact map_natCast σ⁻¹ q
    have hβ0 : σ⁻¹ α ≠ 0 := by
      simp only [ne_eq, AddEquivClass.map_eq_zero_iff]; exact hα0
    have hcoc : τ α / α = τ (σ⁻¹ α) / (σ⁻¹ α) :=
      kummer_cocycle_eq τ hτμ (q : L) α (σ⁻¹ α) hα hβm hα0 hβ0
    have key : τ (σ⁻¹ α) = χ * (σ⁻¹ α) := by
      rw [hχdef, hcoc, div_mul_cancel₀ _ hβ0]
    calc (σ * τ * σ⁻¹) α = σ (τ (σ⁻¹ α)) := by simp only [AlgEquiv.mul_apply]
    _ = σ (χ * σ⁻¹ α) := by rw [key]
    _ = σ χ * σ (σ⁻¹ α) := by rw [map_mul]
    _ = χ ^ q * α := by
        rw [hσμ _ hχm, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  rw [hLHS, hRHS]

end WCOTTameR

end

section
open GaloisRep Finset IsLocalRing

namespace WCOTTameRp

theorem eq_of_pow_eq_one_of_sub_mem {R : Type} [CommRing R] [IsLocalRing R] {m : ℕ} (hm : m ≠ 0)
    (hmu : IsUnit ((m : ℕ) : R)) (x y : R) (hx : x ^ m = 1) (hy : y ^ m = 1)
    (hxy : x - y ∈ IsLocalRing.maximalIdeal R) : x = y := by
  have htel : (∑ i ∈ range m, x ^ i * y ^ (m - 1 - i)) * (x - y) = 0 := by
    rw [geom_sum₂_mul, hx, hy, sub_self]
  have hres : IsLocalRing.residue R x = IsLocalRing.residue R y := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hxy
  have hyu : IsUnit y := IsUnit.of_pow_eq_one hy hm
  have hS : IsUnit (∑ i ∈ range m, x ^ i * y ^ (m - 1 - i)) := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff]
    have hr : IsLocalRing.residue R (∑ i ∈ range m, x ^ i * y ^ (m - 1 - i)) =
        (m : IsLocalRing.ResidueField R) * IsLocalRing.residue R y ^ (m - 1) := by
      rw [map_sum]; simp only [map_mul, map_pow, hres]; exact geom_sum₂_self _ _
    rw [hr]
    have h1 : IsUnit (m : IsLocalRing.ResidueField R) := by
      simpa using hmu.map (IsLocalRing.residue R)
    exact (h1.mul ((hyu.map (IsLocalRing.residue R)).pow (m - 1))).ne_zero
  exact sub_eq_zero.mp ((hS.mul_right_eq_zero).mp htel)

variable {L : Type} [Field L]

theorem mem_of_pow_eq_one (A : ValuationSubring L) {μ : L} {m : ℕ} (hm : m ≠ 0) (hμ : μ ^ m = 1) :
    μ ∈ A := by
  rcases A.mem_or_inv_mem μ with h | h
  · exact h
  · have hμ0 : μ ≠ 0 := by rintro rfl; rw [zero_pow hm] at hμ; exact zero_ne_one hμ
    have h1 : μ ^ (m - 1) = μ⁻¹ := by
      rw [pow_sub₀ μ hμ0 (Nat.one_le_iff_ne_zero.mpr hm), hμ, pow_one, one_mul]
    have h2 : μ = μ⁻¹ ^ (m - 1) := by rw [inv_pow, h1, inv_inv]
    rw [h2]; exact pow_mem h _

theorem isUnit_natCast_of_coprime (A : ValuationSubring L) {q m : ℕ} (hq : A.LiesOverPrime q)
    (hmq : Nat.Coprime m q) : IsUnit ((m : ℕ) : A) := by
  rw [← IsLocalRing.notMem_maximalIdeal]
  intro hm
  have hqA : ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]; (simp at hq ⊢; exact hq)
  obtain ⟨u, v, huv⟩ := (Nat.Coprime.cast (R := A) hmq)
  have h1 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← huv]; exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ hqA)
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

variable {K : Type} [Field K] [Algebra K L]

private theorem _root_.WCOTTameRp.inertia_fixes_root_of_unity (A : ValuationSubring L) {q : ℕ} (hq : A.LiesOverPrime q)
    {m : ℕ} (hm : m ≠ 0) (hmq : Nat.Coprime m q) (μ : L) (hμ : μ ^ m = 1)
    (σ : L ≃ₐ[K] L) (hσ : σ ∈ A.inertiaSubgroupIn K) : σ μ = μ := by
  obtain ⟨τ, hτI, hτσ⟩ := hσ
  subst hτσ
  have hμA : μ ∈ A := mem_of_pow_eq_one A hm hμ
  have hτμ : ((τ : L ≃ₐ[K] L) μ) ^ m = 1 := by rw [← map_pow, hμ, map_one]
  have hτμA : (τ : L ≃ₐ[K] L) μ ∈ A := mem_of_pow_eq_one A hm hτμ
  set x : A := ⟨(τ : L ≃ₐ[K] L) μ, hτμA⟩
  set y : A := ⟨μ, hμA⟩
  have hx : x ^ m = 1 := Subtype.ext (by
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]; exact hτμ)
  have hy : y ^ m = 1 := Subtype.ext (by
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]; exact hμ)
  have hτy : τ • y = x := rfl
  have hres : IsLocalRing.residue A x = IsLocalRing.residue A y := by
    rw [← hτy, IsLocalRing.ResidueField.residue_smul]
    have hτker : MulSemiringAction.toRingAut (A.decompositionSubgroup K)
        (IsLocalRing.ResidueField A) τ = 1 := hτI
    have := DFunLike.congr_fun (congrArg RingEquiv.toEquiv hτker) (IsLocalRing.residue A y)
    simpa using this
  have hxy : x - y ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hres, sub_self]
  have key := eq_of_pow_eq_one_of_sub_mem hm (isUnit_natCast_of_coprime A hq hmq) x y hx hy hxy
  exact congrArg Subtype.val key

p2m_export "WCOTTameRp" "inertia_fixes_root_of_unity"

noncomputable def residueRootOfUnity (A : ValuationSubring L) {m : ℕ} (hm : m ≠ 0)
    (ζ : L) (hζ : ζ ^ m = 1) : IsLocalRing.ResidueField A :=
  IsLocalRing.residue A ⟨ζ, mem_of_pow_eq_one A hm hζ⟩

theorem residueRootOfUnity_pow (A : ValuationSubring L) {m : ℕ} (hm : m ≠ 0)
    (ζ : L) (hζ : ζ ^ m = 1) : (residueRootOfUnity A hm ζ hζ) ^ m = 1 := by
  rw [residueRootOfUnity, ← map_pow, ← map_one (IsLocalRing.residue A)]
  congr 1
  exact Subtype.ext (by simpa using hζ)

theorem residueRootOfUnity_injective (A : ValuationSubring L) {m : ℕ} (hm : m ≠ 0)
    (hmu : IsUnit ((m : ℕ) : A)) (ζ ξ : L) (hζ : ζ ^ m = 1) (hξ : ξ ^ m = 1)
    (hres : residueRootOfUnity A hm ζ hζ = residueRootOfUnity A hm ξ hξ) : ζ = ξ := by
  set x : A := ⟨ζ, mem_of_pow_eq_one A hm hζ⟩
  set y : A := ⟨ξ, mem_of_pow_eq_one A hm hξ⟩
  have hx : x ^ m = 1 := Subtype.ext (by simpa using hζ)
  have hy : y ^ m = 1 := Subtype.ext (by simpa using hξ)
  have hxy : x - y ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]; exact hres
  exact congrArg Subtype.val (eq_of_pow_eq_one_of_sub_mem hm hmu x y hx hy hxy)

theorem exists_residue_eq_of_pow_eq_one (A : ValuationSubring L) {m : ℕ} (hm : m ≠ 0)
    (hmu : IsUnit ((m : ℕ) : A)) (ζ₀ : L) (hζ₀ : IsPrimitiveRoot ζ₀ m)
    (η : IsLocalRing.ResidueField A) (hη : η ^ m = 1) :
    ∃ (ζ : L) (hζ : ζ ^ m = 1), residueRootOfUnity A hm ζ hζ = η := by
  classical
  have hm' : 0 < m := Nat.pos_of_ne_zero hm

  set f : Fin m → IsLocalRing.ResidueField A := fun i =>
    residueRootOfUnity A hm (ζ₀ ^ (i : ℕ)) (by rw [← pow_mul, mul_comm, pow_mul, hζ₀.pow_eq_one,
      one_pow])
  have hfmem : ∀ i : Fin m, f i ∈ Polynomial.nthRootsFinset m (1 : IsLocalRing.ResidueField A) := by
    intro i
    rw [Polynomial.mem_nthRootsFinset hm']
    exact residueRootOfUnity_pow A hm _ _
  have hfinj : Function.Injective f := by
    intro i j hij
    have hpow : ζ₀ ^ (i : ℕ) = ζ₀ ^ (j : ℕ) :=
      residueRootOfUnity_injective A hm hmu _ _ _ _ hij
    exact Fin.ext (hζ₀.pow_inj i.2 j.2 hpow)

  have hcard : (Polynomial.nthRootsFinset m (1 : IsLocalRing.ResidueField A)).card ≤ m := by
    classical
    rw [Polynomial.nthRootsFinset_def]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots m 1)

  have himage : (Finset.univ.image f) = Polynomial.nthRootsFinset m (1 : IsLocalRing.ResidueField A) := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hfmem i
    · rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_fin]
      exact hcard

  have hηmem : η ∈ Polynomial.nthRootsFinset m (1 : IsLocalRing.ResidueField A) :=
    (Polynomial.mem_nthRootsFinset hm' 1).mpr hη
  rw [← himage] at hηmem
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hηmem
  exact ⟨ζ₀ ^ (i : ℕ), _, rfl⟩

theorem exists_mem_fixedField_residue_eq [IsAlgClosed L] [CharZero L]
    (A : ValuationSubring L) {p q : ℕ} (hp : p.Prime) (hq : A.LiesOverPrime q) (hpq : p ≠ q)
    (hqprime : q.Prime) (i : ℕ) (y : IsLocalRing.ResidueField A) (hy : y ^ (p ^ i) = 1) :
    ∃ ζ : L,
      ζ ∈ IntermediateField.fixedField
        ((A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype) ∧
      ∃ hζA : ζ ∈ A, IsLocalRing.residue A ⟨ζ, hζA⟩ = y := by
  have hm : p ^ i ≠ 0 := pow_ne_zero i hp.ne_zero
  have hmq : (p ^ i).Coprime q :=
    Nat.Coprime.pow_left i ((Nat.coprime_primes hp hqprime).mpr hpq)
  have hmu : IsUnit ((p ^ i : ℕ) : A) := isUnit_natCast_of_coprime A hq hmq
  haveI : NeZero ((p ^ i : ℕ) : L) := ⟨Nat.cast_ne_zero.mpr hm⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L (p ^ i)
  obtain ⟨ζ, hζ, hres⟩ := exists_residue_eq_of_pow_eq_one A hm hmu ζ₀ hζ₀ y hy
  refine ⟨ζ, ?_, mem_of_pow_eq_one A hm hζ, hres⟩
  rw [IntermediateField.mem_fixedField_iff]
  intro τ hτ
  exact inertia_fixes_root_of_unity A hq hm hmq ζ hζ τ hτ

end WCOTTameRp

end

section
open IntermediateField
open scoped Pointwise

namespace WCOTTameU

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem isClosed_apply_mem [Algebra.IsIntegral K L] (A : ValuationSubring L) (x : L) :
    IsClosed {σ : L ≃ₐ[K] L | σ x ∈ A} := by
  rw [← isOpen_compl_iff]
  have hcompl : {σ : L ≃ₐ[K] L | σ x ∈ A}ᶜ =
      ⋃ σ₀ ∈ {σ : L ≃ₐ[K] L | σ x ∉ A},
        σ₀ • (MulAction.stabilizer (L ≃ₐ[K] L) x : Set (L ≃ₐ[K] L)) := by
    ext σ
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro h
      refine ⟨σ, h, ?_⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      simp
    · rintro ⟨σ₀, h₀, hmem⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem] at hmem
      have hfix : (σ₀⁻¹ * σ) • x = x := hmem
      rw [mul_smul] at hfix
      have hx : σ • x = σ₀ • x := by
        have := congrArg (σ₀ • ·) hfix
        simpa [smul_smul] using this
      intro hA
      apply h₀
      have : σ₀ x = σ x := by simpa [AlgEquiv.smul_def] using hx.symm
      rwa [this]
  rw [hcompl]
  exact isOpen_biUnion fun σ₀ _ =>
    (stabilizer_isOpen_of_isIntegral (K := K) x).smul σ₀

theorem isClosed_decompositionSubgroup [Algebra.IsIntegral K L] (A : ValuationSubring L) :
    IsClosed ((A.decompositionSubgroup K : Subgroup (L ≃ₐ[K] L)) : Set (L ≃ₐ[K] L)) := by
  have hS : IsClosed {σ : L ≃ₐ[K] L | ∀ x ∈ A, σ x ∈ A} := by
    have hset : {σ : L ≃ₐ[K] L | ∀ x ∈ A, σ x ∈ A} =
        ⋂ x ∈ (A : Set L), {σ : L ≃ₐ[K] L | σ x ∈ A} := by
      ext σ; simp
    rw [hset]
    exact isClosed_biInter fun x _ => isClosed_apply_mem A x
  have hset : ((A.decompositionSubgroup K : Subgroup (L ≃ₐ[K] L)) : Set (L ≃ₐ[K] L)) =
      {σ : L ≃ₐ[K] L | ∀ x ∈ A, σ x ∈ A} ∩
        (fun σ : L ≃ₐ[K] L => σ⁻¹) ⁻¹' {σ : L ≃ₐ[K] L | ∀ x ∈ A, σ x ∈ A} := by
    ext σ
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · intro hσ
      have h : σ • A = A := hσ
      constructor
      · intro x hx
        have hmem : σ • x ∈ σ • A := ValuationSubring.smul_mem_pointwise_smul σ x A hx
        rw [h] at hmem
        simpa [AlgEquiv.smul_def] using hmem
      · intro x hx
        rw [← h] at hx
        have := ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem.mp hx
        simpa [AlgEquiv.smul_def] using this
    · rintro ⟨h₁, h₂⟩
      show σ • A = A
      ext y
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      constructor
      · intro hy
        have := h₁ _ hy
        simpa [AlgEquiv.smul_def, smul_inv_smul] using this
      · intro hy
        simpa [AlgEquiv.smul_def] using h₂ y hy
  rw [hset]
  exact hS.inter (hS.preimage continuous_inv)

theorem fixingSubgroup_fixedField_map_inertia_le [IsGalois K L] [Algebra.IsIntegral K L]
    (A : ValuationSubring L) :
    (IntermediateField.fixedField
        ((A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype)).fixingSubgroup ≤
      A.decompositionSubgroup K := by
  have hle : (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype ≤
      A.decompositionSubgroup K := by
    rintro σ ⟨τ, _, rfl⟩
    exact τ.2
  have hff : IntermediateField.fixedField (A.decompositionSubgroup K) ≤
      IntermediateField.fixedField
        ((A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype) :=
    IntermediateField.fixedField_le hle
  have hfix := IntermediateField.fixingSubgroup_antitone hff
  refine hfix.trans (le_of_eq ?_)
  exact InfiniteGalois.fixingSubgroup_fixedField
    ⟨A.decompositionSubgroup K, isClosed_decompositionSubgroup A⟩

theorem smul_eq_self_of_mem_fixingSubgroup [IsGalois K L] [Algebra.IsIntegral K L]
    (A : ValuationSubring L) (σ : L ≃ₐ[K] L)
    (hσ : σ ∈ (IntermediateField.fixedField
        ((A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype)).fixingSubgroup) :
    σ • A = A :=
  fixingSubgroup_fixedField_map_inertia_le A hσ

end WCOTTameU

end

section
open IntermediateField
open scoped Pointwise

namespace WCOTTameU

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem fixedField_topologicalClosure_eq [Algebra.IsIntegral K L]
    (H : Subgroup (L ≃ₐ[K] L)) :
    IntermediateField.fixedField H.topologicalClosure = IntermediateField.fixedField H := by
  refine le_antisymm (IntermediateField.fixedField_le (Subgroup.le_topologicalClosure H)) ?_
  intro x hx
  rw [IntermediateField.mem_fixedField_iff] at hx ⊢
  intro σ hσ
  have hstab : (↑H : Set (L ≃ₐ[K] L)) ⊆
      (MulAction.stabilizer (L ≃ₐ[K] L) x : Set (L ≃ₐ[K] L)) := by
    intro τ hτ
    simpa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] using hx τ hτ
  have hclosed : IsClosed (MulAction.stabilizer (L ≃ₐ[K] L) x : Set (L ≃ₐ[K] L)) :=
    Subgroup.isClosed_of_isOpen _ (stabilizer_isOpen_of_isIntegral (K := K) x)
  have hsub : closure (↑H : Set (L ≃ₐ[K] L)) ⊆
      (MulAction.stabilizer (L ≃ₐ[K] L) x : Set (L ≃ₐ[K] L)) :=
    closure_minimal hstab hclosed
  have hσ' : σ ∈ closure (↑H : Set (L ≃ₐ[K] L)) := by
    rwa [← Subgroup.topologicalClosure_coe]
  simpa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] using hsub hσ'

theorem fixingSubgroup_fixedField_eq_topologicalClosure [IsGalois K L]
    [Algebra.IsIntegral K L] (H : Subgroup (L ≃ₐ[K] L)) :
    (IntermediateField.fixedField H).fixingSubgroup = H.topologicalClosure := by
  rw [← fixedField_topologicalClosure_eq H]
  exact InfiniteGalois.fixingSubgroup_fixedField
    ⟨H.topologicalClosure, Subgroup.isClosed_topologicalClosure H⟩

theorem exists_mem_apply_eq_of_mem_fixingSubgroup [IsGalois K L] [Algebra.IsIntegral K L]
    (H : Subgroup (L ≃ₐ[K] L)) (σ : L ≃ₐ[K] L)
    (hσ : σ ∈ (IntermediateField.fixedField H).fixingSubgroup) (x : L) :
    ∃ τ ∈ H, τ x = σ x := by
  have hσc : σ ∈ closure (↑H : Set (L ≃ₐ[K] L)) := by
    rw [← Subgroup.topologicalClosure_coe]
    exact (fixingSubgroup_fixedField_eq_topologicalClosure H) ▸ hσ
  have hU : IsOpen (σ • (MulAction.stabilizer (L ≃ₐ[K] L) x : Set (L ≃ₐ[K] L))) :=
    (stabilizer_isOpen_of_isIntegral (K := K) x).smul σ
  have hσU : σ ∈ σ • (MulAction.stabilizer (L ≃ₐ[K] L) x : Set (L ≃ₐ[K] L)) := by
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp
  obtain ⟨τ, hτU, hτH⟩ := mem_closure_iff.mp hσc _ hU hσU
  refine ⟨τ, hτH, ?_⟩
  rw [Set.mem_smul_set_iff_inv_smul_mem] at hτU
  have : (σ⁻¹ * τ) • x = x := hτU
  rw [mul_smul] at this
  have := congrArg (σ • ·) this
  simpa [smul_smul, AlgEquiv.smul_def] using this

end WCOTTameU

end

section
open IntermediateField
open scoped Pointwise

namespace WCOTTameUI

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem isOpen_setOf_apply [Algebra.IsIntegral K L] (Q : L → Prop) (x : L) :
    IsOpen {σ : L ≃ₐ[K] L | Q (σ x)} := by
  have h : {σ : L ≃ₐ[K] L | Q (σ x)} = ⋃ σ₀ ∈ {σ : L ≃ₐ[K] L | Q (σ x)},
      σ₀ • (MulAction.stabilizer (L ≃ₐ[K] L) x : Set (L ≃ₐ[K] L)) := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro hσ
      refine ⟨σ, hσ, ?_⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      simp
    · rintro ⟨σ₀, h₀, hmem⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem] at hmem
      have hfix : (σ₀⁻¹ * σ) • x = x := hmem
      rw [mul_smul] at hfix
      have hx : σ • x = σ₀ • x := by
        have := congrArg (σ₀ • ·) hfix
        simpa [smul_smul] using this
      have : σ x = σ₀ x := by simpa [AlgEquiv.smul_def] using hx
      rw [this]
      exact h₀
  rw [h]
  exact isOpen_biUnion fun σ₀ _ => (stabilizer_isOpen_of_isIntegral (K := K) x).smul σ₀

theorem isClosed_setOf_apply [Algebra.IsIntegral K L] (Q : L → Prop) (x : L) :
    IsClosed {σ : L ≃ₐ[K] L | Q (σ x)} := by
  rw [← isOpen_compl_iff]
  have : {σ : L ≃ₐ[K] L | Q (σ x)}ᶜ = {σ : L ≃ₐ[K] L | ¬ Q (σ x)} := by ext; simp
  rw [this]
  exact isOpen_setOf_apply (fun y => ¬ Q y) x

theorem mem_inertia_map_iff (A : ValuationSubring L) (σ : L ≃ₐ[K] L) :
    σ ∈ (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype ↔
      σ ∈ A.decompositionSubgroup K ∧ ∀ a : A, A.valuation (σ a - a) < 1 := by
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    refine ⟨τ.2, fun a => ?_⟩
    change τ ∈ MonoidHom.ker (MulSemiringAction.toRingAut (A.decompositionSubgroup K)
      (IsLocalRing.ResidueField A)) at hτ
    rw [MonoidHom.mem_ker] at hτ
    have h1 : τ • IsLocalRing.residue A a = IsLocalRing.residue A a := RingEquiv.congr_fun hτ _
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff] at h1
    exact h1
  · rintro ⟨hD, hv⟩
    refine ⟨⟨σ, hD⟩, ?_, rfl⟩
    change (⟨σ, hD⟩ : A.decompositionSubgroup K) ∈ MonoidHom.ker (MulSemiringAction.toRingAut
      (A.decompositionSubgroup K) (IsLocalRing.ResidueField A))
    rw [MonoidHom.mem_ker]
    apply RingEquiv.ext
    intro x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    change (⟨σ, hD⟩ : A.decompositionSubgroup K) • IsLocalRing.residue A a = IsLocalRing.residue A a
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff]
    exact hv a

theorem isClosed_inertia_map [Algebra.IsIntegral K L] (A : ValuationSubring L) :
    IsClosed (((A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype : Subgroup (L ≃ₐ[K] L)) :
      Set (L ≃ₐ[K] L)) := by
  have hset : (((A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype : Subgroup (L ≃ₐ[K] L)) :
      Set (L ≃ₐ[K] L)) =
      ((A.decompositionSubgroup K : Subgroup (L ≃ₐ[K] L)) : Set (L ≃ₐ[K] L)) ∩
        ⋂ a : A, {σ : L ≃ₐ[K] L | A.valuation (σ a - a) < 1} := by
    ext σ
    rw [SetLike.mem_coe, mem_inertia_map_iff, Set.mem_inter_iff, SetLike.mem_coe, Set.mem_iInter]
    rfl
  rw [hset]
  exact (WCOTTameU.isClosed_decompositionSubgroup A).inter
    (isClosed_iInter fun a => isClosed_setOf_apply (fun y => A.valuation (y - a) < 1) a)

theorem topologicalClosure_inertia_map [Algebra.IsIntegral K L] (A : ValuationSubring L) :
    ((A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype).topologicalClosure =
      (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype :=
  le_antisymm (Subgroup.topologicalClosure_minimal _ le_rfl (isClosed_inertia_map A))
    (Subgroup.le_topologicalClosure _)

end WCOTTameUI

end

section

namespace WCOTTameJ

variable {G : Type*} [Group G] [TopologicalSpace G]

theorem eq_one_of_forall_mem_openNormalSubgroup [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] [T2Space G]
    (y : G) (hy : ∀ N : OpenNormalSubgroup G, y ∈ N) : y = 1 := by
  by_contra hne
  have hU : IsOpen ({y}ᶜ : Set G) := isClosed_singleton.isOpen_compl
  have h1 : (1 : G) ∈ ({y}ᶜ : Set G) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact fun h => hne h.symm
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hU h1
  exact (hN (hy N)) rfl

theorem exists_pow_mul_inv_mem (N : OpenNormalSubgroup G) {p : ℕ}
    (hcop : (N.toSubgroup.index).Coprime p) (g : G) (k : ℕ) :
    ∃ x : G, (x ^ p ^ k)⁻¹ * g ∈ N.toSubgroup := by
  have hcard : (Nat.card (G ⧸ N.toSubgroup)).Coprime (p ^ k) := by
    rw [← Subgroup.index_eq_card]
    exact hcop.pow_right k
  obtain ⟨xbar, hxbar⟩ := (powCoprime hcard).surjective ((g : G ⧸ N.toSubgroup))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xbar
  refine ⟨x, ?_⟩
  rw [← QuotientGroup.eq, QuotientGroup.mk_pow]
  exact hxbar

theorem exists_pow_pow_eq [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    [T2Space G] {p : ℕ}
    (hidx : ∀ N : OpenNormalSubgroup G, (N.toSubgroup.index).Coprime p)
    (g : G) (k : ℕ) :
    ∃ w : G, w ^ p ^ k = g := by
  haveI : Nonempty (OpenNormalSubgroup G) :=
    ⟨⟨⟨⊤, isOpen_univ⟩, inferInstanceAs ((⊤ : Subgroup G).Normal)⟩⟩
  have hcont : Continuous fun x : G => (x ^ p ^ k)⁻¹ * g :=
    ((continuous_pow (p ^ k)).inv).mul continuous_const
  set C : OpenNormalSubgroup G → Set G :=
    fun N => (fun x : G => (x ^ p ^ k)⁻¹ * g) ⁻¹' (N.toSubgroup : Set G) with hCdef
  have hclosed : ∀ N, IsClosed (C N) := fun N =>
    (N.toOpenSubgroup.isClosed).preimage hcont
  have hne : ∀ N, (C N).Nonempty := fun N => by
    obtain ⟨x, hx⟩ := exists_pow_mul_inv_mem N (hidx N) g k
    exact ⟨x, hx⟩
  have hdir : Directed (· ⊇ ·) C := by
    intro N M
    refine ⟨N ⊓ M, ?_, ?_⟩
    · intro x hx
      exact (Subgroup.mem_inf.mp hx).1
    · intro x hx
      exact (Subgroup.mem_inf.mp hx).2
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir hne
    (fun N => (hclosed N).isCompact) hclosed
  refine ⟨x, ?_⟩
  have hy : ∀ N : OpenNormalSubgroup G, (x ^ p ^ k)⁻¹ * g ∈ N :=
    fun N => Set.mem_iInter.mp hx N
  have h1 : (x ^ p ^ k)⁻¹ * g = 1 := eq_one_of_forall_mem_openNormalSubgroup _ hy
  exact (inv_mul_eq_one.mp h1)

end WCOTTameJ

end

section
open IntermediateField

namespace WCOTTameJ

theorem index_coprime_of_forall_pow_surjective
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {p : ℕ} (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hdiv : ∀ K' : IntermediateField K L, FiniteDimensional K K' →
      ∀ a : K', a ≠ 0 → ∃ b : K', b ^ p = a)
    (N : OpenNormalSubgroup (L ≃ₐ[K] L)) :
    (N.toSubgroup.index).Coprime p := by
  by_contra hcop
  have hdvd : p ∣ N.toSubgroup.index := by
    by_contra hnd
    exact hcop (Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.mpr hnd))

  have hNc : IsClosed ((N.toSubgroup : Subgroup (L ≃ₐ[K] L)) : Set (L ≃ₐ[K] L)) :=
    N.toOpenSubgroup.isClosed
  set M : IntermediateField K L := IntermediateField.fixedField N.toSubgroup with hM
  have hfix : M.fixingSubgroup = N.toSubgroup :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨N.toSubgroup, hNc⟩
  haveI hfin : FiniteDimensional K M := by
    rw [← InfiniteGalois.isOpen_iff_finite M]
    rw [hfix]
    exact N.toOpenSubgroup.isOpen'
  haveI hgal : IsGalois K ↥M := by
    rw [← InfiniteGalois.normal_iff_isGalois M]
    rw [hfix]
    exact N.isNormal'

  haveI : (⟨N.toSubgroup, hNc⟩ : ClosedSubgroup (L ≃ₐ[K] L)).Normal := N.isNormal'
  have hcard : Nat.card (↥M ≃ₐ[K] ↥M) = N.toSubgroup.index := by
    rw [Subgroup.index_eq_card]
    exact (Nat.card_congr (InfiniteGalois.normalAutEquivQuotient
      ⟨N.toSubgroup, hNc⟩).toEquiv).symm
  have hdvd' : p ∣ Fintype.card (↥M ≃ₐ[K] ↥M) := by
    rw [← Nat.card_eq_fintype_card, hcard]
    exact hdvd

  haveI := Fact.mk hp
  obtain ⟨τ, hτ⟩ := exists_prime_orderOf_dvd_card p hdvd'

  set C : Subgroup (↥M ≃ₐ[K] ↥M) := Subgroup.zpowers τ with hC
  set K' : IntermediateField K ↥M := IntermediateField.fixedField C with hK'
  have hrank : Module.finrank ↥K' ↥M = p := by
    rw [hK', IntermediateField.finrank_fixedField_eq_card, hC, Nat.card_eq_fintype_card,
      Fintype.card_zpowers, hτ]
  haveI : IsCyclic ↥C := by
    rw [hC]
    infer_instance
  haveI hcyc : IsCyclic (↥M ≃ₐ[↥K'] ↥M) := by
    have hKc : IntermediateField.fixingSubgroup K' = C :=
      IntermediateField.fixingSubgroup_fixedField C
    haveI : IsCyclic ↥(IntermediateField.fixingSubgroup K') := by rw [hKc]; infer_instance
    exact isCyclic_of_surjective (IntermediateField.fixingSubgroupEquiv K').toMonoidHom
      (IntermediateField.fixingSubgroupEquiv K').surjective

  have hζ' : IsPrimitiveRoot (algebraMap K ↥K' ζ) p :=
    hζ.map_of_injective (algebraMap K ↥K').injective
  have hK : (primitiveRoots (Module.finrank ↥K' ↥M) ↥K').Nonempty := by
    rw [hrank]
    exact ⟨algebraMap K ↥K' ζ, (mem_primitiveRoots hp.pos).mpr hζ'⟩
  obtain ⟨α, hαmem, hadj⟩ := exists_root_adjoin_eq_top_of_isCyclic ↥K' ↥M hK
  rw [hrank] at hαmem
  obtain ⟨a₀, ha₀⟩ := hαmem

  have hbotM : α ∈ (⊥ : IntermediateField ↥K' ↥M) → False := by
    intro hα
    have htop : (⊤ : IntermediateField ↥K' ↥M) = ⊥ :=
      le_antisymm (hadj ▸ IntermediateField.adjoin_simple_le_iff.mpr hα) bot_le
    have h1 : Module.finrank ↥K' ↥M = 1 := by
      rw [← IntermediateField.finrank_bot' (F := ↥K') (E := ↥M), ← htop,
        IntermediateField.finrank_top]
    rw [hrank] at h1
    exact hp.one_lt.ne' h1
  by_cases ha₀0 : a₀ = 0
  ·
    apply hbotM
    have : α ^ p = 0 := by rw [← ha₀, ha₀0, map_zero]
    have hα0 : α = 0 := pow_eq_zero_iff hp.ne_zero |>.mp this
    rw [hα0]
    exact zero_mem ⊥
  ·
    haveI : FiniteDimensional K ↥(K'.map M.val) :=
      Module.Finite.equiv (IntermediateField.equivMap K' M.val).toLinearEquiv
    obtain ⟨b₁, hb₁⟩ := hdiv (K'.map M.val) inferInstance
      (IntermediateField.equivMap K' M.val a₀)
      (by simpa using (IntermediateField.equivMap K' M.val).injective.ne ha₀0)
    set b₀ : ↥K' := (IntermediateField.equivMap K' M.val).symm b₁ with hb₀
    have hb₀p : b₀ ^ p = a₀ := by
      apply (IntermediateField.equivMap K' M.val).injective
      rw [map_pow, hb₀, AlgEquiv.apply_symm_apply, hb₁]
    have hb₀0 : b₀ ≠ 0 := by
      intro h
      apply ha₀0
      rw [← hb₀p, h, zero_pow hp.ne_zero]

    set β : ↥M := algebraMap ↥K' ↥M b₀ with hβdef
    have hβ0 : β ≠ 0 := by
      simpa [hβdef] using (algebraMap ↥K' ↥M).injective.ne hb₀0
    have hβp : β ^ p = α ^ p := by
      rw [hβdef, ← map_pow, hb₀p, ha₀]
    have hα0 : α ≠ 0 := by
      intro h
      apply ha₀0
      apply (algebraMap ↥K' ↥M).injective
      rw [ha₀, h, zero_pow hp.ne_zero, map_zero]
    have hquot : (α / β) ^ p = 1 := by
      rw [div_pow, hβp, div_self (pow_ne_zero p hα0)]

    haveI : NeZero p := ⟨hp.ne_zero⟩
    have hζM : IsPrimitiveRoot (algebraMap K ↥M ζ) p :=
      hζ.map_of_injective (algebraMap K ↥M).injective
    obtain ⟨i, _, hi⟩ := hζM.eq_pow_of_pow_eq_one hquot
    apply hbotM
    rw [IntermediateField.mem_bot]
    refine ⟨algebraMap K ↥K' ζ ^ i * b₀, ?_⟩
    rw [map_mul, map_pow, ← IsScalarTower.algebraMap_apply K ↥K' ↥M, hi, ← hβdef,
      div_mul_cancel₀ α hβ0]

end WCOTTameJ

end

section
open Polynomial

namespace WCOTTameRes

variable {L : Type} [Field L]

theorem exists_pow_eq_residue [IsAlgClosed L] (P : ValuationSubring L) (n : ℕ) (hn : n ≠ 0)
    (c : IsLocalRing.ResidueField P) : ∃ y : IsLocalRing.ResidueField P, y ^ n = c := by
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective c
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (x : L) (Nat.pos_of_ne_zero hn)
  have hβP : β ∈ P := by
    by_contra h
    have h1 : 1 < P.valuation β := by rwa [← not_le, P.valuation_le_one_iff]
    have h2 : P.valuation β ^ n ≤ 1 := by rw [← map_pow, hβ]; exact P.valuation_le_one x
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have h3 : P.valuation β ≤ P.valuation β ^ (k + 1) := by
      rw [pow_succ]
      calc P.valuation β = 1 * P.valuation β := (one_mul _).symm
        _ ≤ P.valuation β ^ k * P.valuation β := mul_le_mul' (one_le_pow_of_one_le' h1.le k) le_rfl
    exact absurd (lt_of_lt_of_le h1 (h3.trans h2)) (lt_irrefl 1)
  refine ⟨IsLocalRing.residue P ⟨β, hβP⟩, ?_⟩
  rw [← map_pow]
  congr 1
  exact Subtype.ext hβ

theorem exists_pow_eq_one_residue [CharZero L] (P : ValuationSubring L) (q : ℕ) (hqp : q.Prime)
    (hq : ((q : ℕ) : P) ∈ IsLocalRing.maximalIdeal P) (halg : ∀ x : L, IsAlgebraic ℚ x)
    (c : IsLocalRing.ResidueField P) (hc : c ≠ 0) : ∃ N : ℕ, 0 < N ∧ c ^ N = 1 := by
  classical

  have hqκ : (q : IsLocalRing.ResidueField P) = 0 := by
    have : IsLocalRing.residue P (q : P) = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hq
    simpa using this
  haveI : Fact q.Prime := ⟨hqp⟩
  haveI : CharP (IsLocalRing.ResidueField P) q := (CharP.charP_iff_prime_eq_zero hqp).mpr hqκ
  letI : Algebra (ZMod q) (IsLocalRing.ResidueField P) := ZMod.algebra _ q

  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective c
  have halgZ : IsAlgebraic ℤ (x : L) := (IsFractionRing.isAlgebraic_iff ℤ ℚ L).mpr (halg _)
  obtain ⟨g, hg0, hgx⟩ := halgZ
  set pp : ℤ[X] := g.primPart with hppdef
  have hppL : aeval (x : L) pp = 0 := by
    have h := hgx
    rw [g.eq_C_content_mul_primPart, map_mul, aeval_C] at h
    refine (mul_eq_zero.mp h).resolve_left ?_
    have : g.content ≠ 0 := mt Polynomial.content_eq_zero_iff.mp hg0
    exact (map_ne_zero_iff (algebraMap ℤ L) (algebraMap ℤ L).injective_int).mpr this

  have hppP : aeval x pp = 0 := by
    have h := Polynomial.aeval_algHom_apply (P.subtype.toIntAlgHom) x pp
    apply P.subtype_injective
    rw [map_zero]
    change P.subtype.toIntAlgHom (aeval x pp) = 0
    rw [← h]
    exact hppL
  have hppκ : aeval (IsLocalRing.residue P x) pp = 0 := by
    have h := Polynomial.aeval_algHom_apply ((IsLocalRing.residue P).toIntAlgHom) x pp
    refine h.trans ?_
    rw [hppP, map_zero]

  set h : (ZMod q)[X] := pp.map (Int.castRingHom (ZMod q)) with hhdef
  have hh0 : h ≠ 0 := by
    intro h0
    have hdvd : C (q : ℤ) ∣ pp := by
      rw [C_dvd_iff_dvd_coeff]
      intro i
      have : (Int.castRingHom (ZMod q)) (pp.coeff i) = 0 := by
        rw [← coeff_map, ← hhdef, h0, coeff_zero]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
    have hu : IsUnit (q : ℤ) := (isPrimitive_iff_isUnit_of_C_dvd.mp g.isPrimitive_primPart) _ hdvd
    rcases Int.isUnit_iff.mp hu with h1 | h1
    · exact hqp.one_lt.ne' (by exact_mod_cast h1)
    · have : (0 : ℤ) ≤ q := Int.natCast_nonneg q
      omega
  have hhc : aeval (IsLocalRing.residue P x) h = 0 := by
    rw [hhdef, aeval_def, eval₂_map]
    have : (algebraMap (ZMod q) (IsLocalRing.ResidueField P)).comp (Int.castRingHom (ZMod q)) =
        algebraMap ℤ (IsLocalRing.ResidueField P) := RingHom.ext_int _ _
    rw [this, ← aeval_def, hppκ]

  have halgc : IsAlgebraic (ZMod q) (IsLocalRing.residue P x) := ⟨h, hh0, hhc⟩
  have hint : IsIntegral (ZMod q) (IsLocalRing.residue P x) :=
    IsAlgebraic.isIntegral (K := ZMod q) (A := IsLocalRing.ResidueField P) halgc
  set S := (Algebra.adjoin (ZMod q) {IsLocalRing.residue P x}).toSubmodule with hS
  haveI : Module.Finite (ZMod q) S := Module.Finite.iff_fg.mpr hint.fg_adjoin_singleton
  haveI : Finite S := Module.finite_of_finite (ZMod q)
  have hmem : ∀ i : ℕ, IsLocalRing.residue P x ^ i ∈ S := fun i =>
    show IsLocalRing.residue P x ^ i ∈ Algebra.adjoin (ZMod q) {IsLocalRing.residue P x} from
      Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton _ _) i
  obtain ⟨i, j, hij, hpow⟩ := Finite.exists_ne_map_eq_of_infinite (fun i : ℕ => (⟨_, hmem i⟩ : S))
  have hpow' : IsLocalRing.residue P x ^ i = IsLocalRing.residue P x ^ j := congrArg Subtype.val hpow

  have key : ∀ i j : ℕ, i < j → IsLocalRing.residue P x ^ i = IsLocalRing.residue P x ^ j →
      ∃ N : ℕ, 0 < N ∧ IsLocalRing.residue P x ^ N = 1 := by
    intro i j hlt heq
    refine ⟨j - i, Nat.sub_pos_of_lt hlt, ?_⟩
    have hsplit : IsLocalRing.residue P x ^ j = IsLocalRing.residue P x ^ i * IsLocalRing.residue P x ^ (j - i) := by
      rw [← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [hsplit] at heq
    have hi0 : IsLocalRing.residue P x ^ i ≠ 0 := pow_ne_zero _ hc
    exact (mul_right_injective₀ hi0 (heq.symm.trans (mul_one _).symm))
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact key i j hlt hpow'
  · exact key j i hlt hpow'.symm

theorem exists_pow_sub_mem_of_lifts {K : Type} [Field K] [Algebra K L] (P : ValuationSubring L) (p : ℕ)
    (hp : p.Prime) (hroots : ∀ c : IsLocalRing.ResidueField P, ∃ y, y ^ p = c)
    (htor : ∀ c : IsLocalRing.ResidueField P, c ≠ 0 → ∃ N : ℕ, 0 < N ∧ c ^ N = 1)
    (hμ : ∀ (i : ℕ) (y : IsLocalRing.ResidueField P), y ^ (p ^ i) = 1 →
      ∃ k : K, ∃ hk : algebraMap K L k ∈ P, IsLocalRing.residue P ⟨algebraMap K L k, hk⟩ = y)
    (u : P.comap (algebraMap K L)) (hu : IsUnit u) :
    ∃ z : P.comap (algebraMap K L), z ^ p - u ∈ IsLocalRing.maximalIdeal (P.comap (algebraMap K L)) := by
  classical
  let ψ : P.comap (algebraMap K L) →+* P :=
    { toFun := fun k => ⟨algebraMap K L k, k.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  let r : P.comap (algebraMap K L) →+* IsLocalRing.ResidueField P := (IsLocalRing.residue P).comp ψ
  have hr : ∀ (k : K) (hk : algebraMap K L k ∈ P),
      r ⟨k, hk⟩ = IsLocalRing.residue P ⟨algebraMap K L k, hk⟩ := fun _ _ => rfl

  have hrefl : ∀ t, r t = 0 → t ∈ IsLocalRing.maximalIdeal (P.comap (algebraMap K L)) := by
    intro t ht
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro htu
    have h1 : IsUnit (ψ t) := htu.map ψ
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit] at h1
    exact h1 ht
  have hū : r u ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr (hu.map ψ)
  obtain ⟨y, hy⟩ := hroots (r u)
  obtain ⟨N, hN, hN1⟩ := htor (r u) hū
  obtain ⟨a, m, hnd, hNam⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' p hp.one_lt.ne'
  have hyM : y ^ (p ^ (a + 1) * m) = 1 := by
    rw [pow_succ', mul_assoc, pow_mul, hy, ← hNam, hN1]

  have tail : ∀ (e : ℕ) (w : IsLocalRing.ResidueField P), w ^ (p ^ (a + 1)) = 1 → y = r u ^ e * w →
      ∃ z : P.comap (algebraMap K L), z ^ p - u ∈ IsLocalRing.maximalIdeal (P.comap (algebraMap K L)) := by
    intro e w hw hyw
    obtain ⟨k, hk, hkw⟩ := hμ (a + 1) w hw
    refine ⟨⟨k, hk⟩ * u ^ e, hrefl _ ?_⟩
    rw [map_sub, map_pow, map_mul, map_pow, sub_eq_zero, hr k hk, hkw, mul_comm, ← hyw, hy]
  by_cases hm1 : m = 1
  · refine tail 0 y ?_ (by rw [pow_zero, one_mul])
    rw [← hyM, hm1, mul_one]
  · have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hNam
      exact hN.ne' hNam
    have hm : 1 < m := Nat.lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr hm0) (Ne.symm hm1)
    have hcop : Nat.Coprime (p ^ (a + 1)) m :=
      (Nat.coprime_pow_left_iff (Nat.succ_pos a) _ _).mpr (hp.coprime_iff_not_dvd.mpr hnd)
    obtain ⟨A, -, hA⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hm
    set j := p ^ (a + 1) * A / m with hj
    have hMA : p ^ (a + 1) * A = m * j + 1 := by
      have := Nat.div_add_mod (p ^ (a + 1) * A) m
      rw [hA] at this
      exact this.symm
    have hyjM : (y ^ (m * j)) ^ (p ^ (a + 1)) = 1 := by
      rw [← pow_mul, show m * j * p ^ (a + 1) = (p ^ (a + 1) * m) * j by ring, pow_mul, hyM, one_pow]
    refine tail (p ^ a * A) ((y ^ (m * j)) ^ (p ^ (a + 1) - 1)) ?_ ?_
    · rw [← pow_mul, mul_comm (p ^ (a + 1) - 1) (p ^ (a + 1)), pow_mul, hyjM, one_pow]
    · symm
      calc r u ^ (p ^ a * A) * (y ^ (m * j)) ^ (p ^ (a + 1) - 1)
          = y ^ (m * j) * y * (y ^ (m * j)) ^ (p ^ (a + 1) - 1) := by
            rw [← hy, ← pow_mul, show p * (p ^ a * A) = p ^ (a + 1) * A by ring, hMA, pow_succ]
        _ = y * ((y ^ (m * j)) ^ (p ^ (a + 1) - 1) * y ^ (m * j)) := by ring
        _ = y * (y ^ (m * j)) ^ (p ^ (a + 1)) := by
            rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos)]
        _ = y := by rw [hyjM, mul_one]

end WCOTTameRes

end

section
open IntermediateField
open scoped Pointwise

namespace WCOTTameJg

variable (k : Type) {L : Type} [Field k] [Field L] [Algebra k L]

noncomputable abbrev Iner (A : ValuationSubring L) : Subgroup (L ≃ₐ[k] L) :=
  (A.inertiaSubgroup k).map (A.decompositionSubgroup k).subtype

noncomputable def K0 (A : ValuationSubring L) : IntermediateField k L := fixedField (Iner k A)

def Rad (p q : ℕ) : Set L := {α : L | ∃ n : ℕ, α ^ (p ^ n) = (q : L)}

noncomputable def Kinf (A : ValuationSubring L) (p q : ℕ) : IntermediateField k L :=
  IntermediateField.adjoin k ((K0 k A : Set L) ∪ Rad p q)

variable {k}

theorem K0_le_Kinf (A : ValuationSubring L) (p q : ℕ) : K0 k A ≤ Kinf k A p q :=
  fun _ hx => IntermediateField.subset_adjoin k _ (Or.inl hx)

theorem mem_Kinf_of_pow_eq (A : ValuationSubring L) {p q : ℕ} {α : L} {n : ℕ} (h : α ^ (p ^ n) = (q : L)) :
    α ∈ Kinf k A p q :=
  IntermediateField.subset_adjoin k _ (Or.inr ⟨n, h⟩)

theorem frobConj_mem_Iner (A : ValuationSubring L) {q : ℕ} (σ τ : L ≃ₐ[k] L)
    (hσ : σ ∈ A.decompositionSubgroup k) (hτ : τ ∈ Iner k A) :
    σ * τ * σ⁻¹ * (τ ^ q)⁻¹ ∈ Iner k A := by
  refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hτ q))
  obtain ⟨τ', hτ', hττ⟩ := hτ
  have hN : (A.inertiaSubgroup k).Normal := by
    delta ValuationSubring.inertiaSubgroup
    exact MonoidHom.normal_ker _
  let s : A.decompositionSubgroup k := ⟨σ, hσ⟩
  have hmem : s * τ' * s⁻¹ ∈ A.inertiaSubgroup k := hN.conj_mem τ' hτ' s
  have heq : (A.decompositionSubgroup k).subtype (s * τ' * s⁻¹) = σ * τ * σ⁻¹ := by
    rw [map_mul, map_mul, map_inv, hττ]; rfl
  rw [Subgroup.mem_map]
  exact ⟨s * τ' * s⁻¹, hmem, heq⟩

theorem apply_eq_of_mem_adjoin (S : Set L) (g : L ≃ₐ[k] L) (hS : ∀ s ∈ S, g s = s) (x : L)
    (hx : x ∈ IntermediateField.adjoin k S) : g x = x := by
  have hle : IntermediateField.adjoin k S ≤ fixedField (Subgroup.zpowers g) := by
    rw [IntermediateField.adjoin_le_iff]
    intro s hs
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro h hh
    have hst : Subgroup.zpowers g ≤ MulAction.stabilizer (L ≃ₐ[k] L) s := by
      rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
      exact hS s hs
    exact hst hh
  have := (IntermediateField.mem_fixedField_iff _ _).mp (hle hx) g (Subgroup.mem_zpowers g)
  exact this

theorem frobConj_mem_fixingSubgroup_Kinf [CharZero L] (A : ValuationSubring L) {p q : ℕ} (hp : p.Prime)
    (hq : A.LiesOverPrime q) (hpq : p ≠ q) (hq' : q.Prime) (σ : L ≃ₐ[k] L) (hσ : A.IsFrobeniusAt σ q)
    (τ : L ≃ₐ[k] L) (hτ : τ ∈ Iner k A) :
    σ * τ * σ⁻¹ * (τ ^ q)⁻¹ ∈ (Kinf k A p q).fixingSubgroup := by
  set g := σ * τ * σ⁻¹ * (τ ^ q)⁻¹ with hg
  have hgI : g ∈ Iner k A := frobConj_mem_Iner A σ τ hσ.mem_decompositionSubgroup hτ
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  refine apply_eq_of_mem_adjoin _ g ?_ x hx
  rintro s (hs | ⟨n, hs⟩)
  · exact (IntermediateField.mem_fixedField_iff _ _).mp hs g hgI
  ·
    have hq0 : (q : L) ≠ 0 := Nat.cast_ne_zero.mpr hq'.ne_zero
    set β := (τ ^ q)⁻¹ s with hβ
    have hβn : β ^ (p ^ n) = (q : L) := by rw [hβ, ← map_pow, hs, map_natCast]
    have hβ0 : β ≠ 0 := by
      intro h0; rw [h0, zero_pow (pow_ne_zero _ hp.ne_zero)] at hβn; exact hq0 hβn.symm
    have hcop : Nat.Coprime (p ^ n) q := Nat.Coprime.pow_left n ((Nat.coprime_primes hp hq').mpr hpq)
    have hK := WCOTTameR.frob_conj_eq_pow_on_radical A hq (pow_ne_zero n hp.ne_zero) hcop τ hτ σ hσ β hβn hβ0

    rw [hg, AlgEquiv.mul_apply, ← hβ, hK, hβ, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

theorem hdiv_Kinf [IsAlgClosed L] [CharZero L] [IsGalois k L] (halg : ∀ x : L, IsAlgebraic ℚ x)
    (A : ValuationSubring L) {p q : ℕ} (hp : p.Prime) (hq' : q.Prime) (hpq : p ≠ q) (hq : A.LiesOverPrime q)
    (K' : IntermediateField (Kinf k A p q) L) (a : K') (ha : a ≠ 0) : ∃ b : K', b ^ p = a := by
  have hqmax : ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    simp at hq ⊢
    exact hq

  have hstab : ∀ (s : L ≃ₐ[K'] L) (x : L), x ∈ A → s x ∈ A := by
    intro s x hx
    let s₀ : L ≃ₐ[k] L := (s.restrictScalars (Kinf k A p q)).restrictScalars k
    have hs₀ : ∀ z, s₀ z = s z := fun _ => rfl
    have hsK0 : s₀ ∈ (K0 k A).fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      have hy' : y ∈ Kinf k A p q := K0_le_Kinf A p q hy
      have e : y = algebraMap K' L (algebraMap (Kinf k A p q) K' ⟨y, hy'⟩) := by
        rw [← IsScalarTower.algebraMap_apply]; rfl
      rw [hs₀, e, AlgEquiv.commutes]
    have hD := WCOTTameU.fixingSubgroup_fixedField_map_inertia_le (K := k) A hsK0
    have hsA : s₀ • A = A := hD
    have := ValuationSubring.smul_mem_pointwise_smul s₀ x A hx
    rw [hsA] at this
    simpa [AlgEquiv.smul_def, hs₀] using this

  have hroot : ∀ n : ℕ, ∃ r : K', r ^ (p ^ n) = (q : K') := by
    intro n
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (q : L) (pow_pos hp.pos n)
    refine ⟨algebraMap (Kinf k A p q) K' ⟨α, mem_Kinf_of_pow_eq A hα⟩, ?_⟩
    apply (algebraMap K' L).injective
    rw [map_pow, ← IsScalarTower.algebraMap_apply, map_natCast]
    exact hα

  have hμ : ∀ (i : ℕ) (y : IsLocalRing.ResidueField A), y ^ (p ^ i) = 1 →
      ∃ kk : K', ∃ hk : algebraMap K' L kk ∈ A, IsLocalRing.residue A ⟨algebraMap K' L kk, hk⟩ = y := by
    intro i y hy
    obtain ⟨ζ, hζ0, hζA, hres⟩ := WCOTTameRp.exists_mem_fixedField_residue_eq (K := k) A hp hq hpq hq' i y hy
    replace hζ0 : ζ ∈ K0 k A := hζ0
    have gen : ∀ (z : L), z = ζ → ∃ hz : z ∈ A, IsLocalRing.residue A ⟨z, hz⟩ = y := by
      rintro z rfl; exact ⟨hζA, hres⟩
    refine ⟨algebraMap (Kinf k A p q) K' ⟨ζ, K0_le_Kinf A p q hζ0⟩, gen _ ?_⟩
    rw [← IsScalarTower.algebraMap_apply]; rfl
  have hres : ∀ u : A.comap (algebraMap K' L), IsUnit u →
      ∃ z : A.comap (algebraMap K' L), z ^ p - u ∈ IsLocalRing.maximalIdeal (A.comap (algebraMap K' L)) :=
    WCOTTameRes.exists_pow_sub_mem_of_lifts A p hp (WCOTTameRes.exists_pow_eq_residue A p hp.ne_zero)
      (WCOTTameRes.exists_pow_eq_one_residue A q hq' hqmax halg) hμ
  exact ValuationSubring.exists_pow_eq_of_kummer_descent A hstab p q hp hq' hpq hqmax halg hroot hres a ha

end WCOTTameJg

end

section
open IntermediateField
open scoped Pointwise

namespace WCOTTameGen

open WCOTTameJg

variable {k : Type} {L : Type} [Field k] [Field L] [Algebra k L]

theorem exists_mem_Iner_pow_eq [IsAlgClosed L] [CharZero L] [IsGalois k L]
    (halg : ∀ x : L, IsAlgebraic ℚ x) (A : ValuationSubring L) {p q : ℕ} (hp : p.Prime) (hq' : q.Prime)
    (hpq : p ≠ q) (hq : A.LiesOverPrime q) (n : ℕ) (g : L ≃ₐ[k] L)
    (hgE : g ∈ (Kinf k A p q).fixingSubgroup) :
    ∃ w : L ≃ₐ[k] L, w ∈ Iner k A ∧ w ^ (p ^ n) = g := by
  set E : IntermediateField k L := Kinf k A p q with hE

  let g' : L ≃ₐ[E] L := IntermediateField.fixingSubgroupEquiv E ⟨g, hgE⟩
  haveI : T2Space (L ≃ₐ[E] L) := krullTopology_t2

  haveI : NeZero ((p : ℕ) : L) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  obtain ⟨ζL, hζL⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L p
  have hζK0 : ζL ∈ K0 k A := by
    rw [K0, IntermediateField.mem_fixedField_iff]
    intro t ht
    exact WCOTTameR.inertia_fixes_root_of_unity A hq hp.ne_zero ((Nat.coprime_primes hp hq').mpr hpq) ζL
      hζL.pow_eq_one t ht
  let ζ : E := ⟨ζL, K0_le_Kinf A p q hζK0⟩
  have hζ : IsPrimitiveRoot ζ p :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap E L) (by exact hζL) (algebraMap E L).injective
  have hidx : ∀ N : OpenNormalSubgroup (L ≃ₐ[E] L), (N.toSubgroup.index).Coprime p :=
    fun N => WCOTTameJ.index_coprime_of_forall_pow_surjective hp hζ
      (fun K' _ a ha => hdiv_Kinf halg A hp hq' hpq hq K' a ha) N
  obtain ⟨w', hw'⟩ := WCOTTameJ.exists_pow_pow_eq hidx g' n
  let w : E.fixingSubgroup := (IntermediateField.fixingSubgroupEquiv E).symm w'
  refine ⟨(w : L ≃ₐ[k] L), ?_, ?_⟩
  · have h1 : (w : L ≃ₐ[k] L) ∈ (K0 k A).fixingSubgroup :=
      IntermediateField.fixingSubgroup_le (K0_le_Kinf A p q) w.2
    have h2 : (K0 k A).fixingSubgroup = Iner k A := by
      rw [K0, WCOTTameU.fixingSubgroup_fixedField_eq_topologicalClosure, WCOTTameUI.topologicalClosure_inertia_map]
    rw [h2] at h1
    exact h1
  · have hws : (IntermediateField.fixingSubgroupEquiv E).symm (w' ^ p ^ n) = w ^ p ^ n := map_pow _ _ _
    rw [hw'] at hws
    have : (IntermediateField.fixingSubgroupEquiv E).symm g' = ⟨g, hgE⟩ := MulEquiv.symm_apply_apply _ _
    rw [this] at hws
    have := congrArg (fun x : E.fixingSubgroup => (x : L ≃ₐ[k] L)) hws
    simpa using this.symm

end WCOTTameGen

end

set_option backward.isDefEq.respectTransparency false in

theorem solution
    {p q : ℕ} (hp : p.Prime) (hq' : q.Prime) (hpq : p ≠ q)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hq : P.LiesOverPrime q) (n : ℕ)
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hg : g ∈ P.inertiaSubgroupIn ℚ)
    (hrad : ∀ (α : AlgebraicClosure ℚ) (k : ℕ), α ^ (p ^ k) = (q : AlgebraicClosure ℚ) → g α = α) :
    ∃ w ∈ P.inertiaSubgroupIn ℚ, w ^ (p ^ n) = g := by
  have hg' : g ∈ WCOTTameJg.Iner ℚ P := hg
  have hE : g ∈ (WCOTTameJg.Kinf ℚ P p q).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    refine WCOTTameJg.apply_eq_of_mem_adjoin _ g ?_ y hy
    rintro s (hs | ⟨n, hs⟩)
    · exact (IntermediateField.mem_fixedField_iff _ _).mp hs g hg'
    · exact hrad s n hs
  obtain ⟨w, hw, hwg⟩ := WCOTTameGen.exists_mem_Iner_pow_eq (k := ℚ) (fun x => Algebra.IsAlgebraic.isAlgebraic x)
    P hp hq' hpq hq n g hE
  exact ⟨w, hw, hwg⟩

end S_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq
end P2MW
export P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq (solution)
